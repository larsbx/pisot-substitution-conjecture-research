#!/usr/bin/env python3
"""Fail closed if a manuscript source or PDF is missing or not what it claims to be.

``manuscripts/MANIFEST`` lists the required files, one per line.  Every listed
file must exist; every ``.tex`` in the directory must be valid UTF-8 with no
control bytes other than tab and newline, a ``\\documentclass`` first line,
``\\begin{document}`` before ``\\end{document}``, and at least MIN_LINES lines;
every ``.pdf`` must carry the ``%PDF-`` header, a ``startxref`` offset that
(the last one before the final ``%%EOF``) that points at a classic ``xref`` table\n(subsections of 20-byte entries, then a ``trailer`` dictionary with ``/Size`` and\n``/Root``) or at a ``/Type /XRef`` stream object whose body matches its direct\n``/Length``, inflates if Flate-encoded, and has a positive multiple of the ``/W``\nrow width, and ``%%EOF``
within the last 1024 bytes.  Exit status 1 names every failure, so a missing,
byte-mangled or truncated file never passes.

Usage: check_manuscript_source.py [DIR]   (default: manuscripts/)
"""
from __future__ import annotations

import re
import sys
import zlib
from pathlib import Path

MIN_LINES = 500
ROOT = Path(__file__).resolve().parents[1]


def check_tex(path: Path) -> list[str]:
    raw = path.read_bytes()
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as e:
        return [f"{path}: not valid UTF-8 ({e})"]
    problems = []
    bad = sorted({c for c in text if ord(c) < 32 and c not in "\n\t"})
    if bad:
        problems.append(f"{path}: control characters {[hex(ord(c)) for c in bad]}")
    lines = text.splitlines()
    first = next((l for l in lines if l.strip()), "")
    if not first.startswith("\\documentclass"):
        problems.append(f"{path}: first line is not \\documentclass")
    b, e = text.find("\\begin{document}"), text.rfind("\\end{document}")
    if b < 0 or e < 0 or e < b:
        problems.append(f"{path}: missing or misordered \\begin{{document}} / \\end{{document}}")
    if len(lines) < MIN_LINES:
        problems.append(f"{path}: only {len(lines)} lines (< {MIN_LINES})")
    return problems


def _dict_at(buf: bytes, i: int) -> bytes | None:
    """The dictionary starting at ``buf[i:i+2] == b'<<'``, delimiters included."""
    if buf[i:i + 2] != b"<<":
        return None
    depth, j = 0, i
    while j < len(buf) - 1:
        pair = buf[j:j + 2]
        if pair == b"<<":
            depth, j = depth + 1, j + 2
        elif pair == b">>":
            depth, j = depth - 1, j + 2
            if depth == 0:
                return buf[i:j]
        else:
            j += 1
    return None


def _classic_table(raw: bytes, off: int) -> str | None:
    """Problem with the classic ``xref`` table at ``raw[off:]``, or None."""
    at = raw[off:]
    m = re.match(rb"xref[ \t]*(?:\r\n|\r|\n)", at)
    if not m:
        return "malformed xref keyword"
    pos, entries = m.end(), 0
    while True:
        sub = re.match(rb"(\d+)[ \t]+(\d+)[ \t]*(?:\r\n|\r|\n)", at[pos:pos + 64])
        if not sub:
            break
        pos, start, count = pos + sub.end(), int(sub.group(1)), int(sub.group(2))
        block = at[pos:pos + 20 * count]
        if len(block) < 20 * count:
            return "truncated xref subsection"
        for k in range(count):
            e = re.fullmatch(rb"(\d{10}) (\d{5}) ([nf])(?: \r| \n|\r\n)", block[20 * k:20 * k + 20])
            if not e:
                return f"malformed xref entry {entries + k}"
            if e.group(3) == b"n":
                # an in-use entry must point at the header of its own object
                target, gen, num = int(e.group(1)), int(e.group(2)), start + k
                if target >= len(raw) or not re.match(rb"%d\s+%d\s+obj\b" % (num, gen), raw[target:target + 40]):
                    return f"xref entry for object {num} does not point at '{num} {gen} obj'"
        pos, entries = pos + 20 * count, entries + count
    if entries == 0:
        return "xref table has no entries"
    t = re.match(rb"trailer\s*", at[pos:pos + 32])
    if not t:
        return "xref table not followed by trailer"
    d = _dict_at(at, pos + t.end())
    if d is None:
        return "trailer has no dictionary"
    if not re.search(rb"/Size\s+\d+", d) or not re.search(rb"/Root\s+\d+\s+\d+\s+R", d):
        return "trailer dictionary lacks /Size or /Root"
    return None


def _xref_stream(at: bytes) -> str | None:
    """Problem with the cross-reference stream object at ``at[0:]``, or None."""
    m = re.match(rb"\d+\s+\d+\s+obj\s*", at)
    if not m:
        return "not an object"
    d = _dict_at(at, m.end())
    if d is None:
        return "object has no dictionary"
    if not re.search(rb"/Type\s*/XRef\b", d):
        return "object is not a cross-reference stream"
    if not re.search(rb"/Size\s+\d+", d) or not re.search(rb"/Root\s+\d+\s+\d+\s+R", d):
        return "cross-reference stream lacks /Size or /Root"
    w = re.search(rb"/W\s*\[([\d\s]+)\]", d)
    if not w:
        return "cross-reference stream lacks /W"
    widths = [int(x) for x in w.group(1).split()]
    if len(widths) != 3:
        return f"cross-reference stream /W must have exactly three fields, has {len(widths)}"
    row = sum(widths)
    pred = re.search(rb"/Predictor\s+(\d+)", d)
    if pred and int(pred.group(1)) >= 10:
        row += 1
    if row == 0:
        return "cross-reference stream has zero row width"
    length = re.search(rb"/Length\s+(\d+)(\s+\d+\s+R)?", d)
    if not length:
        return "cross-reference stream lacks /Length"
    if length.group(2):
        return "cross-reference stream /Length is an indirect reference, not a direct integer"
    n = int(length.group(1))
    size = int(re.search(rb"/Size\s+(\d+)", d).group(1))
    if b"/Index" in d:
        index = re.search(rb"/Index\s*\[([\d\s]+)\]", d)
        values = [int(x) for x in index.group(1).split()] if index else []
        if not values or len(values) % 2:
            return "cross-reference stream /Index is not an array of start/count pairs"
        pairs = list(zip(values[::2], values[1::2]))
        if any(c <= 0 or st + c > size for st, c in pairs):
            return "cross-reference stream /Index range is empty or exceeds /Size"
        expected_rows = sum(c for _, c in pairs)
    else:
        expected_rows = size
    body = re.match(rb"\s*stream(?:\r\n|\n)", at[m.end() + len(d):m.end() + len(d) + 16])
    if not body:
        return "cross-reference stream has no stream body"
    data_start = m.end() + len(d) + body.end()
    data = at[data_start:data_start + n]
    tail = re.match(rb"(?:\r\n|\r|\n)?endstream\s*endobj\b", at[data_start + n:data_start + n + 32])
    if len(data) < n or not tail:
        return "cross-reference stream body does not match /Length or is not closed by endstream and endobj"
    filters = None
    if b"/Filter" in d:
        flt = re.search(rb"/Filter\s*(?:/(\w+)|\[\s*((?:/\w+\s*)*)\])", d)
        if not flt:
            return "cross-reference stream /Filter is not a name or an array of names"
        filters = [flt.group(1)] if flt.group(1) else re.findall(rb"/(\w+)", flt.group(2))
        if filters != [b"FlateDecode"]:
            return f"unsupported cross-reference stream filter chain {[f.decode() for f in filters]}"
    if filters:
        try:
            payload = zlib.decompress(data)
        except zlib.error as e:
            return f"cross-reference stream payload does not inflate ({e})"
    else:
        payload = data
    if len(payload) == 0 or len(payload) % row != 0:
        return f"cross-reference stream payload of {len(payload)} bytes is not a positive multiple of the row width {row}"
    rows = len(payload) // row
    if rows != expected_rows:
        return f"cross-reference stream has {rows} rows but declares {expected_rows} (/Index or /Size)"
    return None


def check_pdf(path: Path) -> list[str]:
    raw = path.read_bytes()
    if not raw.startswith(b"%PDF-"):
        return [f"{path}: missing %PDF- signature (got {raw[:5]!r})"]
    tail = raw[-1024:]
    eof = tail.rfind(b"%%EOF")
    if eof < 0:
        return [f"{path}: no %%EOF in the last 1024 bytes (truncated?)"]
    # the trailer that counts is the last startxref before the final %%EOF
    sx = tail.rfind(b"startxref", 0, eof)
    if sx < 0:
        return [f"{path}: no startxref before the final %%EOF"]
    m = re.fullmatch(rb"startxref\s+(\d+)\s*", tail[sx:eof])
    if not m:
        return [f"{path}: malformed startxref before the final %%EOF"]
    off = int(m.group(1))
    if off >= len(raw):
        return [f"{path}: startxref offset {off} beyond end of file ({len(raw)} bytes)"]
    at = raw[off:]
    if at.startswith(b"xref"):
        problem = _classic_table(raw, off)
    elif re.match(rb"\d+\s+\d+\s+obj\b", at[:32]):
        problem = _xref_stream(at)
    else:
        problem = "startxref offset does not point at an xref table or object"
    return [f"{path}: at startxref offset {off}: {problem}"] if problem else []


def main(argv: list[str]) -> int:
    directory = Path(argv[0]) if argv else ROOT / "manuscripts"
    manifest = directory / "MANIFEST"
    problems = []
    if not manifest.is_file():
        problems.append(f"{manifest}: missing manifest of required files")
        required = []
    else:
        required = [directory / l.strip() for l in manifest.read_text().splitlines() if l.strip()]
        if not required:
            problems.append(f"{manifest}: empty manifest")
    for p in required:
        if not p.is_file():
            problems.append(f"{p}: required by the manifest but missing")
    present = sorted(directory.glob("*.tex")) + sorted(directory.glob("*.pdf")) if directory.is_dir() else []
    checked = 0
    for p in present:
        problems += check_tex(p) if p.suffix == ".tex" else check_pdf(p)
        checked += 1
    if not any(p.suffix == ".tex" for p in required) or not any(p.suffix == ".pdf" for p in required):
        problems.append(f"{manifest}: must list at least one .tex and one .pdf")
    for m in problems:
        print("FAIL", m)
    if not problems:
        print(f"OK manuscript sources: {len(required)} required files present, {checked} .tex/.pdf checked")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
