#!/usr/bin/env python3
"""Fail closed if a manuscript source or PDF is missing or not what it claims to be.

``manuscripts/MANIFEST`` lists the required files, one per line.  Every listed
file must exist; every ``.tex`` in the directory must be valid UTF-8 with no
control bytes other than tab and newline, a ``\\documentclass`` first line,
``\\begin{document}`` before ``\\end{document}``, and at least MIN_LINES lines;
every ``.pdf`` must carry the ``%PDF-`` header, a ``startxref`` offset that
(the last one before the final ``%%EOF``) that points at a classic ``xref`` table\n(subsections of 20-byte entries, then a ``trailer`` dictionary with ``/Size`` and\n``/Root``) or at a ``/Type /XRef`` stream object whose body matches its direct\n``/Length``, inflates if Flate-encoded, and has a positive multiple of the ``/W``\nrow width, and ``%%EOF``; finally pypdf parses the whole file in strict mode and
every object, including object-stream members, is dereferenced and the page
tree read
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
MAX_XREF_ROWS = 1_000_000  # the repository PDF has 1133 objects; a declaration above this is never inflated
MAX_STREAM_BYTES = 1 << 26  # the largest decoded stream in the repository PDF is 34 KB
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


def _prev_of(d: bytes) -> int | None:
    m = re.search(rb"/Prev\s+(\d+)", d)
    return int(m.group(1)) if m else None


Entry = tuple[int, int, int, bool]
"""``(kind, field, generation, classic)``: kind 0 is free (field = next free object number),
kind 1 in use (field = byte offset), kind 2 compressed (field = object stream number,
generation slot = index); ``classic`` records whether the entry came from a classic table,
whose free entries must be on the free list, rather than from a cross-reference stream."""


Section = tuple[dict[int, Entry], int, int | None, int | None]
"""``(entries by object number, trailer /Size, /Prev offset or None, /XRefStm offset or None)``."""


def _classic_table(raw: bytes, off: int) -> str | Section:
    """The classic ``xref`` table at ``raw[off:]``: a problem, or its section."""
    at = raw[off:]
    m = re.match(rb"xref[ \t]*(?:\r\n|\r|\n)", at)
    if not m:
        return "malformed xref keyword"
    pos, entries, ranges, table = m.end(), 0, [], {}
    while True:
        sub = re.match(rb"(\d+)[ \t]+(\d+)[ \t]*(?:\r\n|\r|\n)", at[pos:pos + 64])
        if not sub:
            break
        pos, start, count = pos + sub.end(), int(sub.group(1)), int(sub.group(2))
        if count == 0:
            return f"empty xref subsection at object {start}"
        ranges.append((start, count))
        block = at[pos:pos + 20 * count]
        if len(block) < 20 * count:
            return "truncated xref subsection"
        for k in range(count):
            e = re.fullmatch(rb"(\d{10}) (\d{5}) ([nf])(?: \r| \n|\r\n)", block[20 * k:20 * k + 20])
            if not e:
                return f"malformed xref entry {entries + k}"
            num, field, gen = start + k, int(e.group(1)), int(e.group(2))
            if gen > 65535:
                return f"xref entry for object {num} has generation {gen} > 65535"
            if e.group(3) == b"n":
                # an in-use entry must point at the header of its own object
                if field >= len(raw) or not re.match(rb"%d\s+%d\s+obj\b" % (num, gen), raw[field:field + 40]):
                    return f"xref entry for object {num} does not point at '{num} {gen} obj'"
            table[num] = (0 if e.group(3) == b"f" else 1, field, gen, True)
        pos, entries = pos + 20 * count, entries + count
    if entries == 0:
        return "xref table has no entries"
    t = re.match(rb"trailer\s*", at[pos:pos + 32])
    if not t:
        return "xref table not followed by trailer"
    d = _dict_at(at, pos + t.end())
    if d is None:
        return "trailer has no dictionary"
    size = re.search(rb"/Size\s+(\d+)", d)
    if not size or not re.search(rb"/Root\s+\d+\s+\d+\s+R", d):
        return "trailer dictionary lacks /Size or /Root"
    if any(st + c > int(size.group(1)) for st, c in ranges):
        return f"xref subsection exceeds the trailer /Size {int(size.group(1))}"
    stray = [n for n, (k, f, *_) in table.items() if k == 0 and f >= int(size.group(1))]
    if stray:
        return f"free entry for object {stray[0]} points at object {table[stray[0]][1]} beyond /Size"
    xrefstm = re.search(rb"/XRefStm\s+(\d+)", d)
    return table, int(size.group(1)), _prev_of(d), int(xrefstm.group(1)) if xrefstm else None


def _unpredict(payload: bytes, row: int) -> bytes | None:
    """Undo PNG row prediction (filter byte per row); None on an unknown filter."""
    width, prev, out = row - 1, bytes(row - 1), []
    for i in range(0, len(payload), row):
        f, line = payload[i], bytearray(payload[i + 1:i + row])
        for j in range(width):
            a = line[j - 1] if j else 0
            b, c = prev[j], (prev[j - 1] if j else 0)
            if f == 0:
                pred = 0
            elif f == 1:
                pred = a
            elif f == 2:
                pred = b
            elif f == 3:
                pred = (a + b) // 2
            elif f == 4:
                pa, pb, pc = abs(b - c), abs(a - c), abs(a + b - 2 * c)
                pred = a if pa <= pb and pa <= pc else (b if pb <= pc else c)
            else:
                return None
            line[j] = (line[j] + pred) & 0xFF
        prev = bytes(line)
        out.append(prev)
    return b"".join(out)


def _xref_rows(raw: bytes, rows: bytes, widths: list[int], numbers: list[int], size: int) -> str | dict[int, Entry]:
    """Decode each row per ``/W`` and dereference in-use entries; the entries if all agree."""
    w0, w1, w2 = widths
    stride, table = sum(widths), {}
    for i, num in enumerate(numbers):
        r = rows[i * stride:(i + 1) * stride]
        kind = int.from_bytes(r[:w0], "big") if w0 else 1
        f2 = int.from_bytes(r[w0:w0 + w1], "big")
        f3 = int.from_bytes(r[w0 + w1:], "big")
        if kind in (0, 1) and f3 > 65535:
            return f"cross-reference stream entry for object {num} has generation {f3} > 65535"
        if kind == 0:
            if f2 >= size:
                return f"cross-reference stream free entry for object {num} points at object {f2} beyond /Size"
        elif kind == 1:
            if f2 >= len(raw) or not re.match(rb"%d\s+%d\s+obj\b" % (num, f3), raw[f2:f2 + 40]):
                return f"cross-reference stream entry for object {num} does not point at '{num} {f3} obj'"
        elif kind == 2:
            if f2 >= size:
                return f"cross-reference stream entry for object {num} names object stream {f2} beyond /Size"
        else:
            return f"cross-reference stream entry for object {num} has unknown type {kind}"
        table[num] = (kind, f2, f3, False)
    return table


def _xref_stream(raw: bytes, off: int) -> str | Section:
    """The cross-reference stream object at ``raw[off:]``: a problem, or its section
    (type-0 rows included)."""
    at = raw[off:]
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
    predicted = bool(pred and int(pred.group(1)) >= 10)
    if predicted:
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
    else:
        pairs = [(0, size)]
    expected_rows = sum(c for _, c in pairs)  # object numbers are materialized only once the payload agrees
    if expected_rows > MAX_XREF_ROWS:
        return f"cross-reference stream declares {expected_rows} rows, above the ceiling of {MAX_XREF_ROWS}"
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
        inflater = zlib.decompressobj()
        try:
            payload = inflater.decompress(data, expected_rows * row + 1)  # never inflate past the declared size
        except zlib.error as e:
            return f"cross-reference stream payload does not inflate ({e})"
        if not inflater.eof or inflater.unconsumed_tail or inflater.unused_data:
            return "cross-reference stream payload inflates past the declared row count or is not a complete deflate member"
    else:
        payload = data
    if len(payload) == 0 or len(payload) % row != 0:
        return f"cross-reference stream payload of {len(payload)} bytes is not a positive multiple of the row width {row}"
    rows = len(payload) // row
    if rows != expected_rows:
        return f"cross-reference stream has {rows} rows but declares {expected_rows} (/Index or /Size)"
    numbers = [st + k for st, c in pairs for k in range(c)]
    if predicted:
        payload = _unpredict(payload, row)
        if payload is None:
            return "cross-reference stream uses an unknown PNG row filter"
    table = _xref_rows(raw, payload, widths, numbers, size)
    return table if isinstance(table, str) else (table, size, _prev_of(d), None)


def _free_list(table: dict[int, Entry], classic: bool) -> str | None:
    """Object 0 is free (with generation 65535 when its entry comes from a classic table)
    and heads a chain of free entries that returns to object 0.  ``table`` is the effective
    table at one section of the chain: at a classic section every classic free entry must
    be on the chain; a stream type-0 entry (the free list of a cross-reference stream is
    optional) may be off the chain if it points at 0 or at another free entry, but never
    at an object in use."""
    head = table.get(0)
    if head is None or head[0] != 0:
        return "object 0 is not a free entry"
    if head[3] and head[2] != 65535:
        return f"object 0 in a classic table has generation {head[2]}, not 65535"
    free, walked, n = {k for k, v in table.items() if v[0] == 0}, [0], head[1]
    while n != 0:
        if n not in free or n in walked:
            return f"free list reaches object {n}, which is not an unvisited free entry"
        walked.append(n)
        n = table[n][1]
    stray = sorted(n for n in free - set(walked) if (classic and table[n][3]) or table[n][1] not in free | {0})
    return f"free entries {stray} are not on the free list" if stray else None


def _section_at(raw: bytes, off: int, seen: list[int]) -> str | Section:
    """Parse the section at ``off``, which must lie in the file and not have been visited."""
    if off >= len(raw):
        return f"cross-reference offset {off} beyond end of file ({len(raw)} bytes)"
    if off in seen:
        return f"cross-reference chain revisits offset {off}"
    seen.append(off)
    at = raw[off:]
    if at.startswith(b"xref"):
        section = _classic_table(raw, off)
    elif re.match(rb"\d+\s+\d+\s+obj\b", at[:32]):
        section = _xref_stream(raw, off)
    else:
        section = "offset does not point at an xref table or object"
    return f"at cross-reference offset {off}: {section}" if isinstance(section, str) else section


def _xref_chain(raw: bytes, off: int) -> str | int:
    """Walk the cross-reference sections from ``off`` along ``/Prev`` (a classic table's
    ``/XRefStm`` companion stream is merged beneath it), then replay them oldest first: at
    each section the free list is validated on the effective table and the trailer
    ``/Size`` must be one more than its highest object number, since every prefix of the
    chain was once a complete file.  A problem, or the highest object number of the final
    merged table."""
    seen, sections = [], []
    while off is not None:
        section = _section_at(raw, off, seen)
        if isinstance(section, str):
            return section
        entries, size, off, xrefstm = section
        classic = xrefstm is not None or raw.startswith(b"xref", seen[-1])
        if xrefstm is not None:
            companion = _section_at(raw, xrefstm, seen)
            if isinstance(companion, str):
                return f"/XRefStm: {companion}"
            entries = {**companion[0], **entries}  # the table's own entries take precedence
        sections.append((entries, size, classic))
    merged = {}
    for entries, size, classic in reversed(sections):
        merged = {**merged, **entries}  # newer sections win
        if problem := _free_list(merged, classic):
            return problem
        if size != max(merged) + 1:
            return f"trailer /Size {size} is not one more than the highest object number {max(merged)} of its section"
    return max(merged)


def _inflate_strictly(obj) -> str | None:
    """Every stream must carry no filter or exactly ``/FlateDecode``, and a Flate body must
    inflate to end of stream with no trailing bytes.  pypdf's own decoder returns partial or
    empty data on a corrupt payload instead of raising, so the inflate is done here."""
    filters = obj.get("/Filter")
    names = [] if filters is None else [str(f) for f in (filters if isinstance(filters, list) else [filters])]
    if names not in ([], ["/FlateDecode"]):
        return f"unsupported stream filter chain {names}"
    if names:
        d = zlib.decompressobj()
        try:
            out = d.decompress(obj._data, MAX_STREAM_BYTES + 1)
        except zlib.error as e:
            return f"stream does not inflate ({e})"
        if len(out) > MAX_STREAM_BYTES:
            return f"stream inflates beyond the ceiling of {MAX_STREAM_BYTES} bytes"
        if not d.eof or d.unused_data:
            return "stream does not inflate to a complete deflate member"
    obj.get_data()
    return None


def _full_parse(path: Path, top: int) -> str | None:
    """Parse the whole file with pypdf in strict mode, dereference and decode every object.

    This covers what the structural checks above do not model: ``/Prev`` chains,
    object streams and their members, filter and predictor parameters, the body of
    every stream, and the page tree.  ``/Size`` must be one more than the highest
    object number in the whole cross-reference chain: ``top`` from the structural walk
    counts free entries, which pypdf does not record, and pypdf's in-use entries cover
    any hybrid ``/XRefStm`` section.  A missing or broken parser is a failure, never a
    skip.
    """
    try:
        from pypdf import PdfReader
        from pypdf.generic import IndirectObject, StreamObject
    except BaseException as e:  # noqa: BLE001 - a broken parser install must fail closed
        return f"pypdf is not importable ({type(e).__name__}); install the pinned dev dependency"
    try:
        reader = PdfReader(str(path), strict=True)
        size = int(reader.trailer["/Size"])
        ids = [(i, g) for g, table in reader.xref.items() for i in table] + [(i, 0) for i in reader.xref_objStm]
        for idnum, gen in ids:
            obj = reader.get_object(IndirectObject(idnum, gen, reader))
            if isinstance(obj, StreamObject) and (err := _inflate_strictly(obj)):
                return f"object {idnum}: {err}"
        pages = len(reader.pages)
    except Exception as e:  # noqa: BLE001 - any parser failure is a guard failure
        return f"full parse failed ({type(e).__name__}: {str(e)[:120]})"
    top = max(top, *(i for i, _ in ids)) if ids else top
    if not ids or size != top + 1 or pages == 0:
        return f"full parse inconsistent: /Size {size} against highest object number {top}, {len(ids)} objects, {pages} pages"
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
    chain = _xref_chain(raw, off)
    if isinstance(chain, str):
        return [f"{path}: {chain}"]
    problem = _full_parse(path, chain)
    return [f"{path}: {problem}"] if problem else []


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
