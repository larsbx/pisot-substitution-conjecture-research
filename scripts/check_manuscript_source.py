#!/usr/bin/env python3
"""Fail closed if a manuscript source or PDF is missing or not what it claims to be.

``manuscripts/MANIFEST`` lists the required files, one per line.  Every listed
file must exist; every ``.tex`` in the directory must be valid UTF-8 with no
control bytes other than tab and newline, a ``\\documentclass`` first line,
``\\begin{document}`` before ``\\end{document}``, and at least MIN_LINES lines;
every ``.pdf`` must carry the ``%PDF-`` header, a ``startxref`` offset that
(the last one before the final ``%%EOF``) that points at an ``xref`` table with a trailer or at a\n``/Type /XRef`` object with a stream body, and ``%%EOF``
within the last 1024 bytes.  Exit status 1 names every failure, so a missing,
byte-mangled or truncated file never passes.

Usage: check_manuscript_source.py [DIR]   (default: manuscripts/)
"""
from __future__ import annotations

import re
import sys
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


def check_pdf(path: Path) -> list[str]:
    raw = path.read_bytes()
    if not raw.startswith(b"%PDF-"):
        return [f"{path}: missing %PDF- signature (got {raw[:5]!r})"]
    tail_start = max(0, len(raw) - 1024)
    tail = raw[tail_start:]
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
    if re.match(rb"xref\s", at[:8]):
        if b"trailer" not in at:
            return [f"{path}: xref table at {off} has no trailer"]
        return []
    if re.match(rb"\d+\s+\d+\s+obj\b", at[:32]):
        # a cross-reference stream: dictionary, then a stream body, then endstream
        body = at.find(b"stream")
        if body < 0 or b"endstream" not in at[body:]:
            return [f"{path}: object at {off} has no stream body (not a cross-reference stream)"]
        if not re.search(rb"/Type\s*/XRef\b", at[:body]):
            return [f"{path}: startxref offset {off} points at an object that is not a cross-reference stream"]
        return []
    return [f"{path}: startxref offset {off} does not point at an xref table or object"]


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
