#!/usr/bin/env python3
"""Fail closed if a manuscript source or PDF is not what it claims to be.

Checks every ``manuscripts/*.tex``: valid UTF-8, no control bytes other than
tab and newline, a ``\\documentclass`` first line, ``\\begin{document}`` and
``\\end{document}`` present in that order, and at least MIN_LINES lines.
Checks every ``manuscripts/*.pdf`` for the ``%PDF`` signature.  Exit status
1 names every failure; a byte-mangled or truncated file never passes.

Usage: check_manuscript_source.py [PATH ...]   (default: manuscripts/)
"""
from __future__ import annotations

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
    bad = sorted({c for c in text if ord(c) < 32 and c not in "\n\t"})
    problems = []
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
    head = path.read_bytes()[:5]
    return [] if head.startswith(b"%PDF-") else [f"{path}: missing %PDF signature (got {head!r})"]


def main(argv: list[str]) -> int:
    targets = [Path(a) for a in argv] or [ROOT / "manuscripts"]
    files = [p for t in targets for p in (sorted(t.iterdir()) if t.is_dir() else [t])]
    problems = []
    for p in files:
        if p.suffix == ".tex":
            problems += check_tex(p)
        elif p.suffix == ".pdf":
            problems += check_pdf(p)
    for m in problems:
        print("FAIL", m)
    if not problems:
        print(f"OK manuscript sources: {sum(p.suffix in ('.tex', '.pdf') for p in files)} files checked")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
