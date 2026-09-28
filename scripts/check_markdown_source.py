#!/usr/bin/env python3
"""Reject unexpected ASCII C0 controls in theorem/research Markdown."""

from __future__ import annotations

import argparse
from pathlib import Path


DEFAULT_TARGETS = (Path("README.md"), Path("docs"), Path("manuscripts"))
ALLOWED_CONTROLS = {0x0A}  # LF is the repository's Markdown line separator.


def markdown_files(targets: list[Path]) -> list[Path]:
    files: set[Path] = set()
    for target in targets:
        if target.is_file() and target.suffix.lower() == ".md":
            files.add(target)
        elif target.is_dir():
            files.update(path for path in target.rglob("*.md") if path.is_file())
    return sorted(files)


def unexpected_controls(path: Path) -> list[tuple[int, int, int]]:
    findings = []
    line = 1
    column = 0
    for byte in path.read_bytes():
        column += 1
        if byte < 0x20 and byte not in ALLOWED_CONTROLS:
            findings.append((line, column, byte))
        if byte == 0x0A:
            line += 1
            column = 0
    return findings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="*", type=Path)
    args = parser.parse_args()
    targets = args.targets or list(DEFAULT_TARGETS)
    files = markdown_files(targets)
    failed = False
    for path in files:
        for line, column, byte in unexpected_controls(path):
            failed = True
            print(f"{path}:{line}:{column}: unexpected C0 control 0x{byte:02x}")
    if failed:
        return 1
    print(f"OK Markdown source integrity: {len(files)} file(s) checked")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
