#!/usr/bin/env python3
"""Check documentation cross-references. Two invariants, both cheap to keep.

1. Index: every note under ``docs/`` is mentioned in ``docs/README.md``. An
   unmentioned note is how record drift starts: the 2026-09-10 audit found
   status surfaces disagreeing because notes accumulated outside the index.

2. References: every repository-relative path mentioned in a live ``.md`` or
   ``.tex`` file resolves, either relative to the mentioning file or to the
   repository root. A path belonging to *another* repository must be qualified
   as ``<repo>:<path>`` (for example ``finite-math-kernels:src/rat_q.mojo``),
   so that a reader can tell a cross-program reference from a broken local one.

A path that deliberately does not resolve -- a file a port table records as
removed, a finding quoting a broken path, a path inside an uploaded archive, a
file a plan proposes to create -- must be declared, per file:

    <!-- check-docs-refs: exempt scripts/old_driver.py -->

Declaring a path that *does* exist is an error, so declarations cannot rot into
silent exemptions.

Not checked: ``archive/`` (immutable historical evidence, whose references are
part of the record), the vendored packages listed in ``vendored.toml`` (fixed
upstream, never patched here), generated files (fix their generator), and the
preserved patches under ``docs/source-imports/``. Exit 0 when both invariants
hold.
"""

from __future__ import annotations

import json
import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SUFFIXES = ("md", "tex", "py", "mojo", "sh", "yml", "yaml", "toml", "json", "lean", "tla", "cfg", "pin", "jsonl", "pdf", "patch")
# a slash-separated path ending in a known suffix
REF = re.compile(r"(?:[A-Za-z0-9_.-]+/)+[A-Za-z0-9_.-]+\.(?:" + "|".join(SUFFIXES) + r")\b")
# a repository tag immediately before a path marks it as living in that
# repository: the `NLAP: docs/x.md` / `FMK: src/y.mojo` convention the
# cross-program notes declare in their own legend, or a bare `<repo>:<path>`
QUALIFIED = re.compile(r"[A-Za-z0-9_.-]+: ?$")
EXEMPT = re.compile(r"<!--\s*check-docs-refs:\s*exempt\s+(.*?)-->")
SKIP_DIRS = {".git", "archive", "__pycache__", ".pixi", ".lake", "node_modules"}


def vendored_files(root: Path) -> set[Path]:
    """Paths of every vendored file, which this repository does not own."""
    pin = root / "vendored.toml"
    if not pin.exists():
        return set()
    data = tomllib.loads(pin.read_text(encoding="utf-8"))
    return {
        root / package["root"] / name
        for package in data.get("package", ())
        for name in package.get("files", {})
    }


def generated_files(root: Path) -> set[Path]:
    """Files written by a generator; a bad reference there is the generator's."""
    ledger = root / "tla" / "ledger.json"
    if not ledger.exists():
        return set()
    index = json.loads(ledger.read_text(encoding="utf-8")).get("index_path")
    return {root / index} if index else set()


def text_files(root: Path) -> list[Path]:
    skip = vendored_files(root) | generated_files(root)
    out = []
    for path in sorted(root.rglob("*")):
        if not path.is_file() or path.suffix not in (".md", ".tex"):
            continue
        relative = path.relative_to(root).parts
        if set(relative) & SKIP_DIRS or path in skip or "source-imports" in relative:
            continue
        out.append(path)
    return out


def unindexed(root: Path) -> list[str]:
    """Notes under docs/ that docs/README.md does not mention."""
    index_path = root / "docs" / "README.md"
    index = index_path.read_text(encoding="utf-8") if index_path.exists() else ""
    return [
        path.name
        for path in sorted((root / "docs").glob("*.md"))
        if path != index_path and path.name not in index
    ]


def unresolved(root: Path, paths: list[Path]) -> list[str]:
    out = []
    for path in paths:
        text = path.read_text(encoding="utf-8")
        exempt = {ref for group in EXEMPT.findall(text) for ref in group.split()}
        for ref in sorted(exempt):
            if (root / ref).exists():
                out.append(f"{path.relative_to(root)}: {ref} is declared exempt but exists")
        for lineno, line in enumerate(text.splitlines(), 1):
            for match in REF.finditer(line):
                ref = match.group()
                before = line[: match.start()]
                if before.endswith("//") or QUALIFIED.search(before):
                    continue  # a URL, or a path qualified with its repository
                if ref in exempt:
                    continue  # declared above, and checked to be genuinely absent
                if (path.parent / ref).exists() or (root / ref).exists():
                    continue
                out.append(f"{path.relative_to(root)}:{lineno}: {ref} does not resolve")
    return out


def main(argv: list[str] | None = None) -> int:
    argv = sys.argv[1:] if argv is None else argv
    root = Path(argv[0]).resolve() if argv else ROOT
    files = text_files(root)
    missing, broken = unindexed(root), unresolved(root, files)
    if missing:
        print(f"{len(missing)} note(s) under docs/ are not mentioned in docs/README.md:\n")
        print("\n".join("  " + name for name in missing))
    if broken:
        print(f"\n{len(broken)} unresolved path reference(s); fix the path, or qualify a")
        print("cross-repository one as <repo>:<path>:\n")
        print("\n".join("  " + line for line in broken))
    if missing or broken:
        return 1
    print(f"OK: docs/README.md indexes every note; every path reference in {len(files)} text files resolves.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
