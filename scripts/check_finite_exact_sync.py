#!/usr/bin/env python3
"""Check that mojo/finite_exact/ matches its pinned upstream up to the import rewrite.

The vendored files differ from larsbx/NLAP-JT only by the package-qualified
import lines recorded in mojo/finite_exact/UPSTREAM.md. This script reverses
that rewrite and compares SHA-256 digests with the pinned upstream digests, so
no local patch to the arithmetic can land unnoticed. Exit 0 on agreement.
"""

from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / "mojo" / "finite_exact"
PIN = PACKAGE / "UPSTREAM.md"
ROW_RE = re.compile(r"^\| `([^`]+)` \| `([^`]+)` \| `([0-9a-f]{64})` \|$", re.MULTILINE)
COMMIT_RE = re.compile(r"at commit `([0-9a-f]{7,40})`")
REWRITES = [
    ("from finite_exact.bigint_z import", "from bigint_z import"),
    ("from finite_exact.rat_q import", "from rat_q import"),
]


def unrewrite(text: str) -> str:
    return "\n".join(
        next((new + line[len(old):] for old, new in REWRITES if line.startswith(old)), line)
        for line in text.split("\n")
    )


def check() -> list[str]:
    if not PIN.exists():
        return [f"missing pin file {PIN.relative_to(ROOT)}"]
    pin = PIN.read_text(encoding="utf-8")
    if COMMIT_RE.search(pin) is None:
        return ["pin file does not name an upstream commit"]
    rows = ROW_RE.findall(pin)
    if len(rows) < 3:
        return ["pin file lists fewer than three vendored files"]
    errors: list[str] = []
    listed = set()
    for upstream, local, digest in rows:
        path = ROOT / local
        listed.add(path.name)
        if not path.exists():
            errors.append(f"{local}: vendored file missing")
            continue
        actual = hashlib.sha256(unrewrite(path.read_text(encoding="utf-8")).encode("utf-8")).hexdigest()
        if actual != digest:
            errors.append(f"{local}: differs from upstream {upstream} at the pinned commit")
    for path in sorted(PACKAGE.glob("*.mojo")):
        if path.name != "__init__.mojo" and path.name not in listed:
            errors.append(f"{path.relative_to(ROOT)}: not listed in UPSTREAM.md")
    return errors


def main() -> int:
    errors = check()
    if errors:
        print("finite_exact vendoring is out of sync with its upstream pin:\n")
        print("\n".join(errors))
        return 1
    print("OK: mojo/finite_exact matches the pinned upstream up to the recorded import rewrite.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
