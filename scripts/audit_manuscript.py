#!/usr/bin/env python3
"""Audit PSC manuscript sources for stale or overclaiming formulations.

The audit is intentionally conservative: it catches phrases that caused
version drift during the v11 -> v12.1 transition. It is not a LaTeX prover;
it is a CI guardrail against known bad claims.
"""
from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path

TEXT_SUFFIXES = {".tex", ".md", ".txt", ".rst"}
DEFAULT_SKIP_DIRS = {
    ".git",
    ".pytest_cache",
    "__pycache__",
    "dist",
    "build",
    ".venv",
    "venv",
}

CURRENT_SURFACE = {
    "README.md",
    "docs/proof-ladder.md",
    "docs/conjecture-ledger.md",
    "docs/boundary-synchronization.md",
    "docs/automation-protocol.md",
}


@dataclass(frozen=True)
class Rule:
    name: str
    pattern: re.Pattern[str]
    message: str


RULES: tuple[Rule, ...] = (
    Rule(
        name="synthetic-countermodel-transpose",
        pattern=re.compile(r"N[_ ]?C\s*=\s*M[_ ]?sigma(?!\s*(?:\^T|\\top|\^\\top|\^\\T))", re.IGNORECASE),
        message="Synthetic countermodel must be N_C = M_sigma^T, P = I; not N_C = M_sigma.",
    ),
    Rule(
        name="old-cycle-exclusion-target",
        pattern=re.compile(r"no recurrent noncoincident cycle", re.IGNORECASE),
        message="Cycle-exclusion is a retired false target; use SCC Producer / nonsynchronizing trap framing.",
    ),
    Rule(
        name="future-replacement-overclaim",
        pattern=re.compile(r"self-contained replacement is in preparation", re.IGNORECASE),
        message="Do not promise a self-contained replacement; state the precise open conjecture instead.",
    ),
    Rule(
        name="unconditional-main-theorem",
        pattern=re.compile(
            r"Then\s+(?:the\s+)?associated\s+tiling\s+dynamical\s+system\s+has\s+pure\s+discrete\s+spectrum(?![^.]{0,120}conditional)",
            re.IGNORECASE | re.DOTALL,
        ),
        message="Main PDS claim must be explicitly conditional unless SCC Producer is proved.",
    ),
    Rule(
        name="loose-subblock-language",
        pattern=re.compile(r"contains\s+M[_ ]?sigma\s+as\s+an\s+invariant\s+sub-?block", re.IGNORECASE),
        message="Use 'acts on an invariant subspace as a similar copy of M_sigma' instead of loose sub-block language.",
    ),
)


def iter_text_files(root: Path, strict_current: bool = False):
    if strict_current:
        base = root.resolve()
        for rel in sorted(CURRENT_SURFACE):
            path = base / rel
            if path.exists():
                yield path
        return

    for path in root.rglob("*"):
        if path.is_dir():
            continue
        if any(part in DEFAULT_SKIP_DIRS for part in path.parts):
            continue
        if path.suffix.lower() in TEXT_SUFFIXES:
            yield path


def audit_file(path: Path) -> list[str]:
    try:
        text = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return []
    failures: list[str] = []
    lines = text.splitlines()
    for rule in RULES:
        for match in rule.pattern.finditer(text):
            line = text.count("\n", 0, match.start()) + 1
            line_text = lines[line - 1] if line <= len(lines) else ""

            # Meta/documentation uses are not stale mathematical claims.  In
            # particular, the Parikh intertwiner contains the substring
            # "N_C = M_sigma" without asserting the retired synthetic model.
            if rule.name == "synthetic-countermodel-transpose":
                if "P_C N_C = M_sigma P_C" in line_text or "No stale" in line_text:
                    continue
            if rule.name == "old-cycle-exclusion-target" and "Do not cite" in line_text:
                continue

            snippet = " ".join(match.group(0).split())
            failures.append(f"{path}:{line}: {rule.name}: {rule.message} [matched: {snippet!r}]")
    return failures


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd(), help="repository root to audit")
    parser.add_argument(
        "--strict-current",
        action="store_true",
        help="audit only the canonical current manuscript/research surface, not archives",
    )
    args = parser.parse_args(argv)

    root = args.root.resolve()
    failures: list[str] = []
    for path in iter_text_files(root, strict_current=args.strict_current):
        failures.extend(audit_file(path))

    if failures:
        print("PSC manuscript/source audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  - {failure}", file=sys.stderr)
        return 1
    print("PSC manuscript/source audit passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
