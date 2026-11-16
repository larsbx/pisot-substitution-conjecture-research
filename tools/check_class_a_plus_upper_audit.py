#!/usr/bin/env python3
"""Refuse incomplete or altered upper-cycle Lean semantic-audit receipts.

This parser authenticates the complete output contract, not the proof itself.
The producing Lean process must succeed separately. Counts are pinned to the
checked-in source and compiler; source changes require a deliberate re-audit.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

PREFIX = "PSC_CLASS_A_PLUS_UPPER"
MODULES = (
    ("PscVerif.ClassAMinusPrefixAssembly", 81, 43),
    ("PscVerif.ClassAPlusUpperCycles", 86, 71),
)
ENDPOINTS = (
    "small_decrement", "base_one_path", "base_two_path", "eight_ordered_paths",
    "signed_ordered_paths", "eight_traced_strict_prefixes", "zero_typed",
    "disputed_last_is_c",
)


def check_log(text: str) -> dict[str, int]:
    """Require complete LF-delimited rows; additional empty LF lines are allowed."""
    if not text.endswith("\n"):
        raise ValueError("Lean audit output must end with LF")
    if "\x00" in text or "\r" in text:
        raise ValueError("noncanonical control character in Lean audit output")
    rows = [line.split("\t") for line in text[:-1].split("\n") if line]
    expected = [[PREFIX + "_MODULE", name, str(decls), str(proofs)]
                for name, decls, proofs in MODULES]
    declarations = sum(row[1] for row in MODULES)
    proofs = sum(row[2] for row in MODULES)
    expected.append([PREFIX + "_DECLARATIONS", "2", str(declarations), str(proofs)])
    expected += [[PREFIX + "_ENDPOINT", "Psc.ClassAPlusUpperCycles." + name]
                 for name in ENDPOINTS]
    expected.append([PREFIX + "_AUDIT_COMPLETE", "8", "24"])
    if rows != expected:
        raise ValueError("missing, duplicate, reordered, malformed or altered upper-cycle audit receipt")
    return {"modules": 2, "declarations": declarations, "theorems": proofs,
            "endpoints": 8, "negative_controls": 24}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    args = parser.parse_args()
    try:
        result = check_log(args.log.read_bytes().decode("utf-8"))
    except (OSError, UnicodeError, ValueError) as exc:
        parser.exit(1, str(exc) + "\n")
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
