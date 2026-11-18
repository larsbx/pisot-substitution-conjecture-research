#!/usr/bin/env python3
"""Refuse incomplete or altered combined upper recurrence/completion audits.

This authenticates the entire LF-delimited output contract, not a proof. The
producing, source-bound Lean processes must also succeed. Declaration counts
are pinned to the checked-in sources and compiler, so changes require re-audit.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

RECURRENCE = "PSC_CLASS_A_PLUS_UPPER_RECURRENCE"
COMPLETION = "PSC_CLASS_A_PLUS_UPPER_COMPLETION"
RECURRENCE_ENDPOINTS = (
    "family_coefficients", "forward_integer_bound", "eventual_constant_tail",
    "eventual_alternating_tail", "energy_periodic_constant", "shear_bound",
    "twist_recurrence", "reconstruction_delay", "central_coordinate_recurrence",
    "central_gap_in_run", "run_gap_digit_step", "nonzero_upper_cycle_control",
    "half_tie_control",
)
COMPLETION_ENDPOINTS = (
    "decrement_path", "all_ordered_paths", "all_signed_ordered_paths",
    "all_traced_strict_prefixes",
)


def check_log(text: str) -> dict[str, int]:
    """Require all records in order; permit additional empty LF lines only."""
    if not text.endswith("\n"):
        raise ValueError("Lean audit output must end with LF")
    if "\x00" in text or "\r" in text:
        raise ValueError("noncanonical control character in Lean audit output")
    rows = [line.split("\t") for line in text[:-1].split("\n") if line]
    expected = [
        [RECURRENCE + "_MODULE", "PscVerif.ClassAPlusUpperRecurrence", "96", "80"],
        [RECURRENCE + "_DECLARATIONS", "1", "96", "80"],
    ]
    expected += [[RECURRENCE + "_ENDPOINT", "Psc.ClassAPlusUpperRecurrence." + name]
                 for name in RECURRENCE_ENDPOINTS]
    expected += [
        [RECURRENCE + "_AUDIT_COMPLETE", "13", "39"],
        [COMPLETION + "_MODULE", "PscVerif.ClassAPlusUpperCycleCompletion", "20", "18"],
    ]
    expected += [[COMPLETION + "_ENDPOINT", "Psc.ClassAPlusUpperCycleCompletion." + name]
                 for name in COMPLETION_ENDPOINTS]
    expected.append([COMPLETION + "_AUDIT_COMPLETE", "4", "12"])
    if rows != expected:
        raise ValueError("missing, duplicate, reordered, malformed or altered upper recurrence/completion audit receipt")
    return {"modules": 2, "declarations": 116, "theorems": 98,
            "endpoints": 17, "negative_controls": 51}


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
