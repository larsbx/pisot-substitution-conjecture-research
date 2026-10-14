"""Independent Python oracle for the bounded Mojo aligned-prefix radius probe.

Not theorem support and not the original lost constrained-family enumeration.
This enumerates *every aligned cut* at depths 0..max_depth for the fixed
historical substitution 0->001, 1->22, 2->220, on the swap pair 01|10.
A finite depth-9 witness refutes a radius-8 upper bound for this observable.
The algorithm makes no saturation/infinite-depth/exhaustive-family claim.

Replay from repository root:
    python3 oracles/python/boxwalk_radius_probe.py --max-depth 9 --max-symbols 30000
The output JSON is independently checked against
    evidence/boxwalk-radius8-depth9.json
"""

from __future__ import annotations

import argparse
import json

SIGMA = ((0, 0, 1), (2, 2), (2, 2, 0))


def inflate(word: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(symbol for letter in word for symbol in SIGMA[letter])


def radius_row(depth: int, top: tuple[int, ...], bottom: tuple[int, ...]) -> dict:
    if len(top) != len(bottom):
        raise ValueError("input words have unequal lengths")
    defect = [0, 0, 0]
    radius = 0
    first_cut = 0
    first_defect = [0, 0, 0]
    for cut, (a, b) in enumerate(zip(top, bottom), 1):
        defect[a] += 1
        defect[b] -= 1
        current = max(map(abs, defect))
        if current > radius:
            radius = current
            first_cut = cut
            first_defect = defect.copy()
    if defect != [0, 0, 0]:
        raise ValueError("swap words are not balanced at the terminal cut")
    return {
        "depth": depth,
        "length": len(top),
        "radius": radius,
        "first_max_cut": first_cut,
        "first_max_defect": first_defect,
    }


def probe(max_depth: int = 9, max_symbols: int = 30000) -> dict:
    if max_depth < 0 or max_symbols < 2:
        raise ValueError("depth must be nonnegative and per-side budget at least 2")
    top, bottom = (0, 1), (1, 0)
    rows = []
    for depth in range(max_depth + 1):
        if len(top) > max_symbols or len(bottom) > max_symbols:
            return {
                "status": "BUDGET_EXHAUSTED",
                "completed_through_depth": depth - 1,
                "max_depth": max_depth,
                "max_symbols_per_side": max_symbols,
                "saturation": "NOT_CHECKED",
                "constrained_family_exhaustion": "NOT_CHECKED",
                "rows": rows,
            }
        rows.append(radius_row(depth, top, bottom))
        if depth < max_depth:
            top, bottom = inflate(top), inflate(bottom)
    return {
        "status": ("FINITE_COUNTEREXAMPLE_TO_ALIGNED_RADIUS_LE_8"
                   if any(r["radius"] > 8 for r in rows)
                   else "DEPTH_BUDGET_COMPLETE_NO_VERDICT"),
        "completed_through_depth": max_depth,
        "max_depth": max_depth,
        "max_symbols_per_side": max_symbols,
        "saturation": "NOT_CHECKED",
        "constrained_family_exhaustion": "NOT_CHECKED",
        "rows": rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-depth", type=int, default=9)
    parser.add_argument("--max-symbols", type=int, default=30000)
    args = parser.parse_args()
    print(json.dumps(probe(args.max_depth, args.max_symbols),
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
