#!/usr/bin/env python3
"""Print the exact conjugacy classification of finite endpoint maps."""

from __future__ import annotations

import argparse
import json

from psc_research.endpoint_core import classify_maps, functional_cycle_lengths


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--size", type=int, default=3)
    parser.add_argument("--json", action="store_true", help="emit JSON lines")
    args = parser.parse_args()

    classes = classify_maps(args.size)
    for item in classes:
        row = {
            "representative": list(item.representative),
            "class_size": item.size,
            "cycle_lengths": list(functional_cycle_lengths(item.representative)),
            "globally_synchronizing": item.globally_synchronizing,
            "nonsynchronizing_pairs": [list(pair) for pair in item.nonsynchronizing_pairs],
            "recurrent_core": [list(pair) for pair in item.recurrent_core],
        }
        if args.json:
            print(json.dumps(row, separators=(",", ":"), sort_keys=True))
        else:
            print(
                "rep=", item.representative,
                " class_size=", item.size,
                " cycles=", tuple(row["cycle_lengths"]),
                " globally_sync=", item.globally_synchronizing,
                " nonsync=", len(item.nonsynchronizing_pairs),
                " recurrent_core=", item.recurrent_core,
                sep="",
            )

    print(f"classes={len(classes)} maps={sum(item.size for item in classes)}")


if __name__ == "__main__":
    main()
