#!/usr/bin/env python3
"""Dimension semantics of Tier 2 loop-gain fixtures.

``schemas/tier2-loop-gain-fixture.schema.json`` fixes the shape of a fixture
and pins each fixed-rank channel (``CHANNEL_RANK``) to its power basis. What
JSON Schema cannot express is checked here: every gain vector and every
generated-module generator has exactly one coordinate per basis label, the
labels are distinct, and a power basis has rank equal to the degree of its
monic minimal polynomial. A fixture failing any check has no unambiguous
exact interpretation, so it is rejected rather than read.

Usage:
    check_tier2_fixture.py FIXTURE.json...   exit 1 if any fixture is ill-dimensioned
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

SCHEMA = Path(__file__).resolve().parents[1] / "schemas" / "tier2-loop-gain-fixture.schema.json"

# Channels whose arithmetic module is fixed by the channel name. Mirrored by
# the schema's ``allOf`` conditionals; tests/test_tier2_fixture_check.py keeps
# the two in sync.
CHANNEL_RANK = {"affine_forcing": 3}


def dimension_errors(doc: dict) -> tuple[str, ...]:
    basis = doc["arithmetic_basis"]
    labels = basis["labels"]
    rank = len(labels)
    channel = doc["gain_channel"]
    poly = basis.get("minimal_polynomial")
    vectors = [(f"edge {e['edge_id']}", e["gain_coordinates"]) for e in doc["edges"]] + [
        (f"generator {i}", g) for i, g in enumerate(doc.get("generated_module_generators", []))
    ]
    checks = [
        (len(set(labels)) != rank, "basis labels are not distinct"),
        (
            channel in CHANNEL_RANK
            and (basis["kind"] != "integer_power_basis" or rank != CHANNEL_RANK[channel]),
            f"channel {channel} requires the rank-{CHANNEL_RANK.get(channel)} integer power basis",
        ),
        (
            basis["kind"] == "integer_power_basis" and poly is None,
            "a power basis needs its minimal polynomial",
        ),
        (
            poly is not None and (len(poly) != rank + 1 or poly[-1] != 1),
            f"minimal polynomial must be monic of degree {rank} (the basis rank)",
        ),
    ] + [
        (len(v) != rank, f"{name} has {len(v)} coordinates for a rank-{rank} basis")
        for name, v in vectors
    ]
    return tuple(msg for failed, msg in checks if failed)


def main(paths: list[str]) -> int:
    failures = [
        f"{p}: {msg}" for p in paths for msg in dimension_errors(json.loads(Path(p).read_text()))
    ]
    print("\n".join(failures) or f"{len(paths)} Tier 2 fixture(s) dimensionally consistent")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
