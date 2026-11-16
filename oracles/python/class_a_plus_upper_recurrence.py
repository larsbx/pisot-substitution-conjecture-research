"""Strict independent replay of actual canonical upper-central transcripts.

Every source in the declared finite grid, literal child, full integral offset,
nearest-phase cutoff, two-coordinate reserve and original prefix is checked.
This parser authenticates mathematical transcript content; the separately
source-bound Mojo runner authenticates execution and completion.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re
import runpy

O = runpy.run_path(str(Path(__file__).with_name("class_a_plus_upper_recurrence_independent.py")))
CONTRACT = "contract-receipt: class_a_plus_upper_central_to_zero_paths"
MAX_BYTES = 16 * 1024 * 1024
TOTAL = re.compile(r"PLUS_UPPER_CENTRAL_TOTAL paths=(0|[1-9][0-9]*) edges=(0|[1-9][0-9]*) "
                   r"central_edges=(0|[1-9][0-9]*) max_depth=(0|[1-9][0-9]*) "
                   r"max_central=(0|[1-9][0-9]*) max_prefix_digits=(0|[1-9][0-9]*) "
                   r"controls=(0|[1-9][0-9]*)")


@lru_cache(maxsize=1)
def expected_sources():
    return frozenset(O["source_grid"]())


def parse_row(line, members=None):
    tokens = line.split(" ")
    if tokens[0] != "PLUS_UPPER_CENTRAL_PATH" or any(not token for token in tokens):
        raise ValueError("malformed native central path spacing or tag")
    try:
        values = tuple(int(token) for token in tokens[1:])
    except ValueError as error:
        raise ValueError("native central path needs complete integer fields") from error
    if any(str(value) != token for value, token in zip(values, tokens[1:])):
        raise ValueError("noncanonical native central integer")
    if len(values) < 14:
        raise ValueError("truncated native central header")
    n, J, p, q, r, central_depth, depth, B = values[:8]
    key = (n, J, p, q, r)
    if key not in expected_sources():
        raise ValueError("native central source outside the required finite set")
    if not 0 <= central_depth <= depth <= O["STEP_CAP"] or len(values) != 14+7*depth:
        raise ValueError("native central depth or complete field count mismatch")
    if members is None:
        members = {}
    if (n, J) not in members:
        members[n, J] = O["LiteralMember"](n, J)
    member = members[n, J]
    source = (2, 2, p, q, r)
    record = dict(n=n, J=J, source=source, central_depth=central_depth, B=B, steps=[])
    current = source
    for offset in range(8, 8+7*depth, 7):
        i, j, *target = values[offset:offset+7]
        _, top_prefix, bottom_prefix = member.step(current, (i, j))
        record["steps"].append(dict(source=current, indices=(i, j), target=target,
                                    top_prefix=top_prefix, bottom_prefix=bottom_prefix))
        current = tuple(target)
    result = O["replay"](member, record)
    P, Q = values[-6:-3], values[-3:]
    if result["P"] != P or result["Q"] != Q:
        raise ValueError("native central original prefixes differ")
    record["result"] = result
    return key, record


def verify_transcript(contents):
    if not isinstance(contents, str) or len(contents.encode("utf-8")) > MAX_BYTES:
        raise ValueError("native central transcript resource cap: no verdict")
    if "\r" in contents or "\x00" in contents or not contents.endswith("\n"):
        raise ValueError("native central transcript requires complete LF records")
    lines = contents[:-1].split("\n")
    if len(lines) != len(expected_sources())+2 or lines[-1] != CONTRACT:
        raise ValueError("missing, malformed or duplicate native central completion receipts")
    total = TOTAL.fullmatch(lines[-2])
    if total is None:
        raise ValueError("malformed native central totals")
    declared = tuple(map(int, total.groups()))
    if declared[0] != len(expected_sources()) or declared[-1] != 28:
        raise ValueError("native central source or control count mismatch")
    members, paths = {}, {}
    edges = central_edges = max_depth = max_central = 0
    max_digits = 1
    for line in lines[:-2]:
        key, record = parse_row(line, members)
        if key in paths:
            raise ValueError("duplicate native central source")
        paths[key] = record
        result = record["result"]
        edges += result["depth"]
        central_edges += result["central_depth"]
        max_depth = max(max_depth, result["depth"])
        max_central = max(max_central, result["central_depth"])
        max_digits = max(max_digits, *(len(str(v)) for side in ("P", "Q") for v in result[side]))
    actual = (len(paths), edges, central_edges, max_depth, max_central, max_digits, 28)
    if set(paths) != expected_sources() or declared != actual:
        raise ValueError("incomplete native central source set or false totals")
    return dict(status="accepted_finite_native_central_replay", paths=len(paths), edges=edges,
                central_edges=central_edges, maximum_depth=max_depth, maximum_central_depth=max_central,
                maximum_prefix_digits=max_digits, native_controls=28,
                complete_original_prefixes=True, recurrence_executed=True,
                all_source_entry=False, universal_BH=False,
                transcript_sha256=hashlib.sha256(contents.encode("utf-8")).hexdigest(),
                oracle_sha256=hashlib.sha256(Path(O["__file__"]).read_bytes()).hexdigest(),
                adapter_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", type=Path, required=True)
    args = parser.parse_args()
    if args.native.stat().st_size > MAX_BYTES:
        raise ValueError("native central transcript resource cap: no verdict")
    result = verify_transcript(args.native.read_bytes().decode("utf-8"))
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
