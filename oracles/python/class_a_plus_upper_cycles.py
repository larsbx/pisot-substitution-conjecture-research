"""Strict independent replay of the canonical eight-case Mojo transcript.

The arithmetic checker is independently written in class_a_plus_upper_independent.
No native recipe or native arithmetic is imported. Every original occurrence,
complete offset and accumulated prefix is replayed before totals are accepted.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import runpy

O = runpy.run_path(str(Path(__file__).with_name("class_a_plus_upper_independent.py")))
CASES = O["CASES"]
N_VALUES = (7, 8, 9, 10, 11, 12, 16, 31, 64, 127)
DEPTHS = dict(zip(CASES, (3, 3, 5, 7, 3, 5, 2, 2)))
TOTAL = "PLUS_UPPER_TOTAL paths=160 edges=600 max_depth=7 controls=23"
CONTRACT = "contract-receipt: class_a_plus_upper_eight_literal_paths"
MAX_BYTES = 2 * 1024 * 1024


def parse_row(line):
    tokens = line.split(" ")
    if tokens[0] != "PLUS_UPPER_PATH" or any(not token for token in tokens):
        raise ValueError("malformed native path spacing or tag")
    try:
        values = tuple(int(token) for token in tokens[1:])
    except ValueError as error:
        raise ValueError("native path needs complete integer fields") from error
    if any(str(value) != token for value, token in zip(values, tokens[1:])):
        raise ValueError("noncanonical native integer")
    if len(values) < 16:
        raise ValueError("truncated native path header")
    n, J, H, flip, a, b, p, q, r, depth = values[:10]
    if n not in N_VALUES or (J, H) not in CASES or flip not in (0, 1):
        raise ValueError("native source outside required finite set")
    if depth != DEPTHS[J, H] or len(values) != 16 + 7 * depth:
        raise ValueError("native depth or complete field count mismatch")
    member = O["LiteralMember"](n, J)
    source = (a, b, p, q, r)
    record = dict(n=n, J=J, H=H, flip=bool(flip), source=source, steps=[])
    current = source
    for offset in range(10, 10 + 7 * depth, 7):
        i, j, *target = values[offset:offset + 7]
        # Count the selected literal prefixes; do not obtain indices from a
        # constructor or replace the supplied target with our expected child.
        _, top_prefix, bottom_prefix = member.step(current, (i, j))
        record["steps"].append(dict(source=current, indices=(i, j), target=target,
            top_prefix=top_prefix, bottom_prefix=bottom_prefix))
        current = tuple(target)
    result = O["replay"](member, record)
    P, Q = values[-6:-3], values[-3:]
    if result["P"] != P or result["Q"] != Q:
        raise ValueError("native original prefix witnesses differ")
    record["result"] = result
    return (n, J, H, bool(flip)), record


def verify_transcript(contents):
    if not isinstance(contents, str) or len(contents.encode("utf-8")) > MAX_BYTES:
        raise ValueError("native transcript resource cap: no verdict")
    if "\r" in contents or not contents.endswith("\n"):
        raise ValueError("native transcript requires complete LF records")
    lines = contents[:-1].split("\n")
    if len(lines) != 162 or lines[-2:] != [TOTAL, CONTRACT]:
        raise ValueError("missing, malformed or duplicate native completion receipts")
    paths = {}
    edges = 0
    maximum = 0
    for line in lines[:-2]:
        key, record = parse_row(line)
        if key in paths:
            raise ValueError("duplicate native source")
        paths[key] = record
        edges += record["result"]["depth"]
        maximum = max(maximum, record["result"]["depth"])
    expected = {(n, J, H, flip) for n in N_VALUES for J, H in CASES
                for flip in (False, True)}
    if set(paths) != expected or edges != 600 or maximum != 7:
        raise ValueError("incomplete native source set or totals")
    return dict(status="accepted_finite_native_replay", paths=len(paths), edges=edges,
        maximum_depth=maximum, native_controls=23, complete_original_prefixes=True,
        transcript_sha256=hashlib.sha256(contents.encode()).hexdigest(),
        oracle_sha256=hashlib.sha256(Path(O["__file__"]).read_bytes()).hexdigest(),
        adapter_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        recurrence_executed=False, all_source_entry=False, universal_BH=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", type=Path, required=True)
    args = parser.parse_args()
    if args.native.stat().st_size > MAX_BYTES:
        raise ValueError("native transcript resource cap: no verdict")
    print(json.dumps(verify_transcript(args.native.read_bytes().decode("utf-8")),
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
