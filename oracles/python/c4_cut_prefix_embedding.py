#!/usr/bin/env python3
"""Independent literal oracle for canonical Mojo cut-prefix witness packets.

The oracle expands the whole words, locates each parent by binary search on
independently computed block boundaries, and recounts literal prefix slices.
Matrix action uses unbounded Python integers and repeated incidence action.
It compares the entire declared finite domain, full marks, reference points,
signed corrections and every lower-depth residue witness. No aggregate-only
acceptance, finite-to-universal promotion, or positivity inference is made.
"""

from __future__ import annotations

import argparse
from bisect import bisect_right
from copy import deepcopy
from functools import lru_cache
import hashlib
import json
from pathlib import Path


SCHEMA = "c4-cut-prefix-embedding-v1"
IMAGES = (((1,), (0, 2, 1), (0, 0, 1)), ((1,), (0, 1, 2), (0, 0, 1)))
POWERS = (0, 2, 4, 6)
SOURCES = ((0, 1, 2), (2, 0, 1, 0), (1, 2, 0))
CAPS = {"power": 6, "source": 8, "word": 100000}
SCOPE = "finite literal embedding and residue witnesses; no limiting or measure conclusion"


class InvalidPacket(ValueError):
    """The complete literal packet or its declared domain differs."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise InvalidPacket(message)


@lru_cache(maxsize=None)
def inflated(fixture: int, source: tuple[int, ...], power: int) -> tuple[int, ...]:
    require(type(fixture) is int and fixture in (0, 1), "unknown fixture")
    require(type(power) is int and 0 <= power <= 8, "outside inflation power")
    require(all(type(a) is int and 0 <= a < 3 for a in source), "bad source letter")
    value = source
    for _ in range(power):
        value = tuple(a for b in value for a in IMAGES[fixture][b])
        require(len(value) <= CAPS["word"], "word budget")
    return value


def counts(value: tuple[int, ...]) -> tuple[int, int, int]:
    return tuple(value.count(a) for a in range(3))


def subtract(a, b):
    return tuple(x - y for x, y in zip(a, b, strict=True))


def action(fixture: int, value, power: int):
    result = tuple(value)
    for _ in range(power):
        result = tuple(sum(IMAGES[fixture][parent].count(letter) * result[parent]
                           for parent in range(3)) for letter in range(3))
    return result


def witness(fixture: int, source: tuple[int, ...], power: int, position: int) -> dict:
    require(power in POWERS, "named reference only admits compatible even powers")
    require(0 < len(source) <= CAPS["source"], "source budget")
    output = inflated(fixture, source, power)
    require(type(position) is int and 0 <= position < len(output), "no following occurrence")
    blocks = [inflated(fixture, (a,), power) for a in source]
    boundaries = [0]
    for block in blocks:
        boundaries.append(boundaries[-1] + len(block))
    parent = bisect_right(boundaries, position) - 1
    local = position - boundaries[parent]
    block = blocks[parent]
    reference = inflated(fixture, (0,), 2)
    j = reference.index(source[parent])
    reference_position = len(inflated(fixture, reference[:j], power)) + local
    # Direct seed inflation is independent of the native reference construction.
    fixed_prefix = inflated(fixture, (0,), power + 2)
    require(fixed_prefix[reference_position] == output[position] == block[local],
            "following letter changed")
    x = counts(output[:position])
    y = counts(fixed_prefix[:reference_position])
    z = subtract(counts(source[:parent]), counts(reference[:j]))
    difference = subtract(x, y)
    require(difference == action(fixture, z, power), "signed prefix identity")
    residues = [action(fixture, z, power - q) for q in range(power + 1)]
    for q, value in enumerate(residues):
        require(action(fixture, value, q) == difference, "lower residue witness")
    return {
        "address": [fixture, power, position, parent, local, source[parent],
                    output[position], j, reference_position],
        "source": list(source),
        "reference": list(reference),
        "parent_before": list(source[:parent]),
        "parent_after": list(source[parent + 1:]),
        "local_before": list(block[:local]),
        "local_after": list(block[local + 1:]),
        "point": list(x),
        "reference_point": list(y),
        "correction": list(z),
        "residue_witnesses": [list(value) for value in residues],
    }


@lru_cache(maxsize=1)
def expected_packet() -> dict:
    witnesses = [witness(f, u, k, i) for f in range(2) for k in POWERS for u in SOURCES
                 for i in range(len(inflated(f, u, k)))]
    balanced = []
    for f in range(2):
        for k in POWERS:
            top = inflated(f, (0, 1), k)
            bottom = inflated(f, (1, 0), k)
            require(counts(top) == counts(bottom), "two complete tracks unbalanced")
            for i in range(len(top)):
                if counts(top[:i]) == counts(bottom[:i]):
                    balanced.append({"top": witness(f, (0, 1), k, i),
                                     "bottom": witness(f, (1, 0), k, i)})
    distinct = sum(pair["top"]["address"][6] != pair["bottom"]["address"][6]
                   for pair in balanced)
    return {
        "schema": SCHEMA,
        "fixtures": [0, 1],
        "powers": list(POWERS),
        "sources": [list(u) for u in SOURCES],
        "caps": dict(CAPS),
        "scope": SCOPE,
        "witnesses": witnesses,
        "balanced_cuts": balanced,
        "counts": [len(witnesses), sum(len(w["residue_witnesses"]) for w in witnesses),
                   len(balanced), distinct],
    }


def exact_equal(actual, expected, path="packet") -> None:
    require(type(actual) is type(expected), f"{path}: incorrect JSON type")
    if isinstance(expected, dict):
        require(actual.keys() == expected.keys(), f"{path}: field inventory mismatch")
        for key in expected:
            exact_equal(actual[key], expected[key], f"{path}.{key}")
    elif isinstance(expected, list):
        require(len(actual) == len(expected), f"{path}: complete record count mismatch")
        for i, (a, e) in enumerate(zip(actual, expected, strict=True)):
            exact_equal(a, e, f"{path}[{i}]")
    else:
        require(actual == expected, f"{path}: literal value mismatch")


def strict_loads(text: str):
    def object_pairs(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, f"duplicate JSON key: {key}")
            result[key] = value
        return result

    def reject_number(value):
        raise InvalidPacket(f"noninteger JSON number: {value}")

    return json.loads(text, object_pairs_hook=object_pairs,
                      parse_float=reject_number, parse_constant=reject_number)


def verify_packet(packet) -> None:
    exact_equal(packet, expected_packet())


def run_controls() -> list[str]:
    source = expected_packet()
    # Choose a genuine nonzero-correction record with a nonempty local suffix.
    victim = next(i for i, w in enumerate(source["witnesses"])
                  if w["address"][1] == 2 and any(w["correction"])
                  and w["local_before"] and w["local_after"])
    controls = []
    for mode in range(15):
        bad = deepcopy(source)
        row = bad["witnesses"][victim]
        if mode == 0:
            bad["witnesses"].pop()
        elif mode == 1:
            bad["witnesses"][0], bad["witnesses"][1] = bad["witnesses"][1], bad["witnesses"][0]
        elif mode == 2:
            bad["witnesses"].append(deepcopy(row))
        elif mode == 3:
            row["address"][0] = 1 - row["address"][0]
        elif mode == 4:
            row["reference"].reverse()
        elif mode == 5:
            row["address"][3] += 1
        elif mode == 6:
            row["local_before"].append(0)
        elif mode == 7:
            row["local_after"].pop()
        elif mode == 8:
            row["correction"] = [-a for a in row["correction"]]
        elif mode == 9:
            row["reference_point"][0] += 1
        elif mode == 10:
            row["residue_witnesses"].pop()
        elif mode == 11:
            row["residue_witnesses"][0][0] += 1
        elif mode == 12:
            row["address"][0] = bool(row["address"][0])
        elif mode == 13:
            bad["extra_unreviewed_claim"] = "positive measure"
        else:
            bad["balanced_cuts"][0]["bottom"]["point"][0] += 1
        try:
            verify_packet(bad)
        except InvalidPacket:
            controls.append(f"full_packet_mutation_{mode}")
        else:
            raise InvalidPacket(f"control {mode} unexpectedly accepted")
    for value in ('{"schema":1,"schema":2}', '{"value":1.0}', '{"value":NaN}'):
        try:
            strict_loads(value)
        except InvalidPacket:
            controls.append("strict_json_" + str(len(controls)))
        else:
            raise InvalidPacket("ambiguous JSON control accepted")
    # z=e0 is not in M Z^3: its first-minus-third coordinate is odd,
    # whereas that difference equals twice the third input coordinate on Mz.
    for fixture in range(2):
        basis = (1, 0, 0)
        require((basis[0] - basis[2]) % 2 == 1, "deeper residue counterexample")
        require(action(fixture, basis, 0) != (0, 0, 0), "nonzero residue correction")
    controls.append("finite_residue_agreement_does_not_identify_points")
    return controls


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", type=Path)
    parser.add_argument("--controls", action="store_true")
    args = parser.parse_args()
    result = {"schema": SCHEMA, "finite_domain_counts": expected_packet()["counts"],
              "scope": SCOPE, "native_compared": False}
    if args.native:
        data = args.native.read_bytes()
        require(len(data) <= 16_000_000, "packet exceeds byte budget")
        verify_packet(strict_loads(data.decode("utf-8")))
        result["native_compared"] = True
        result["native_sha256"] = hashlib.sha256(data).hexdigest()
    if args.controls:
        result["controls"] = run_controls()
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
