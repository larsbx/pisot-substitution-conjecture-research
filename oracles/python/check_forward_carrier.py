"""Independent literal replay of a canonical Mojo forward-carrier packet.

The producer is the repository's bounded Mojo BPA engine. This oracle does
not enumerate a carrier: it checks a supplied finite ordered carrier and
reconstructs every complete raw child row with independent prefix counts.
Accepted carriers may be closed supersets of the seed-generated states.
The export protocol requires both orientations of every noncoincident state.
Neither this program nor its receipt supplies Lean or productivity acceptance.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


SCHEMA = "psc-forward-carrier-v1"
FIELDS = {
    "schema", "fixture", "substitution", "state_cap", "length_cap",
    "complete", "normalized_state_count", "state_count",
    "max_state_length", "states",
}
STATE_FIELDS = {"top", "bottom", "children"}
FIXTURES = (
    ((1,), (0, 2, 1), (0, 0, 1)),
    ((1,), (0, 1, 2), (0, 0, 1)),
)
SEEDS = {
    ((a, b), (b, a))
    for a in range(3) for b in range(3) if a != b
}


class InvalidCertificate(ValueError):
    """The supplied object does not satisfy the forward-carrier contract."""


def require(condition: bool, message: str) -> None:
    # Do not use Python assertions: refusal must survive python -O.
    if not condition:
        raise InvalidCertificate(message)


def integer(value: Any, minimum: int, maximum: int | None = None) -> bool:
    return (type(value) is int and value >= minimum
            and (maximum is None or value <= maximum))


def word(value: Any, context: str) -> tuple[int, ...]:
    require(type(value) is list and len(value) > 0,
            f"{context}: expected a nonempty word")
    require(all(integer(a, 0, 2) for a in value),
            f"{context}: letters must be exact integers in 0..2")
    return tuple(value)


def prefix_counts(value: tuple[int, ...]) -> list[tuple[int, int, int]]:
    """Both tracks get independent complete prefix-count tables."""
    counts = [0, 0, 0]
    prefixes = [(0, 0, 0)]
    for letter in value:
        counts[letter] += 1
        prefixes.append(tuple(counts))
    return prefixes


def balanced_factors(
    top: tuple[int, ...], bottom: tuple[int, ...]
) -> tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]:
    """Cut exactly at equal prefix-Parikh vectors, including the final cut."""
    require(len(top) == len(bottom), "pair tracks have different lengths")
    top_prefixes, bottom_prefixes = prefix_counts(top), prefix_counts(bottom)
    require(top_prefixes[-1] == bottom_prefixes[-1], "pair is not balanced")
    cuts = [i for i in range(len(top) + 1)
            if top_prefixes[i] == bottom_prefixes[i]]
    return tuple((top[left:right], bottom[left:right])
                 for left, right in zip(cuts, cuts[1:]))


def validate_packet(packet: Any) -> dict[str, Any]:
    """Check the exact declared schema and every literal forward-closure row."""
    require(type(packet) is dict and set(packet) == FIELDS,
            "packet fields do not match the forward-carrier schema")
    require(packet["schema"] == SCHEMA, "wrong forward-carrier schema")
    fixture = packet["fixture"]
    require(integer(fixture, 0, 1), "fixture must be exact integer 0 or 1")
    require(type(packet["substitution"]) is list
            and len(packet["substitution"]) == 3,
            "substitution must have exactly three literal images")
    images = tuple(word(w, f"image {i}")
                   for i, w in enumerate(packet["substitution"]))
    require(images == FIXTURES[fixture], "literal named substitution mismatch")
    require(packet["complete"] is True, "partial or capped packet is inconclusive")
    for name in ("state_cap", "length_cap", "normalized_state_count",
                 "state_count", "max_state_length"):
        require(integer(packet[name], 1), f"{name} must be a positive exact integer")
    require(type(packet["states"]) is list
            and len(packet["states"]) == packet["state_count"],
            "state_count does not match the complete state list")

    decoded: list[tuple[tuple[int, ...], tuple[int, ...]]] = []
    rows: list[tuple[int, ...]] = []
    index: dict[tuple[tuple[int, ...], tuple[int, ...]], int] = {}
    for i, record in enumerate(packet["states"]):
        require(type(record) is dict and set(record) == STATE_FIELDS,
                f"state {i}: unexpected or missing fields")
        top, bottom = word(record["top"], f"state {i} top"), word(record["bottom"], f"state {i} bottom")
        pair = (top, bottom)
        require(pair not in index, f"state {i}: duplicate ordered word pair")
        require(balanced_factors(top, bottom) == (pair,),
                f"state {i}: pair is not an irreducible balanced block")
        require(len(top) <= packet["length_cap"],
                f"state {i}: word length exceeds the declared budget")
        children = record["children"]
        require(type(children) is list
                and all(integer(j, 0, packet["state_count"] - 1) for j in children),
                f"state {i}: child index outside the ordered carrier")
        index[pair] = i
        decoded.append(pair)
        rows.append(tuple(children))

    require(SEEDS <= index.keys(), "carrier omits an actual ordered swap seed")
    require(all((bottom, top) in index for top, bottom in decoded),
            "carrier omits the swapped orientation of a state")
    normalized = {min(pair, (pair[1], pair[0])) for pair in decoded}
    require(len(normalized) == packet["normalized_state_count"],
            "normalized_state_count does not match the decoded swap classes")
    require(len(normalized) <= packet["state_cap"],
            "normalized state count exceeds the declared budget")
    maximum = max(len(top) for top, _ in decoded)
    require(maximum == packet["max_state_length"],
            "max_state_length does not match the decoded words")

    edge_count = repeated_positions = terminal_count = 0
    for i, (top, bottom) in enumerate(decoded):
        if top == bottom:
            require(not rows[i], f"state {i}: coincidence must be terminal")
            terminal_count += 1
            continue
        inflated_top = tuple(letter for a in top for letter in images[a])
        inflated_bottom = tuple(letter for a in bottom for letter in images[a])
        factors = balanced_factors(inflated_top, inflated_bottom)
        require(all(factor in index for factor in factors),
                f"state {i}: an actual child exits the supplied carrier")
        expected = tuple(index[factor] for factor in factors)
        require(rows[i] == expected,
                f"state {i}: complete ordered raw child row mismatch")
        edge_count += len(expected)
        repeated_positions += len(expected) - len(set(expected))

    return {
        "fixture": fixture,
        "substitution": packet["substitution"],
        "state_count": len(decoded),
        "normalized_state_count": len(normalized),
        "terminal_state_count": terminal_count,
        "ordered_child_occurrences": edge_count,
        "repeated_child_occurrences": repeated_positions,
        "max_state_length": maximum,
        "state_cap": packet["state_cap"],
        "length_cap": packet["length_cap"],
        "ordered_seed_count": len(SEEDS),
        "literal_rows_verified": True,
        "finite_closed_carrier_verified": True,
        "exact_reachability_claimed": False,
        "lean_kernel_acceptance": False,
        "productivity_claimed": False,
    }


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON field: {key}")
        result[key] = value
    return result


def _reject_constant(value: str) -> None:
    raise InvalidCertificate(f"non-JSON numeric constant: {value}")


def parse_packet(data: bytes) -> Any:
    try:
        return json.loads(data.decode("utf-8"), object_pairs_hook=_unique_object,
                          parse_constant=_reject_constant)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise InvalidCertificate(f"invalid UTF-8 JSON packet: {error}") from error


def verify_bytes(data: bytes) -> dict[str, Any]:
    result = validate_packet(parse_packet(data))
    return {"source_sha256": hashlib.sha256(data).hexdigest(), **result}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("packets", type=Path, nargs="+", help="complete native JSON packet(s)")
    args = parser.parse_args()
    try:
        # Print nothing until every requested packet has passed.
        receipts = [{"source_path": str(path), **verify_bytes(path.read_bytes())}
                    for path in args.packets]
    except (OSError, InvalidCertificate) as error:
        parser.error(str(error))
    print(json.dumps({
        "schema": "psc-forward-carrier-oracle-receipt-v1",
        "scope": "independent literal rows and finite closed ordered carriers",
        "oracle_source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "packets": receipts,
        "lean_kernel_acceptance": False,
        "productivity_claimed": False,
    }, separators=(",", ":"), sort_keys=True))


if __name__ == "__main__":
    main()
