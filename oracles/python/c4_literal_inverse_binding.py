"""Independent oracle for literal inverse rows, orientation and finite ancestry.

Canonical implementation: ``kernel/psc/c4_literal_inverse_binding.mojo``.
The pre-code gate is ``docs/c4-literal-inverse-binding-literature-2026-11-10.md``.
This verifier reconstructs literal prefixes by rescanning words, solves the
inverse equation with Fraction Gaussian elimination, and independently scans
all forward position pairs on both orientations of the represented domain.
It makes no compact-cover, measure, positivity or general C4 assertion.
"""

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from itertools import zip_longest
from pathlib import Path
import argparse
import hashlib
import io
import json

import c4_pair_overlap_new_incidence as historical


SCHEMA = "c4-literal-inverse-binding-v1"
ROOT = Path(__file__).resolve().parents[2]
HISTORICAL_REVISION = "0f4b9a05ce95e59d9b6cde11fcdf22d161375030"
ROOTS = ((0, 1, 0, 0, 0), (0, 2, 0, 0, 0), (1, 2, 0, 0, 0))
STATE_CAP = 20000
ROW_CAP = 81
SOURCE_COUNT = 12


class InvalidCertificate(ValueError):
    """A finite binding failed; no mathematical conclusion is authorized."""


def require(condition, message):
    # This explicit branch is retained under python -O.
    if not condition:
        raise InvalidCertificate(message)


def _integer(value, lower=None, upper=None):
    return (type(value) is int and (lower is None or lower <= value)
            and (upper is None or value <= upper))


def source_images(index):
    require(_integer(index, 0, SOURCE_COUNT - 1), "source outside twelve-order class")
    middle = ((0, 1, 2), (0, 2, 1), (1, 0, 2),
              (1, 2, 0), (2, 0, 1), (2, 1, 0))
    return (1, 1), middle[index // 2], ((0, 1), (1, 0))[index % 2]


def square_words(images):
    return tuple(tuple(c for a in word for c in images[a]) for word in images)


def incidence(words):
    return tuple(tuple(word.count(c) for word in words) for c in range(3))


def matrix_product(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(3))
                       for j in range(3)) for i in range(3))


def matrix_vector(a, vector):
    return tuple(sum(x * y for x, y in zip(row, vector)) for row in a)


def _fraction_inverse(matrix):
    """Independent exact elimination; no native cofactor formula is imported."""
    rows = [[Fraction(x) for x in row] + [Fraction(i == j) for j in range(3)]
            for i, row in enumerate(matrix)]
    for column in range(3):
        pivot = next((r for r in range(column, 3) if rows[r][column]), None)
        require(pivot is not None, "singular powered incidence")
        rows[column], rows[pivot] = rows[pivot], rows[column]
        divisor = rows[column][column]
        rows[column] = [entry / divisor for entry in rows[column]]
        for r in range(3):
            if r != column:
                factor = rows[r][column]
                rows[r] = [x - factor * y for x, y in zip(rows[r], rows[column])]
    return tuple(tuple(row[3:]) for row in rows)


@lru_cache(maxsize=1)
def inverse_rows():
    matrix = incidence(square_words(source_images(0)))
    a, b, c = matrix
    determinant = (a[0] * (b[1]*c[2]-b[2]*c[1])
                   - a[1] * (b[0]*c[2]-b[2]*c[0])
                   + a[2] * (b[0]*c[1]-b[1]*c[0]))
    require(determinant == 4, "literal two-step determinant")
    inverse = _fraction_inverse(matrix)
    # Gaussian output is converted to exact scaled integer row maps once.
    # The common denominator is computed, not assumed from the native code.
    from math import lcm
    denominator = lcm(*(entry.denominator for row in inverse for entry in row))
    numerators = tuple(tuple(int(entry * denominator) for entry in row) for row in inverse)
    require(denominator == 4, "two-step integral inverse denominator")
    require(matrix_product(matrix, numerators)
            == tuple(tuple(denominator * int(i == j) for j in range(3)) for i in range(3)),
            "exact inverse identity")
    return denominator, numerators


def integral_ancestor_offset(delta):
    require(type(delta) is tuple and len(delta) == 3
            and all(_integer(x, -1000000, 1000000) for x in delta),
            "bounded integral inverse input")
    denominator, numerator = inverse_rows()
    values = matrix_vector(numerator, delta)
    if any(value % denominator for value in values):
        return None
    result = tuple(value // denominator for value in values)
    require(matrix_vector(incidence(square_words(source_images(0))), result) == delta,
            "integral inverse reconstruction")
    return result


def swap(state):
    return state[1], state[0], *(-value for value in state[2:])


def canonical(state):
    return min(state, swap(state))


@dataclass(frozen=True)
class Digit:
    selected: int
    parent: int
    position: int
    prefix: tuple


@dataclass(frozen=True)
class Slot:
    target: int
    top: int
    bottom: int
    swapped: int


@dataclass(frozen=True)
class Binding:
    source: int
    images: tuple
    words: tuple
    digits: tuple
    states: tuple
    rows: tuple
    births: tuple


def literal_digits(words):
    # Rescanning each prefix is intentionally independent of the Mojo running
    # prefix accumulator. The supported images have only eighteen positions.
    return tuple(Digit(letter, parent, position,
                       tuple(word[:position].count(c) for c in range(3)))
                 for parent, word in enumerate(words)
                 for position, letter in enumerate(word))


@lru_cache(maxsize=SOURCE_COUNT)
def historical_snapshot(index):
    """Freeze the independently rebuilt old graph before it enters a cache."""
    source_images(index)
    graph = historical.build_graph(index)
    states = tuple(tuple(state) for state in graph.states)
    rows = tuple(tuple(row) for row in graph.rows)
    return states, rows


def _internal_rows(states, digits):
    lookup = {state: i for i, state in enumerate(states)}
    by_letter = tuple(tuple(i for i, digit in enumerate(digits) if digit.selected == c)
                      for c in range(3))
    rows = []
    for state in states:
        row = []
        for top in by_letter[state[0]]:
            p = digits[top]
            for bottom in by_letter[state[1]]:
                q = digits[bottom]
                delta = tuple(state[2+k] + q.prefix[k] - p.prefix[k] for k in range(3))
                offset = integral_ancestor_offset(delta)
                if offset is None:
                    continue
                raw = (p.parent, q.parent, *offset)
                representative = canonical(raw)
                target = lookup.get(representative)
                # Membership is the only retention test here. In particular,
                # neither the stable box nor the typed carrier is consulted.
                if target is not None:
                    row.append(Slot(target, top, bottom, int(raw != representative)))
        require(len(row) <= ROW_CAP, "internal row budget exhausted; inconclusive")
        rows.append(tuple(row))
    return tuple(rows)


def _discovery_births(rows):
    births = [None] * len(rows)
    for i in range(3):
        births[i] = (-1, -1)
    for row_id, row in enumerate(rows):
        for position, slot in enumerate(row):
            if births[slot.target] is None:
                require(row_id < slot.target, "discovery is not from an earlier state")
                births[slot.target] = (row_id, position)
    require(all(birth is not None for birth in births), "state lacks an inverse ancestry witness")
    return tuple(births)


def check_births(binding):
    require(type(binding.births) is tuple and len(binding.births) == len(binding.states),
            "birth inventory dimensions")
    depths = [0] * len(binding.states)
    for vertex, birth in enumerate(binding.births):
        require(type(birth) is tuple and len(birth) == 2
                and all(_integer(value) for value in birth), "malformed birth witness")
        if vertex < 3:
            require(birth == (-1, -1), "declared root has a forged birth")
            continue
        source, position = birth
        require(0 <= source < vertex, "circular or non-earlier birth witness")
        require(0 <= position < len(binding.rows[source]), "birth slot outside its source row")
        require(binding.rows[source][position].target == vertex,
                "birth witness does not reach its declared state")
        depths[vertex] = depths[source] + 1
    require(binding.births == _discovery_births(binding.rows),
            "birth witnesses differ from deterministic first discovery")
    return tuple(depths)


def check_lifted_edges(binding):
    """Independently compare both full positional inventories, not just counts."""
    states = binding.states
    lift = tuple(packet for state in states for packet in (state, swap(state)))
    require(len(set(lift)) == 2 * len(states), "ordered lift is not free with unique orbit representatives")
    lookup = {packet: i for i, packet in enumerate(lift)}
    inverse_edges = set()
    inverse_counts = Counter()
    for source, row in enumerate(binding.rows):
        for slot in row:
            p, q = binding.digits[slot.top], binding.digits[slot.bottom]
            ancestor = 2 * slot.target + slot.swapped
            edge = (ancestor, p.position, q.position, 2 * source)
            mate = (ancestor ^ 1, q.position, p.position, 2 * source + 1)
            require(edge not in inverse_edges and mate not in inverse_edges,
                    "duplicate ordered positional occurrence")
            inverse_edges.add(edge)
            inverse_edges.add(mate)
            inverse_counts[source, slot.target] += 1
    forward_edges = set()
    forward_counts = Counter()
    matrix = incidence(binding.words)
    positions = tuple(tuple(digit for digit in binding.digits if digit.parent == letter)
                      for letter in range(3))
    for ancestor, state in enumerate(lift):
        linear = matrix_vector(matrix, state[2:])
        for p in positions[state[0]]:
            for q in positions[state[1]]:
                offset = tuple(linear[k] + p.prefix[k] - q.prefix[k] for k in range(3))
                child = (p.selected, q.selected, *offset)
                target = lookup.get(child)
                if target is not None:
                    forward_edges.add((ancestor, p.position, q.position, target))
                    if ancestor % 2 == 0:
                        forward_counts[target // 2, ancestor // 2] += 1
    require(inverse_edges == forward_edges, "lifted internal positional edge inventory mismatch")
    require(inverse_counts == forward_counts, "actual quotient count transpose mismatch")
    for ancestor, top, bottom, child in forward_edges:
        require((ancestor ^ 1, bottom, top, child ^ 1) in forward_edges,
                "lifted edge involution lacks its swapped mate")
    return len(lift), len(forward_edges), len(inverse_counts)


@lru_cache(maxsize=SOURCE_COUNT)
def reference(index):
    images = source_images(index)
    words = square_words(images)
    require(incidence(words) == matrix_product(incidence(images), incidence(images)),
            "actual iterate incidence differs from the powered matrix")
    digits = literal_digits(words)
    require(len(digits) == 18, "literal two-step digit inventory")
    states, old_rows = historical_snapshot(index)
    require(3 <= len(states) <= STATE_CAP and states[:3] == ROOTS, "historical state inventory")
    require(all(canonical(state) == state and state != swap(state) for state in states),
            "canonical domain contains a noncanonical or fixed packet")
    require(len(set(states)) == len(states), "duplicate canonical state")
    rows = _internal_rows(states, digits)
    require(tuple(tuple(slot.target for slot in row) for row in rows) == old_rows,
            "historical rows differ from complete internal literal rows")
    binding = Binding(index, images, words, digits, states, rows, _discovery_births(rows))
    check_births(binding)
    check_lifted_edges(binding)
    return binding


def validate_binding(binding):
    """Accept a supplied binding only against the complete immutable reference."""
    require(type(binding) is Binding, "unsupported binding object")
    expected = reference(binding.source)
    require(all(type(words) is tuple and len(words) == 3
                and all(type(word) is tuple and all(_integer(c, 0, 2) for c in word)
                        for word in words)
                for words in (binding.images, binding.words)),
            "literal images require integer words")
    require(binding.images == expected.images and binding.words == expected.words,
            "actual substitution or iterated word mismatch")
    require(type(binding.digits) is tuple and len(binding.digits) == 18, "digit inventory dimensions")
    for supplied, correct in zip(binding.digits, expected.digits):
        require(type(supplied) is Digit and _integer(supplied.selected, 0, 2)
                and _integer(supplied.parent, 0, 2) and _integer(supplied.position, 0, 17)
                and type(supplied.prefix) is tuple and len(supplied.prefix) == 3
                and all(_integer(x, 0, 17) for x in supplied.prefix), "malformed literal digit")
        require(supplied == correct, "literal digit position, selected letter or prefix mismatch")
    require(type(binding.states) is tuple
            and all(type(state) is tuple and len(state) == 5
                    and all(_integer(x) for x in state) for state in binding.states)
            and binding.states == expected.states,
            "complete canonical state inventory mismatch")
    require(type(binding.rows) is tuple and len(binding.rows) == len(expected.rows),
            "row inventory dimensions")
    for source, (submitted, correct) in enumerate(zip(binding.rows, expected.rows)):
        require(type(submitted) is tuple and len(submitted) <= ROW_CAP, "bounded immutable row required")
        for slot in submitted:
            require(type(slot) is Slot and _integer(slot.target, 0, len(binding.states)-1)
                    and _integer(slot.top, 0, 17) and _integer(slot.bottom, 0, 17)
                    and _integer(slot.swapped, 0, 1), "malformed literal occurrence slot")
        require(submitted == correct,
                "complete literal slot identity/orientation mismatch in row " + str(source))
    check_births(binding)
    return binding_summary(binding)


def binding_summary(binding):
    row_targets = [tuple(slot.target for slot in row) for row in binding.rows]
    return {
        "source": binding.source,
        "images": [list(word) for word in binding.images],
        "states": len(binding.states),
        "edges": sum(map(len, binding.rows)),
        "swapped": sum(slot.swapped for row in binding.rows for slot in row),
        "repeated_target_slots": sum(len(row)-len(set(row)) for row in row_targets),
        "nonroot_births": len(binding.states)-3,
        "ordered_states": 2*len(binding.states),
        "ordered_edges": 2*sum(map(len, binding.rows)),
        "maximum_discovery_depth": max(check_births(binding)),
    }


def source_lines(binding):
    source = binding.source
    summary = binding_summary(binding)
    yield f"source {source} {summary['states']} {summary['edges']}"
    for kind, words in (("image", binding.images), ("word", binding.words)):
        for letter, word in enumerate(words):
            yield " ".join(map(str, (kind, source, letter, len(word), *word)))
    for number, digit in enumerate(binding.digits):
        yield " ".join(map(str, ("digit", source, number, digit.selected, digit.parent,
                                   digit.position, *digit.prefix)))
    for number, state in enumerate(binding.states):
        yield " ".join(map(str, ("state", source, number, *state)))
    for row, slots in enumerate(binding.rows):
        for position, slot in enumerate(slots):
            yield " ".join(map(str, ("edge", source, row, position, slot.target,
                                       slot.top, slot.bottom, slot.swapped)))
    for state, (row, slot) in enumerate(binding.births):
        yield " ".join(map(str, ("birth", source, state, row, slot)))
    yield " ".join(map(str, ("summary", source, summary["states"], summary["edges"],
                               summary["swapped"], summary["repeated_target_slots"],
                               summary["nonroot_births"])))


def packet_lines():
    yield "schema " + SCHEMA
    summaries = []
    for source in range(SOURCE_COUNT):
        binding = reference(source)
        summaries.append(binding_summary(binding))
        yield from source_lines(binding)
    yield " ".join(map(str, ("total", SOURCE_COUNT,
                               *(sum(s[key] for s in summaries) for key in
                                 ("states", "edges", "swapped", "repeated_target_slots", "nonroot_births")))))


def _digest(lines):
    digest = hashlib.sha256()
    for line in lines:
        digest.update((line + "\n").encode("ascii"))
    return digest.hexdigest()


def receipt():
    summaries = [binding_summary(reference(index)) for index in range(SOURCE_COUNT)]
    return {
        "schema": SCHEMA,
        "canonical_language": "Mojo",
        "historical_graph_revision": HISTORICAL_REVISION,
        "source_count": SOURCE_COUNT,
        "digits_per_source": 18,
        "incidence": [list(row) for row in incidence(source_images(0))],
        "two_step_incidence": [list(row) for row in incidence(square_words(source_images(0)))],
        "two_step_determinant": 4,
        "total_states": sum(s["states"] for s in summaries),
        "total_edges": sum(s["edges"] for s in summaries),
        "total_ordered_states": sum(s["ordered_states"] for s in summaries),
        "total_ordered_edges": sum(s["ordered_edges"] for s in summaries),
        "total_swapped": sum(s["swapped"] for s in summaries),
        "total_repeated_target_slots": sum(s["repeated_target_slots"] for s in summaries),
        "total_nonroot_births": sum(s["nonroot_births"] for s in summaries),
        "sources": summaries,
        "normalized_packet_sha256": _digest(packet_lines()),
        "scope": "complete finite internal occurrence binding, ordered lift and discovery ancestry",
        "non_claims": ["compact inverse-piece coverage", "geometric pruning soundness",
                       "product-Haar scaling", "positive compact root measure", "general C4", "PSC"],
    }


def verify_native_lines(lines):
    """Compare every record; reject empty, truncated, duplicated or added data."""
    count = 0
    for count, (actual, expected) in enumerate(zip_longest(lines, packet_lines()), 1):
        require(actual is not None and expected is not None,
                "complete native packet record count mismatch at " + str(count))
        require(type(actual) is str and actual.strip().split() == expected.split(),
                "native packet mismatch at record " + str(count))
    require(count > 1, "empty native packet")
    result = receipt()
    result["record_count"] = count
    return result


def verify_native(packet):
    require(type(packet) is str, "native packet must be text")
    return verify_native_lines(io.StringIO(packet))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", type=Path, help="authenticate complete canonical native stdout")
    parser.add_argument("--packet", action="store_true", help="print oracle calibration, not native evidence")
    parser.add_argument("--output", type=Path, help="write the observed receipt as JSON")
    args = parser.parse_args()
    require(not (args.native and args.packet), "select native verification or oracle calibration")
    if args.packet:
        for line in packet_lines():
            print(line)
        return
    if args.native:
        with args.native.open(encoding="ascii") as stream:
            result = verify_native_lines(stream)
        result["native_file_sha256"] = hashlib.sha256(args.native.read_bytes()).hexdigest()
    else:
        result = receipt()
    encoded = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
