#!/usr/bin/env python3
"""Independent integer audit of complete finite prefix-window certificates.

Canonical construction is kernel/psc/c4_prefix_closure.mojo.  This oracle
expands literal words, counts literal slices, and locates each output position
by inverse search among full parent boundaries.  It does not share the
native parent/local enumeration or streaming Parikh recurrence.  Only the
existing independent Cramer residue and physical forward-leak controls are
reused.  Complete packet comparison remains active under python -O.

Productive prolongation premises can instantiate the separate Lean limit
construction.  A bounded packet does not authenticate an arbitrary infinite
word, compact prefix tiles, forward completeness, or compact overlap measure.
"""

from __future__ import annotations

import argparse
from bisect import bisect_right
from collections import Counter
from dataclasses import dataclass, fields, is_dataclass
from functools import lru_cache
import hashlib
from itertools import zip_longest
import json
from pathlib import Path
import subprocess

from c4_madic_residue import class_key, forward_leak


SCHEMA = "c4-prefix-closure-v1"
LIMITS = (3, 3, 3, 32, 4096, 12288)
ROOT = Path(__file__).resolve().parents[2]
SOURCES = (
    ".github/workflows/c4-prefix-closure.yml",
    "kernel/psc/c4_prefix_closure.mojo",
    "kernel/c4_prefix_closure.mojo",
    "kernel/tests/test_c4_prefix_closure.mojo",
    "oracles/python/c4_prefix_closure.py",
    "tests/test_c4_prefix_closure_oracle.py",
    "oracles/python/c4_madic_residue.py",
    "kernel/psc/c4_madic_residue.mojo",
    "kernel/psc/c4_nonunit_residue_occupancy.mojo",
    "kernel/psc/c4_bounded_cover.mojo",
    "kernel/psc/c4_literal_inverse_binding.mojo",
    "kernel/psc/c4_pair_overlap_new_incidence.mojo",
    "kernel/psc/c4_pair_overlap_carrier.mojo",
    "kernel/psc/c4_finite_cylinder_overlap.mojo",
    "kernel/psc/c4_cylinder_density.mojo",
    "kernel/psc/affine_ancestry_trace.mojo",
    "kernel/psc/renewal.mojo", "kernel/psc/renewal_address.mojo",
    "kernel/psc/bpa.mojo", "kernel/psc/derived_system.mojo",
    "kernel/psc/words.mojo", "kernel/psc/exact.mojo", "kernel/psc/pisot.mojo",
    "proof/PscVerif/PscVerif/PrefixAddress.lean",
    "proof/PscVerif/PscVerif/PrefixClosure.lean",
    "proof/PscVerif/PscVerif/FixedPointLimit.lean",
    "proof/PscVerif/PscVerif/PrimitiveExpansion.lean",
    "proof/PscVerif/PscVerif/OccurrenceAddress.lean",
    "proof/PscVerif/PscVerif/OccurrenceTransport.lean",
    "proof/PscVerif/PscVerif/OccurrenceFinite.lean",
    "proof/PscVerif/PscVerif/OccurrenceInverse.lean",
    "proof/PscVerif/PscVerif/OccurrencePiece.lean",
    "proof/PscVerif/PscVerif/OccurrenceCover.lean",
    "proof/PscVerif/PscVerif/OccurrenceAdmissibility.lean",
    "proof/PscVerif/PscVerif/OccurrenceResidue.lean",
    "proof/PscVerif/PscVerif/MadicResidue.lean",
    "docs/c4-prefix-closure-2026-11-11.md",
    "docs/c4-prefix-closure-literature-2026-11-11.md",
    "kernel/pixi.toml", "kernel/pixi.lock", "vendored.toml",
)


class InvalidCertificate(ValueError):
    """An incomplete, unsupported, altered, or noncanonical certificate."""


def require(condition, message):
    if not condition:
        raise InvalidCertificate(message)


def integer(value):
    return type(value) is int


def word(value, *, nonempty=False, cap=4096):
    require(type(value) in (list, tuple), "word container")
    require((not nonempty or len(value) > 0) and len(value) <= cap, "word length")
    require(all(integer(letter) and 0 <= letter < 3 for letter in value), "word letter")
    return tuple(value)


def parikh(value):
    counts = Counter(value)
    return tuple(counts[letter] for letter in range(3))


def expand(images, value):
    return tuple(letter for parent in value for letter in images[parent])


def incidence(images):
    return tuple(tuple(image.count(letter) for image in images) for letter in range(3))


def flatten(matrix):
    return tuple(value for row in matrix for value in row)


def rows(matrix):
    return tuple(matrix[i:i + 3] for i in range(0, 9, 3))


def multiply(matrix, vector):
    return tuple(sum(a * b for a, b in zip(row, vector)) for row in matrix)


def matrix_power(matrix, exponent):
    result = tuple(tuple(int(i == j) for j in range(3)) for i in range(3))
    for _ in range(exponent):
        result = tuple(tuple(sum(result[i][k] * matrix[k][j] for k in range(3))
                             for j in range(3)) for i in range(3))
    return result


@dataclass(frozen=True)
class Transition:
    generation: int
    cuts: tuple[tuple[int, ...], ...]
    occurrences: tuple[tuple[int, ...], ...]


@dataclass(frozen=True)
class Certificate:
    images: tuple[tuple[int, ...], ...]
    period: int
    generations: int
    seed: tuple[int, ...]
    word_cap: int
    occurrence_cap: int
    matrix: tuple[int, ...]
    block_images: tuple[tuple[int, ...], ...]
    block_matrix: tuple[int, ...]
    marks: tuple[tuple[int, ...], ...]
    mark_before: tuple[tuple[int, ...], ...]
    mark_after: tuple[tuple[int, ...], ...]
    windows: tuple[tuple[int, ...], ...]
    transitions: tuple[Transition, ...]


def construct(images, period, seed, generations, *, word_cap=4096, occurrence_cap=12288):
    require(integer(period) and 1 <= period <= 3, "block period outside bounded range")
    require(integer(generations) and 1 <= generations <= 3, "transition count outside bounded range")
    require(integer(word_cap) and 1 <= word_cap <= 4096, "window budget outside bounded range")
    require(integer(occurrence_cap) and 1 <= occurrence_cap <= 12288,
            "occurrence budget outside bounded range")
    require(type(images) in (tuple, list) and len(images) == 3, "three substitution images required")
    images = tuple(word(image, nonempty=True, cap=3) for image in images)
    seed = word(seed, nonempty=True, cap=min(32, word_cap))
    block_images = tuple((letter,) for letter in range(3))
    for _ in range(period):
        block_images = tuple(expand(images, image) for image in block_images)
    matrix = incidence(images)
    block_matrix = incidence(block_images)
    require(block_matrix == matrix_power(matrix, period), "literal block incidence disagrees with M^k")
    first_length = sum(len(block_images[parent]) for parent in seed)
    require(first_length <= word_cap, "complete output window exceeds budget")
    first = expand(block_images, seed)
    require(first[:len(seed)] == seed and first_length > len(seed),
            "seed is not a strictly growing prolonging prefix")
    marks, mark_before, mark_after = [], [], []
    offsets = tuple(sum(map(len, block_images[:parent])) for parent in range(3))
    for parent, image in enumerate(block_images):
        for local, selected in enumerate(image):
            before, after = image[:local], image[local + 1:]
            marks.append((parent, local, selected, *parikh(before), *parikh(after)))
            mark_before.append(before)
            mark_after.append(after)
    windows, transitions = [seed], []
    total = 0
    for generation in range(generations):
        source = windows[-1]
        target_length = sum(len(block_images[parent]) for parent in source)
        require(target_length <= word_cap, "complete output window exceeds budget")
        require(total + target_length <= occurrence_cap, "complete occurrence inventory exceeds budget")
        target = expand(block_images, source)
        require(len(target) == target_length and target[:len(source)] == source
                and len(target) > len(source), "productive prefix chain invariant")
        # Literal re-expansion and slice counting, independently of the native
        # streaming recurrence and parent/local forward enumeration.
        expanded_prefixes = tuple(expand(block_images, source[:parent])
                                  for parent in range(len(source) + 1))
        boundaries = tuple(map(len, expanded_prefixes))
        cuts = tuple((parent, boundary, *parikh(source[:parent]),
                      *parikh(expanded_prefixes[parent]))
                     for parent, boundary in enumerate(boundaries))
        addresses = []
        for global_position, selected in enumerate(target):
            parent_position = bisect_right(boundaries, global_position) - 1
            parent = source[parent_position]
            local = global_position - boundaries[parent_position]
            image = block_images[parent]
            before, after = image[:local], image[local + 1:]
            source_prefix = parikh(source[:parent_position])
            transport = multiply(block_matrix, source_prefix)
            require(transport == parikh(expanded_prefixes[parent_position]), "source-prefix transport")
            require(selected == image[local], "selected letter differs from local full Mark")
            require(target[:global_position] == expanded_prefixes[parent_position] + before,
                    "literal prefix identity")
            require(target[global_position + 1:] == after + expand(block_images, source[parent_position + 1:]),
                    "literal suffix identity")
            addresses.append((parent_position, parent, offsets[parent] + local,
                              local, global_position, selected, *source_prefix,
                              *transport, *parikh(before), *parikh(target[:global_position])))
        require(boundaries[-1] == len(target) and len(addresses) == len(target), "full window coverage")
        transitions.append(Transition(generation, cuts, tuple(addresses)))
        windows.append(target)
        total += len(target)
    return Certificate(images, period, generations, seed, word_cap, occurrence_cap,
                       flatten(matrix), block_images, flatten(block_matrix), tuple(marks),
                       tuple(mark_before), tuple(mark_after), tuple(windows), tuple(transitions))


def same_typed(actual, expected):
    # A boolean or floating value must not authenticate an integer field.
    if type(actual) is not type(expected):
        return False
    if is_dataclass(expected):
        return all(same_typed(getattr(actual, field.name), getattr(expected, field.name))
                   for field in fields(expected))
    if isinstance(expected, tuple):
        return len(actual) == len(expected) and all(same_typed(a, e) for a, e in zip(actual, expected))
    return actual == expected


def validate_certificate(value):
    require(type(value) is Certificate, "certificate type")
    expected = construct(value.images, value.period, value.seed, value.generations,
                         word_cap=value.word_cap, occurrence_cap=value.occurrence_cap)
    require(same_typed(value, expected), "complete prefix, full Mark or address inventory changed")


def bind_windows(images, period, seed, windows, *, word_cap=4096, occurrence_cap=12288):
    require(type(windows) in (tuple, list) and 2 <= len(windows) <= 4, "supplied window count")
    require(integer(word_cap) and 1 <= word_cap <= 4096, "window budget outside bounded range")
    supplied = tuple(word(window, cap=word_cap) for window in windows)
    expected = construct(images, period, seed, len(supplied) - 1,
                         word_cap=word_cap, occurrence_cap=occurrence_cap)
    require(supplied == expected.windows, "supplied windows are not the full consecutive expansion")
    return expected


def lookup(certificate, generation, global_position):
    """Lookup on a constructed or separately validated certificate."""
    require(integer(generation) and 0 <= generation < len(certificate.transitions), "lookup transition")
    require(integer(global_position) and 0 <= global_position < len(certificate.windows[generation + 1]),
            "lookup is not an actual output occurrence")
    transition = certificate.transitions[generation]
    require(len(transition.occurrences) == len(certificate.windows[generation + 1]), "lookup full inventory")
    result = transition.occurrences[global_position]
    require(len(result) == 18 and result[4] == global_position, "lookup occurrence identity")
    return result


def summary(certificate, generation):
    source, target = certificate.windows[generation:generation + 2]
    transition = certificate.transitions[generation]
    return (len(source), len(target), len(transition.cuts), len(transition.occurrences),
            *parikh(source), *parikh(target))


FIXTURES = (
    (((1,), (0, 2, 1), (0, 0, 1)), 2),
    (((1,), (0, 1, 2), (0, 0, 1)), 2),
    (((0, 1), (0, 2), (0,)), 1),
    (((0, 0), (1, 1), (2, 2)), 1),
)


@lru_cache(maxsize=4)
def reference(fixture):
    require(integer(fixture) and 0 <= fixture < 4, "unknown prefix fixture")
    images, period = FIXTURES[fixture]
    return construct(images, period, (0,), 3)


def same_residue_control():
    named = reference(0)
    first, second = lookup(named, 2, 0), lookup(named, 2, 29)
    lattice = rows(named.block_matrix)
    # Independent Cramer column replacements establish membership in M^2 Z^3.
    # Class zero is the exact quotient's zero representative, not an arbitrary
    # cyclic surrogate or coordinate-wise modular reduction.
    require(class_key(lattice, first[15:18]) == class_key(lattice, second[15:18]) == (0, 0, 0),
            "named literal prefixes are not both in the zero lattice class")
    require(first[0] != second[0] and first[4] != second[4] and first[2] == second[2],
            "distinct-address same-residue control disappeared")
    return (0, 2, 2, first[4], second[4], first[0], second[0], first[3], second[3], 0)


def refusal(control):
    require(integer(control) and 0 <= control < 14, "unknown prefix refusal control")
    named = FIXTURES[0][0]
    actions = (
        lambda: construct(((), (), ()), 1, (0,), 1),
        lambda: construct(((0, 0), (), (2,)), 1, (0,), 1),
        lambda: construct(((0,), (1,), (2,)), 1, (0,), 1),
        lambda: construct(((1,), (0,), (2,)), 2, (0,), 1),
        lambda: construct(named, 1, (0,), 1),
        lambda: construct(named, 2, (), 1),
        lambda: bind_windows(named, 2, (0,), ((0,), (0,))),
        lambda: bind_windows(named, 2, (0,), ((0,), (0, 2, 1, 0))),
        lambda: lookup(reference(0), 0, 3),
        lambda: construct(named, 2, (0,), 3, word_cap=78),
        lambda: construct(named, 2, (0,), 3, occurrence_cap=96),
        lambda: construct(named, 4, (0,), 1),
        lambda: construct(named, 2, (0,), 4),
        lambda: bind_windows(named, 2, (0,), ((0,), (0, 1, 2))),
    )
    try:
        actions[control]()
    except InvalidCertificate:
        return
    raise InvalidCertificate("negative construction unexpectedly succeeded")


def record(kind, *values):
    return " ".join(map(str, (kind, *values)))


def certificate_lines(fixture, certificate):
    lines = [record("fixture", fixture, certificate.period, certificate.generations,
                    certificate.word_cap, certificate.occurrence_cap)]
    lines.extend(record("image", fixture, source, len(image), *image)
                 for source, image in enumerate(certificate.images))
    lines.append(record("incidence", fixture, *certificate.matrix))
    lines.extend(record("block_image", fixture, source, len(image), *image)
                 for source, image in enumerate(certificate.block_images))
    lines.append(record("block_incidence", fixture, *certificate.block_matrix))
    lines.append(record("seed", fixture, len(certificate.seed), *certificate.seed))
    for identity, mark in enumerate(certificate.marks):
        before, after = certificate.mark_before[identity], certificate.mark_after[identity]
        lines.extend((record("mark", fixture, identity, *mark),
                      record("mark_before", fixture, identity, len(before), *before),
                      record("mark_after", fixture, identity, len(after), *after)))
    lines.extend(record("window", fixture, generation, certificate.period * generation, len(value), *value)
                 for generation, value in enumerate(certificate.windows))
    for generation, transition in enumerate(certificate.transitions):
        lines.extend(record("cut", fixture, generation, *cut) for cut in transition.cuts)
        lines.extend(record("address", fixture, generation, identity, *address)
                     for identity, address in enumerate(transition.occurrences))
        lines.append(record("summary", fixture, generation, *summary(certificate, generation)))
    return lines


def expected_packet():
    lines = [record("schema", SCHEMA), record("limits", *LIMITS)]
    for fixture in range(4):
        lines.extend(certificate_lines(fixture, reference(fixture)))
    lines.append(record("control same_residue", *same_residue_control()))
    named = reference(0)
    source_length = len(named.windows[0])
    lines.append(record("control truncated_successor", 0, 0, source_length, len(named.windows[1]),
                        *lookup(named, 0, source_length)))
    lines.append(record("control terminal_cut", 0, 0, *named.transitions[0].cuts[source_length]))
    lines.append(record("control finite_letter_support", 3, 3, *parikh(reference(3).windows[3])))
    for control in range(14):
        refusal(control)
        lines.append(record("refusal", control, 1))
    lines.append(record("control forward_leak", *forward_leak()))
    certificates = tuple(reference(fixture) for fixture in range(4))
    lines.append(record("total", 4, sum(len(c.windows) for c in certificates),
                        sum(len(c.transitions) for c in certificates),
                        sum(len(c.marks) for c in certificates),
                        sum(len(t.occurrences) for c in certificates for t in c.transitions)))
    return "\n".join(lines) + "\n"


def validate_native(text):
    require(type(text) is str and text.endswith("\n"), "packet must end with newline")
    expected = expected_packet()
    require(text == expected, next(
        (f"complete inventory differs at line {index + 1}: expected {want!r}, got {actual!r}"
         for index, (want, actual) in enumerate(zip_longest(expected.splitlines(), text.splitlines()))
         if want != actual), "noncanonical spacing or final newline"))
    return {
        "schema": SCHEMA,
        "scope": "complete bounded prefix windows and literal addresses; productive seed premises for a separate Lean limit",
        "limits": list(LIMITS),
        "fixtures": [{"fixture": fixture, "period": reference(fixture).period,
                      "summaries": [list(summary(reference(fixture), generation)) for generation in range(3)]}
                     for fixture in range(4)],
        "same_residue_distinct_addresses": list(same_residue_control()),
        "physical_forward_leak": list(forward_leak()),
        "negative_construction_controls": 14,
        "native_sha256": hashlib.sha256(text.encode()).hexdigest(),
        "bytes": len(text.encode()), "lines": len(text.splitlines()),
        "no_governed_claim_promoted": True,
    }


def receipt_source():
    return {
        "git_head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "git_tree": subprocess.check_output(["git", "rev-parse", "HEAD^{tree}"], cwd=ROOT, text=True).strip(),
        "worktree_dirty": bool(subprocess.check_output(["git", "status", "--porcelain"],
                                                       cwd=ROOT, text=True).strip()),
        "sources": {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in SOURCES},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-output", "--native", dest="native_output", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    # Preserve newlines exactly: newline normalization must not authenticate
    # a differently serialized packet.
    result = validate_native(args.native_output.read_bytes().decode("utf-8"))
    result.update(receipt_source())
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
