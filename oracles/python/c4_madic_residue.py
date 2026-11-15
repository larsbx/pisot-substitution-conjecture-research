#!/usr/bin/env python3
"""Independent integer audit of complete bounded matrix-adic residue packets.

Canonical construction is kernel/psc/c4_madic_residue.mojo.  This oracle uses
arbitrary-precision integers, permutation determinants, column-replacement
Cramer numerators, literal word slicing, and Counter/frozenset profiles.  It
neither imports native output as reference data nor shares its adjugate or
streaming-prefix implementation.  Every packet line is reconstructed, and
all rejection checks remain active under python -O.

Finite support sets become compact-set enclosures only through the supplied
literal block tile equation in Lean.  Intersecting profiles certify no actual
overlap, and no physical interval calibration is a compact overlap measure.
"""

from __future__ import annotations

import argparse
from collections import Counter, deque
from dataclasses import dataclass, fields, is_dataclass
from functools import lru_cache
import hashlib
from itertools import combinations, permutations, zip_longest
import json
from math import gcd, prod
from pathlib import Path
import subprocess


SCHEMA = "c4-madic-residue-v1"
LIMITS = (6, 64, 192, 729, 2187)
ROOT = Path(__file__).resolve().parents[2]
SOURCES = (
    ".github/workflows/c4-madic-residue.yml",
    "kernel/psc/c4_madic_residue.mojo",
    "kernel/c4_madic_residue.mojo",
    "kernel/tests/test_c4_madic_residue.mojo",
    "oracles/python/c4_madic_residue.py",
    "tests/test_c4_madic_residue_oracle.py",
    "kernel/psc/c4_nonunit_residue_occupancy.mojo",
    "kernel/psc/c4_bounded_cover.mojo",
    "kernel/psc/c4_literal_inverse_binding.mojo",
    "kernel/psc/affine_ancestry_trace.mojo",
    "proof/PscVerif/PscVerif/MadicResidue.lean",
    "proof/PscVerif/PscVerif/OccurrenceResidue.lean",
    "proof/PscVerif/PscVerif/OccurrenceAdmissibility.lean",
    "proof/PscVerif/PscVerif/OccurrenceCover.lean",
    "proof/PscVerif/PscVerif/OccurrencePiece.lean",
    "docs/c4-madic-residue-2026-11-11.md",
    "docs/c4-madic-residue-literature-2026-11-11.md",
    "kernel/pixi.toml", "kernel/pixi.lock", "vendored.toml",
)


class InvalidCertificate(ValueError):
    """An incomplete, changed, unsupported, or noncanonical certificate."""


def require(condition, message):
    if not condition:
        raise InvalidCertificate(message)


def integer(value):
    return type(value) is int


def determinant(matrix):
    """Leibniz sum; independent of the native adjugate and Q elimination."""
    n = len(matrix)
    require(n > 0 and all(len(row) == n for row in matrix), "determinant shape")
    result = 0
    for permutation in permutations(range(n)):
        inversions = sum(permutation[i] > permutation[j]
                         for i in range(n) for j in range(i + 1, n))
        result += (-1 if inversions % 2 else 1) * prod(
            matrix[row][permutation[row]] for row in range(n))
    return result


IDENTITY = tuple(tuple(int(i == j) for j in range(3)) for i in range(3))
ZERO = (0, 0, 0)
UNITS = tuple(tuple(int(i == j) for i in range(3)) for j in range(3))


def mm(first, second):
    return tuple(tuple(sum(first[i][k] * second[k][j] for k in range(3))
                       for j in range(3)) for i in range(3))


def mv(matrix, vector):
    return tuple(sum(a * b for a, b in zip(row, vector)) for row in matrix)


def power(matrix, exponent):
    result = IDENTITY
    for _ in range(exponent):
        result = mm(result, matrix)
    return result


def cramer_numerators(matrix, vector):
    require(len(vector) == 3 and all(integer(x) for x in vector), "integer vector shape")
    return tuple(determinant(tuple(tuple(vector[i] if j == column else matrix[i][j]
                                        for j in range(3)) for i in range(3)))
                 for column in range(3))


def class_key(matrix, vector):
    index = abs(determinant(matrix))
    require(index > 0, "singular quotient has no finite class key")
    return tuple(numerator % index for numerator in cramer_numerators(matrix, vector))


def inverse_integer(matrix, vector):
    det = determinant(matrix)
    require(det != 0, "singular integer inverse")
    numerators = cramer_numerators(matrix, vector)
    return tuple(n // det for n in numerators) if all(n % det == 0 for n in numerators) else None


def smith_factors(matrix):
    """All determinantal divisors, using independent small permutation sums."""
    divisors = [1]
    for size in range(1, 4):
        value = 0
        for rows in combinations(range(3), size):
            for columns in combinations(range(3), size):
                value = gcd(value, determinant(tuple(tuple(matrix[i][j] for j in columns)
                                                     for i in rows)))
        divisors.append(value)
    require(all(divisors), "singular Smith factors")
    require(all(divisors[i] % divisors[i - 1] == 0 for i in range(1, 4)),
            "determinantal divisors do not divide")
    factors = tuple(divisors[i] // divisors[i - 1] for i in range(1, 4))
    require(prod(factors) == abs(determinant(matrix)), "Smith index identity")
    return factors


def incidence(words):
    return tuple(tuple(words[parent].count(selected) for parent in range(3))
                 for selected in range(3))


def parikh(word):
    return tuple(word.count(letter) for letter in range(3))


@dataclass(frozen=True)
class Level:
    depth: int
    matrix: tuple
    determinant: int
    index: int
    candidates: int
    smith: tuple
    representatives: tuple
    addition: tuple
    generators: tuple
    inverse: tuple
    orders: tuple
    action: tuple
    reduction: tuple
    words: tuple
    occurrences: tuple
    counts: tuple
    profiles: tuple

    def summary(self):
        occupied = sum(row[source + 2] > 0 for row in self.counts for source in range(3))
        return (self.index, self.candidates, len(self.occurrences), sum(map(len, self.profiles)),
                self.action.count(0), len(set(self.action)), len(self.occurrences) - occupied)


@dataclass(frozen=True)
class Certificate:
    images: tuple
    depth: int
    matrix: tuple
    determinant: int
    index_cap: int
    candidate_cap: int
    word_cap: int
    occurrence_cap: int
    levels: tuple


def class_of(level, vector):
    key = class_key(level.matrix, vector)
    matches = [i for i, row in enumerate(level.representatives) if row[3:6] == key]
    require(len(matches) == 1, "class absent or repeated in complete quotient")
    return matches[0]


def quotient(matrix, q, words, previous, index_cap, candidate_cap, occurrence_cap):
    lattice = power(matrix, q)
    det = determinant(lattice)
    index = abs(det)
    require(1 <= index <= index_cap, "complete quotient index budget")
    representatives = [(0, 0, 0, 0, 0, 0, -1, -1)]
    identities = {ZERO: 0}
    pending = deque((0,))
    candidates = 0
    while pending:
        parent = pending.popleft()
        for axis, unit in enumerate(UNITS):
            require(candidates < candidate_cap, "complete basis-extension candidate budget")
            candidates += 1
            vector = tuple(x + y for x, y in zip(representatives[parent][:3], unit))
            key = class_key(lattice, vector)
            if key not in identities:
                require(len(representatives) < index and len(representatives) < index_cap,
                        "quotient traversal exceeds exact index")
                identity = len(representatives)
                identities[key] = identity
                pending.append(identity)
                representatives.append((*vector, *key, parent, axis))
    require(len(identities) == len(representatives) == index and candidates == 3 * index,
            "quotient enumeration is incomplete")
    vectors = tuple(row[:3] for row in representatives)

    def identify(vector):
        key = class_key(lattice, vector)
        require(key in identities, "quotient operation escapes complete inventory")
        return identities[key]

    addition = tuple(tuple(identify(tuple(x + y for x, y in zip(a, b)))
                           for b in vectors) for a in vectors)
    inverse = tuple(identify(tuple(-x for x in vector)) for vector in vectors)
    action = tuple(identify(mv(matrix, vector)) for vector in vectors)
    reduction = tuple(class_of(previous, vector) if previous else 0 for vector in vectors)
    orders = []
    for identity in range(index):
        value = 0
        for order in range(1, index + 1):
            value = addition[value][identity]
            if value == 0:
                orders.append(order)
                break
        else:
            raise InvalidCertificate("quotient element lacks finite order")
        require(addition[identity][inverse[identity]] == 0, "inverse identity")
        value = identity
        for _ in range(q):
            value = action[value]
        require(value == 0, "q-th incidence action is not zero")
        for other in range(index):
            require(addition[identity][other] == addition[other][identity], "quotient commutativity")
            require(action[addition[identity][other]] == addition[action[identity]][action[other]],
                    "induced action is not additive")
            if previous:
                require(reduction[addition[identity][other]] ==
                        previous.addition[reduction[identity]][reduction[other]],
                        "reduction is not additive")
        if previous:
            require(reduction[action[identity]] == previous.action[reduction[identity]],
                    "reduction/action commutation")
    if previous:
        require(set(reduction) == set(range(previous.index)) and
                set(Counter(reduction).values()) == {abs(determinant(matrix))},
                "reduction fibers are incomplete")
    occurrences = []
    for source, word in enumerate(words):
        require(parikh(word) == tuple(lattice[a][source] for a in range(3)),
                "literal word disagrees with incidence power")
        for position, selected in enumerate(word):
            require(len(occurrences) < occurrence_cap, "complete occurrence budget")
            # Slice the literal word afresh; no native running-prefix recurrence.
            prefix, suffix = parikh(word[:position]), parikh(word[position + 1:])
            occurrences.append((source, position, selected, *prefix, *suffix, identify(prefix)))
    buckets = Counter((row[2], row[9], row[0]) for row in occurrences)
    counts = tuple((letter, identity, *(buckets[letter, identity, source] for source in range(3)))
                   for letter in range(3) for identity in range(index))
    supports = tuple(frozenset(row[9] for row in occurrences if row[2] == letter)
                     for letter in range(3))
    return Level(q, lattice, det, index, candidates, smith_factors(lattice),
                 tuple(representatives), addition, tuple(map(identify, UNITS)), inverse,
                 tuple(orders), action, reduction, words, tuple(occurrences), counts,
                 tuple(tuple(sorted(support)) for support in supports))


def construct(images, depth, *, index_cap=64, candidate_cap=192, word_cap=729, occurrence_cap=2187):
    require(isinstance(images, (tuple, list)) and len(images) == 3 and
            all(isinstance(word, (tuple, list)) and 1 <= len(word) <= 3 and
                all(integer(letter) and 0 <= letter < 3 for letter in word) for word in images),
            "literal images outside three-letter length1..3 domain")
    require(integer(depth) and 0 <= depth <= LIMITS[0], "matrix-adic depth budget")
    for value, bound, name in zip((index_cap, candidate_cap, word_cap, occurrence_cap),
                                  LIMITS[1:], ("index", "candidate", "word", "occurrence")):
        require(integer(value) and 1 <= value <= bound, f"invalid {name} budget")
    images = tuple(tuple(word) for word in images)
    matrix = incidence(images)
    det = determinant(matrix)
    require(det != 0, "singular incidence: finite constructor refuses")
    words = ((0,), (1,), (2,))
    levels = []
    for q in range(depth + 1):
        require(abs(det) ** q <= index_cap, "complete quotient index budget")
        levels.append(quotient(matrix, q, words, levels[-1] if levels else None,
                               index_cap, candidate_cap, occurrence_cap))
        if q < depth:
            require(all(sum(len(images[a]) for a in word) <= word_cap for word in words),
                    "complete block word budget")
            words = tuple(tuple(x for a in word for x in images[a]) for word in words)
    return Certificate(images, depth, matrix, det, index_cap, candidate_cap, word_cap,
                       occurrence_cap, tuple(levels))


def validate_certificate(value):
    require(type(value) is Certificate, "certificate type")
    expected = construct(value.images, value.depth, index_cap=value.index_cap,
                         candidate_cap=value.candidate_cap, word_cap=value.word_cap,
                         occurrence_cap=value.occurrence_cap)
    require(_same_typed(value, expected), "complete quotient or literal occurrence inventory changed")


def _same_typed(actual, expected):
    # Python bool/float equality must not authenticate an integer certificate.
    if type(actual) is not type(expected):
        return False
    if is_dataclass(expected):
        return all(_same_typed(getattr(actual, field.name), getattr(expected, field.name))
                   for field in fields(expected))
    if isinstance(expected, tuple):
        return len(actual) == len(expected) and all(_same_typed(a, e) for a, e in zip(actual, expected))
    return actual == expected


FIXTURES = (
    (((1,), (0, 2, 1), (0, 0, 1)), 4),
    (((1,), (0, 1, 2), (0, 0, 1)), 4),
    (((0, 1), (0, 2), (0,)), 3),
    (((0, 0), (1, 1), (2, 2)), 2),
)


@lru_cache(maxsize=4)
def reference(fixture):
    require(integer(fixture) and 0 <= fixture < len(FIXTURES), "unknown fixture")
    return construct(*FIXTURES[fixture])


def profile_intersection(level, first, second, shift):
    require(integer(first) and integer(second) and 0 <= first < 3 and 0 <= second < 3,
            "profile query letter")
    delta = class_of(level, shift)
    return tuple(sorted(set(level.profiles[first]) &
                        {level.addition[delta][x] for x in level.profiles[second]}))


def refusal(control):
    require(integer(control) and 0 <= control < 8, "unknown refusal control")
    words, depth, kwargs = FIXTURES[0][0], 2, {}
    if control < 2:
        words, depth = ((0,), (0,), (0,)), control
    elif control == 2:
        words, depth = FIXTURES[3][0], 3
    elif control == 3:
        kwargs = {"candidate_cap": 11}
    elif control == 4:
        kwargs = {"word_cap": 2}
    elif control == 5:
        kwargs = {"occurrence_cap": 14}
    elif control == 6:
        depth = 7
    else:
        depth, kwargs = 6, {"index_cap": 63}
    try:
        construct(words, depth, **kwargs)
    except InvalidCertificate:
        return
    raise InvalidCertificate("negative construction unexpectedly succeeded")


def forward_leak():
    """Independent replay of the unchanged physical 00/11/22 calibration."""
    words = FIXTURES[3][0]
    matrix = incidence(words)
    domain = {(0, 1, 0, 0, 0), (1, 0, 0, 0, 0)}
    full = retained = exits = 0
    for source in sorted(domain):
        for top in range(len(words[source[0]])):
            for bottom in range(len(words[source[1]])):
                p, r = parikh(words[source[0]][:top]), parikh(words[source[1]][:bottom])
                lift = inverse_integer(matrix, tuple(b - a for a, b in zip(p, r)))
                require((lift is not None) == (top == bottom == 0), "inverse closure parity")
                if lift is not None:
                    require((source[0], source[1], *lift) in domain, "integral ancestor outside domain")
                delta = tuple(a - b for a, b in zip(p, r))
                target = (source[0], source[1], *delta)
                offset = sum(delta)
                physical_length = max(0, min(1, 1 - offset) - max(0, -offset))
                full += physical_length
                retained += physical_length if target in domain else 0
                exits += int(physical_length > 0 and target not in domain)
    require((full, retained, exits) == (4, 2, 2), "mandatory positive forward leak changed")
    return full, retained, exits


def record(kind, *values):
    return " ".join(map(str, (kind, *values)))


def flatten(matrix):
    return tuple(value for row in matrix for value in row)


def level_lines(fixture, level):
    q = level.depth
    # The adjugate columns are reconstructed from Cramer numerators of e_j.
    columns = tuple(cramer_numerators(level.matrix, unit) for unit in UNITS)
    adjugate = tuple(columns[j][i] for i in range(3) for j in range(3))
    lines = [record("level", fixture, q, level.determinant, level.index, level.candidates),
             record("power", fixture, q, *flatten(level.matrix)),
             record("adjugate", fixture, q, *adjugate),
             record("smith", fixture, q, *level.smith)]
    for kind, rows in (("representative", level.representatives), ("add", level.addition)):
        lines.extend(record(kind, fixture, q, i, *row) for i, row in enumerate(rows))
    for kind, values in (("generators", level.generators), ("inverse", level.inverse),
                         ("orders", level.orders), ("action", level.action), ("reduce", level.reduction)):
        lines.append(record(kind, fixture, q, *values))
    lines.extend(record("word", fixture, q, source, len(word), *word)
                 for source, word in enumerate(level.words))
    lines.extend(record("occurrence", fixture, q, i, *row) for i, row in enumerate(level.occurrences))
    lines.extend(record("count", fixture, q, *row) for row in level.counts)
    lines.extend(record("profile", fixture, q, a, len(profile), *profile)
                 for a, profile in enumerate(level.profiles))
    lines.append(record("summary", fixture, q, *level.summary()))
    return lines


@lru_cache(maxsize=1)
def expected_packet():
    """Independent expected text, for comparison and adversarial tests only."""
    lines = [record("schema", SCHEMA), record("limits", *LIMITS)]
    levels = []
    for fixture in range(4):
        value = reference(fixture)
        lines.append(record("fixture", fixture, value.depth, value.determinant,
                            value.index_cap, value.candidate_cap, value.word_cap, value.occurrence_cap))
        lines.extend(record("image", fixture, source, len(word), *word)
                     for source, word in enumerate(value.images))
        lines.append(record("incidence", fixture, *flatten(value.matrix)))
        for level in value.levels:
            lines.extend(level_lines(fixture, level))
            levels.append(level)
    named = reference(0)
    second = named.levels[2]
    require(second.smith == (1, 2, 2) and second.orders == (1, 2, 2, 2), "noncyclic named quotient")
    lines.append(record("control noncyclic", 0, 2, *second.orders))
    collision = next((i for i in range(1, second.index) if second.action[i] == 0), None)
    require(collision is not None, "finite incidence action collision disappeared")
    lines.append(record("control action_collision", 0, 2, 0, collision, 0))
    for shift in (ZERO, UNITS[0]):
        overlap = profile_intersection(second, 2, 2, shift)
        lines.append(record("profile_query", 0, 2, 2, 2, *shift, len(overlap), *overlap))
    for shift in (UNITS[0], (-1, 0, 0)):
        overlap = profile_intersection(named.levels[3], 0, 0, shift)
        lines.append(record("profile_query", 0, 3, 0, 0, *shift, len(overlap), *overlap))
    transposed = tuple(zip(*named.matrix))
    for axis in range(3):
        vector = tuple(named.levels[4].matrix[row][axis] for row in range(3))
        if inverse_integer(power(transposed, 4), vector) is None:
            require(inverse_integer(named.levels[4].matrix, vector) is not None, "actual column not in lattice")
            lines.append(record("control column_lattice", 0, 4, axis, *vector))
            break
    else:
        raise InvalidCertificate("row/column lattice countercontrol disappeared")
    doubled = reference(3)
    lower, upper = (class_of(doubled.levels[q], (2, 0, 0)) for q in (1, 2))
    require(lower == 0 and upper != 0, "truncated residue alias disappeared")
    lines.append(record("control finite_alias", 3, 1, 2, 0, 0, lower, upper))
    lines.append(record("control unit_alias", 2, 3, 1, 0, 0, class_of(reference(2).levels[3], UNITS[0])))
    for control in range(8):
        refusal(control)
        lines.append(record("refusal", control, 1))
    lines.append(record("control forward_leak", *forward_leak()))
    lines.append(record("total", 4, len(levels), sum(level.index for level in levels),
                        sum(len(level.occurrences) for level in levels)))
    return "\n".join(lines) + "\n"


def validate_native(text):
    require(isinstance(text, str) and text.endswith("\n"), "packet must end with newline")
    expected = expected_packet()
    require(text == expected, next(
        (f"complete inventory differs at line {i + 1}: expected {e!r}, got {a!r}"
         for i, (e, a) in enumerate(zip_longest(expected.splitlines(), text.splitlines())) if e != a),
        "noncanonical spacing or final newline"))
    return {
        "schema": SCHEMA,
        "scope": "complete bounded matrix quotients and literal block profiles; conditional geometric enclosure",
        "limits": list(LIMITS),
        "fixtures": [{"fixture": i, "depth": reference(i).depth,
                      "levels": [list(level.summary()) for level in reference(i).levels]} for i in range(4)],
        "named_depth_two_smith": list(reference(0).levels[2].smith),
        "named_depth_two_orders": list(reference(0).levels[2].orders),
        "physical_forward_leak": list(forward_leak()),
        "negative_construction_controls": 8,
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
    result = validate_native(args.native_output.read_text())
    result.update(receipt_source())
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
