"""Independent exact oracle for finite local incoming-admissibility controls.

Canonical implementation: kernel/psc/c4_local_admissibility.mojo. This oracle
rescans literal prefixes, uses permutation determinants/Cramer's rule, and
computes finite sets with Python set operations, not the native bitset code.
Every raw pair is authenticated, including nonintegral and outside pairs.
The cyclic models are abstract compact-interface controls, not authenticated
Pisot tiles. No finite result certifies a Haar recurrence or a governed claim.
"""

from collections import Counter
from dataclasses import dataclass
from itertools import zip_longest
from pathlib import Path
import argparse
import hashlib
import json
import subprocess

from c4_bounded_cover import (
    InvalidCertificate, require, integer, incidence, determinant,
    inverse_integer, digits, mv, construct as construct_bounded,
)


SCHEMA = "c4-local-admissibility-v1"
LIMITS = (15, 64, 27, 64, 4096, 20000, 200000, 100000)
ROOT = Path(__file__).resolve().parents[2]
SOURCES = (
    ".github/workflows/c4-local-admissibility.yml",
    "kernel/psc/c4_local_admissibility.mojo",
    "kernel/c4_local_admissibility.mojo",
    "kernel/tests/test_c4_local_admissibility.mojo",
    "kernel/psc/c4_bounded_cover.mojo",
    "oracles/python/c4_local_admissibility.py",
    "oracles/python/c4_bounded_cover.py",
    "tests/test_c4_local_admissibility_oracle.py",
    "proof/PscVerif/PscVerif/OccurrenceAdmissibility.lean",
    "proof/PscVerif/PscVerif/OccurrenceCover.lean",
    "proof/PscVerif/PscVerif/OccurrencePiece.lean",
    "docs/c4-local-admissibility-2026-11-11.md",
    "docs/c4-local-admissibility-literature-2026-11-11.md",
    "kernel/pixi.toml", "kernel/pixi.lock", "vendored.toml",
)


@dataclass(frozen=True)
class Model:
    words: tuple
    sources: tuple
    domain: tuple
    modulus: int
    action: int
    star: tuple
    tiles: tuple
    profile_modulus: int
    profiles: tuple


def mask(points):
    return sum(1 << x for x in points)


def affine(points, modulus, action, translation):
    return frozenset((action * x + translation) % modulus for x in points)


def star(model, vector):
    return sum(a * b for a, b in zip(model.star, vector)) % model.modulus


def overlap(model, packet):
    return model.tiles[packet[0]] & affine(
        model.tiles[packet[1]], model.modulus, 1, star(model, packet[2:]))


def validate_model(model):
    """Check actual finite tile equations, commuting actions and enclosures."""
    require(integer(model.modulus) and 2 <= model.modulus <= LIMITS[0], "group modulus")
    require(integer(model.action) and 0 <= model.action < model.modulus, "normalized action")
    require(integer(model.profile_modulus) and 1 <= model.profile_modulus <= model.modulus,
            "profile modulus")
    require(model.modulus % model.profile_modulus == 0, "profile quotient is not additive")
    require(len(model.words) == 3 and all(
        1 <= len(w) <= LIMITS[2] and all(integer(c) and 0 <= c < 3 for c in w)
        for w in model.words), "literal images")
    require(len(model.star) == 3 and all(
        integer(a) and 0 <= a < model.modulus for a in model.star), "normalized star")
    require(len(model.tiles) == 3 and len(model.profiles) == 3, "three tile/profile sets")
    for points, modulus in ((k, model.modulus) for k in model.tiles):
        require(isinstance(points, frozenset) and all(integer(x) and 0 <= x < modulus for x in points),
                "tile outside finite group")
    for points in model.profiles:
        require(isinstance(points, frozenset) and all(
            integer(x) and 0 <= x < model.profile_modulus for x in points), "profile outside quotient")
    for a in range(3):
        require({x % model.profile_modulus for x in model.tiles[a]} <= model.profiles[a],
                "profile fails actual tile enclosure")
    for label, packets in (("sources", model.sources), ("domain", model.domain)):
        require(len(packets) <= LIMITS[1], label + " packet budget exhausted")
        for packet in packets:
            require(len(packet) == 5 and all(integer(x) for x in packet), "integer packet")
            require(all(0 <= a < 3 for a in packet[:2]), "packet letters")
            require(all(abs(z) <= LIMITS[3] for z in packet[2:]), "coordinate budget exhausted")
        require(len(set(packets)) == len(packets), "duplicate " + label)
    require(model.sources, "empty source inventory")
    require(set(model.domain) <= set(model.sources), "domain packet lacks checked source")
    ambient = frozenset(range(model.modulus))
    require(len(affine(ambient, model.modulus, model.action, 0)) == model.modulus,
            "ambient action is not injective")
    matrix = incidence(model.words)
    for axis in range(3):
        unit = tuple(int(k == axis) for k in range(3))
        require(star(model, mv(matrix, unit)) == model.action * model.star[axis] % model.modulus,
                "star/incidence action does not commute")
    for x in ambient:
        require((model.action * x % model.modulus) % model.profile_modulus ==
                model.action * (x % model.profile_modulus) % model.profile_modulus,
                "projected action does not commute")
    marks = digits(model.words)
    for selected in range(3):
        pieces = [affine(model.tiles[d[1]], model.modulus, model.action, star(model, d[3:]))
                  for d in marks if d[0] == selected]
        require(frozenset().union(*pieces) == model.tiles[selected], "original complete tile equation")
    return matrix, marks


@dataclass(frozen=True)
class Inventory:
    model: Model
    matrix: tuple
    digits: tuple
    pairs: tuple
    rows: tuple
    basis: tuple

    def summary(self):
        checked = tuple(row for row in self.rows if row[0])
        return (len(self.rows), len(self.pairs), sum(r[6] for r in self.rows),
                sum(r[7] for r in self.rows), sum(r[10] for r in self.rows),
                sum(r[11] for r in self.rows), sum(r[12] for r in self.rows),
                int(all(r[13] for r in checked)), int(all(r[14] for r in checked)),
                int(all(r[15] for r in checked)), sum(b[5] for b in self.basis),
                sum(r[19] for r in self.rows))


def construct(model, *, candidate_cap=LIMITS[6]):
    """Complete one-step inventory; budgets refuse instead of removing pairs."""
    matrix, marks = validate_model(model)
    require(determinant(matrix) != 0, "singular incidence: bounded inverse enumeration unavailable")
    require(integer(candidate_cap) and 1 <= candidate_cap <= LIMITS[6], "invalid candidate budget")
    pairs, rows, basis = [], [], []
    states, histories = set(model.sources), len(model.sources)
    for source, packet in enumerate(model.sources):
        raw_sets, integral_sets, retained_sets, profile_sets = [], [], [], []
        source_pairs = []
        for ti, top in enumerate(marks):
            if top[0] != packet[0]:
                continue
            for bi, bottom in enumerate(marks):
                if bottom[0] != packet[1]:
                    continue
                require(len(pairs) < candidate_cap, "candidate budget exhausted")
                rhs = tuple(packet[2+k] + bottom[3+k] - top[3+k] for k in range(3))
                solution = inverse_integer(matrix, rhs)
                integral = solution is not None
                top_shift = star(model, top[3:])
                bottom_shift = star(model, tuple(packet[2+k] + bottom[3+k] for k in range(3)))
                top_set = affine(model.tiles[top[1]], model.modulus, model.action, top_shift)
                bottom_set = affine(model.tiles[bottom[1]], model.modulus, model.action, bottom_shift)
                raw = top_set & bottom_set
                projected_top = affine(model.profiles[top[1]], model.profile_modulus,
                                       model.action, top_shift)
                projected_bottom = affine(model.profiles[bottom[1]], model.profile_modulus,
                                          model.action, bottom_shift)
                projected = projected_top & projected_bottom
                require({x % model.profile_modulus for x in raw} <= projected,
                        "actual paired set escapes projected enclosure")
                inside, ancestor_set, inverse_set, retained_set = False, frozenset(), frozenset(), frozenset()
                if integral:
                    require(all(abs(x) <= LIMITS[3] for x in solution), "coordinate budget exhausted")
                    ancestor = (top[1], bottom[1], *solution)
                    states.add(ancestor)
                    histories += 1
                    require(len(states) <= LIMITS[4], "state budget exhausted")
                    require(histories <= LIMITS[5], "history budget exhausted")
                    inside = ancestor in model.domain
                    ancestor_set = overlap(model, ancestor)
                    inverse_set = affine(ancestor_set, model.modulus, model.action, top_shift)
                    require(inverse_set == raw, "actual inverse piece differs from paired piece")
                    if inside:
                        retained_set = inverse_set
                pair = (source, ti, bi, *rhs, int(integral), top[1], bottom[1],
                        *(solution if integral else (0, 0, 0)), int(inside),
                        mask(top_set), mask(bottom_set), mask(raw), mask(ancestor_set),
                        mask(inverse_set), mask(retained_set), mask(projected_top),
                        mask(projected_bottom), mask(projected))
                pairs.append(pair)
                source_pairs.append(pair)
                raw_sets.append(raw)
                integral_sets.append(inverse_set)
                retained_sets.append(retained_set)
                profile_sets.append(projected)
        actual = overlap(model, packet)
        raw_union = frozenset().union(*raw_sets)
        integral_union = frozenset().union(*integral_sets)
        retained_union = frozenset().union(*retained_sets)
        require(raw_union == actual, "unconditional raw paired union")
        require(retained_union <= integral_union <= actual, "inverse union subset")
        nonintegral = sum(bool(raw) and not p[6] for p, raw in zip(source_pairs, raw_sets))
        outside = sum(bool(raw) and bool(p[6]) and not p[12] for p, raw in zip(source_pairs, raw_sets))
        local, represented = nonintegral == 0, nonintegral == 0 and outside == 0
        covered = retained_union == actual
        contained = all(raw <= retained_union for raw in raw_sets)
        require(not local or integral_union == actual, "local lifting implies integral cover")
        require(not represented or covered, "represented pairs imply retained cover")
        require(covered == contained, "exact all-raw-pairs containment criterion")
        nonempty_retained = [k for k in retained_sets if k]
        duplicate_images = sum(n - 1 for n in Counter(nonempty_retained).values())
        rows.append((int(packet in model.domain), mask(actual), mask(raw_union),
                     mask(integral_union), mask(retained_union), len(source_pairs),
                     sum(bool(k) for k in raw_sets), sum(p[6] for p in source_pairs),
                     sum(bool(raw) and bool(p[6]) for p, raw in zip(source_pairs, raw_sets)),
                     sum(p[12] for p in source_pairs), len(nonempty_retained), nonintegral, outside,
                     int(local), int(represented), int(covered), int(contained), duplicate_images,
                     sum(bool(raw) and not p[12] and raw <= retained_union
                         for p, raw in zip(source_pairs, raw_sets)),
                     sum(not k for k in profile_sets)))
    for axis in range(3):
        unit = tuple(int(k == axis) for k in range(3))
        # Native basis witnesses are extracted from a complete bounded probe,
        # not from an isolated solve. Apply every bound to that whole row too:
        # an unrelated selected mark may otherwise exceed a coordinate cap.
        child = model.words[0][0]
        probe = construct_bounded(model.words, ((child, child, *unit),), (), 1)
        require(probe.candidates and probe.candidates[0][1:3] == (0, 0),
                "basis probe lost its actual first zero-prefix pair")
        require(probe.digits[0] == (child, 0, 0, 0, 0, 0), "basis first literal mark")
        value = star(model, unit)
        preimages = tuple(x for x in range(model.modulus) if model.action * x % model.modulus == value)
        require(len(preimages) == 1, "ambient basis preimage")
        solution = inverse_integer(matrix, unit)
        first = probe.candidates[0]
        require((solution is None) == (first[3] == 0), "basis probe integral agreement")
        if solution is not None:
            require(probe.nodes[first[4]][7:10] == solution, "basis probe exact solution agreement")
        basis.append((*unit, preimages[0], value, int(solution is not None),
                      *(solution if solution is not None else (0, 0, 0))))
    return Inventory(model, matrix, marks, tuple(pairs), tuple(rows), tuple(basis))


def fixture(index):
    g = frozenset(range(3))
    one = frozenset((0,))
    sources = ((0, 1, 0, 0, 0), (1, 0, 0, 0, 0))
    words, modulus, action, coefficients = ((0, 0), (1, 1), (2, 2)), 3, 2, (1, 1, 1)
    tiles, profile_modulus, profiles = (g, g, g), 1, (one, one, one)
    domain = None
    if index == 0:
        sources = ((1, 2, 0, 0, 0), (2, 1, 0, 0, 0))
        words, action, coefficients = ((0, 0), (1,), (2,)), 1, (0, 1, 1)
    elif index == 1:
        pass
    elif index == 2:
        sources = ((0, 1, 0, 0, 1), (1, 0, 0, 0, -1))
    elif index == 3:
        words, action = ((1,), (2,), (0,)), 1
    elif index == 4:
        words, action, coefficients = ((0, 1), (1,), (2,)), 1, (0, 0, 0)
    elif index == 5:
        words, modulus, action, coefficients = ((0, 0), (1,), (2,)), 6, 1, (0, 1, 1)
        tiles = tuple(frozenset((a, a+3)) for a in range(3))
        profile_modulus, profiles = 3, tuple(frozenset((a,)) for a in range(3))
        sources = ((1, 2, 1, 0, 0), (2, 1, -1, 0, 0),
                   (1, 2, 0, -1, 0), (2, 1, 0, 1, 0),
                   (1, 2, 1, -1, 0), (2, 1, -1, 1, 0))
        domain = sources[:4]
    else:
        raise InvalidCertificate("unknown finite local model")
    return Model(words, sources, sources if domain is None else domain,
                 modulus, action, coefficients, tiles, profile_modulus, profiles)


def reference(index):
    return construct(fixture(index))


def record(kind, *values):
    return kind + " " + " ".join(map(str, values))


def model_lines(index, model, *, singular=False):
    lines = [record("singular_model" if singular else "model", index,
                    model.modulus, model.action, determinant(incidence(model.words)), model.profile_modulus)]
    for a, word in enumerate(model.words):
        lines.append(record("image", index, a, len(word), *word))
    lines.extend((record("star", index, *model.star), record("tiles", index, *map(mask, model.tiles)),
                  record("profiles", index, *map(mask, model.profiles))))
    for i, packet in enumerate(model.sources):
        lines.append(record("source", index, i, *packet))
    for i, packet in enumerate(model.domain):
        lines.append(record("domain", index, i, *packet))
    return lines


def core_lines(index, value):
    lines = model_lines(index, value.model)
    for kind, records in (("digit", value.digits), ("pair", value.pairs),
                          ("row", value.rows), ("basis", value.basis)):
        for i, row in enumerate(records):
            lines.append(record(kind, index, i, *row))
    lines.append(record("summary", index, *value.summary()))
    return lines


def singular_control():
    g, empty, zero = frozenset(range(3)), frozenset(), frozenset((0,))
    roots = ((0, 0, 0, 0, 0),)
    model = Model(((0,), (0,), (0,)), roots, roots, 3, 1, (0, 0, 0),
                  (g, empty, empty), 1, (zero, empty, empty))
    matrix, marks = validate_model(model)
    require(determinant(matrix) == 0, "singular witness is nonsingular")
    nonempty_pairs = tuple((top, bottom) for top in marks for bottom in marks
                           if affine(model.tiles[top[1]], 3, 1, 0) &
                           affine(model.tiles[bottom[1]], 3, 1, 0))
    require(len(nonempty_pairs) == 1 and nonempty_pairs[0][0][1] == nonempty_pairs[0][1][1] == 0,
            "singular nonempty paired mark inventory")
    rows = []
    for ancestor in ((0, 0, 0, 0, 0), (0, 0, 1, -1, 0)):
        mapped = mv(matrix, ancestor[2:])
        actual = overlap(model, ancestor)
        require(mapped == (0, 0, 0) and actual == g, "singular exact lift witness")
        rows.append((*ancestor, *mapped, mask(actual), int(ancestor in model.domain)))
    require(tuple(r[-1] for r in rows) == (1, 0), "singular represented/outside witnesses")
    return model, tuple(rows), (1, 2, 1)


def forward_leak():
    """Mandatory control: integer inverse closure versus physical forward exit.

    The integer interval length below is explicitly physical calibration.
    It is never used for a finite-group set or compact Haar measure.
    """
    model = fixture(1)
    matrix = incidence(model.words)
    full, retained, exits = 0, 0, 0
    for source in model.sources:
        for i in range(2):
            for j in range(2):
                top = tuple(i * int(k == source[0]) for k in range(3))
                bottom = tuple(j * int(k == source[1]) for k in range(3))
                inverse_rhs = tuple(bottom[k] - top[k] for k in range(3))
                lift = inverse_integer(matrix, inverse_rhs)
                require((lift is not None) == (i == j == 0), "literal inverse closure by parity")
                if lift is not None:
                    require((source[0], source[1], *lift) in model.domain, "inverse ancestor exits")
                delta = tuple(top[k] - bottom[k] for k in range(3))
                child = (source[0], source[1], *delta)
                offset = sum(delta)
                length = max(0, min(1, 1-offset) - max(0, -offset))
                full += length
                retained += length if child in model.domain else 0
                exits += int(length > 0 and child not in model.domain)
    require((full, retained, exits) == (4, 2, 2), "forward leak disappeared")
    return full, retained, exits


def expected_packet():
    """Reference text for adversarial tests; never credited as native evidence."""
    lines = ["schema " + SCHEMA, record("limits", *LIMITS)]
    summaries = []
    for index in range(6):
        value = reference(index)
        lines.extend(core_lines(index, value))
        summaries.append(value.summary())
    model, lifts, summary = singular_control()
    lines.extend(model_lines(6, model, singular=True))
    for i, lift in enumerate(lifts):
        lines.append(record("singular_lift", 6, i, *lift))
    lines.append(record("singular_summary", 6, *summary))
    lines.append(record("control", "forward_leak", *forward_leak()))
    lines.append(record("total", 6, sum(s[0] for s in summaries), sum(s[1] for s in summaries)))
    return "\n".join(lines) + "\n"


def validate_native(text):
    require(isinstance(text, str) and text.endswith("\n"), "packet must end with newline")
    expected = expected_packet()
    require(text == expected, next(
        (f"inventory differs at line {i+1}: expected {e!r}, got {a!r}"
         for i, (e, a) in enumerate(zip_longest(expected.splitlines(), text.splitlines())) if e != a),
        "noncanonical packet spacing or final newline"))
    return {"schema": SCHEMA,
            "scope": "abstract finite cyclic-group controls; conditional authentic geometry",
            "models": [{"model": i, "summary": list(reference(i).summary())} for i in range(6)],
            "singular_control": list(singular_control()[2]),
            "physical_forward_leak": list(forward_leak()),
            "native_sha256": hashlib.sha256(text.encode()).hexdigest(),
            "bytes": len(text.encode()), "lines": len(text.splitlines()),
            "no_governed_claim_promoted": True}


def receipt_source():
    return {"git_head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
            "git_tree": subprocess.check_output(["git", "rev-parse", "HEAD^{tree}"], cwd=ROOT, text=True).strip(),
            "worktree_dirty": bool(subprocess.check_output(
                ["git", "status", "--porcelain"], cwd=ROOT, text=True).strip()),
            "sources": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in SOURCES}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = validate_native(args.native.read_text())
    result.update(receipt_source())
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
