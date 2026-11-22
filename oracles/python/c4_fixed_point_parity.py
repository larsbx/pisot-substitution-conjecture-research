#!/usr/bin/env python3
"""Independent finite replay of PR #636 against the optional Mojo census log."""
from __future__ import annotations

import argparse
import ast
import json
import re
import sys
from collections import Counter
from itertools import product
from pathlib import Path
from typing import NamedTuple

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "reference"))
from psc_research.pip_screen import charpoly, irreducible, mat, mul, pip_corpus, pisot, primitive


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def endpoint_data(words):
    first = tuple(word[0] for word in words)
    last = tuple(word[-1] for word in words)
    # Carry both single letters and length-two factors through one inflation.
    # Starting with all single letters supplies factors from every supertile.
    letters = tuple((a,) for a in range(len(words)))
    factors = set(letters)
    while True:
        wider = set(factors)
        for factor in factors:
            image = tuple(a for b in factor for a in words[b])
            wider.update(zip(image, image[1:]))
        if wider == factors:
            break
        factors = wider
    legal = {factor for factor in factors if len(factor) == 2}
    # Independently calculate the stable image as a set of edges.
    eventual = legal
    while True:
        next_edges = {(last[b], first[a]) for b, a in eventual}
        if next_edges == eventual:
            break
        check(next_edges < eventual, "legal edge image must decrease to the eventual range")
        eventual = next_edges
    return (last, first), legal, eventual


def advance(g, xs):
    return tuple(g[x] for x in xs)


def count_powers(words, maps, legal, matrix, depth=8):
    alphabet = range(len(words))
    images = [(a,) for a in alphabet]
    endpoints = [tuple(alphabet), tuple(alphabet)]
    identity = [[int(a == b) for b in alphabet] for a in alphabet]
    power = identity
    traces, counts = [], []
    for n in range(1, depth + 1):
        images = [tuple(a for b in word for a in words[b]) for word in images]
        check(all(len(word) <= 2_000_000 for word in images), ("word cap", words, n))
        check(all(word != (a,) for a, word in enumerate(images)), ("singleton self-image", words, n))
        endpoints = [advance(g, xs) for g, xs in zip(maps, endpoints)]
        check(endpoints == [tuple(w[-1] for w in images), tuple(w[0] for w in images)],
              ("endpoint iteration", words, n))
        left, right = ({a for a in alphabet if xs[a] == a} for xs in endpoints)
        seams = len(legal.intersection(product(left, right)))
        literal = sum(word[1:-1].count(a) for a, word in enumerate(images)) + seams
        power = [[sum(matrix[i][k] * power[k][j] for k in alphabet)
                  for j in alphabet] for i in alphabet]
        trace = sum(power[a][a] for a in alphabet)
        check(literal + len(left) + len(right) == trace + seams, ("fixed count", words, n))
        traces.append(trace)
        counts.append(literal)
    return traces, counts


class Profile(NamedTuple):
    coefficients: tuple[int, int, int]
    theorem_e_filter: bool
    tree: bool
    square: bool
    traces: list[int]
    counts: list[int]


def profile(words, depth=8):
    matrix = mat({a + 1: tuple(x + 1 for x in w) for a, w in enumerate(words)})
    coeffs = charpoly(matrix)
    trace, e2, det = coeffs
    maps, legal, eventual = endpoint_data(words)
    left, right = ({edge[side] for edge in eventual} for side in range(2))
    for g, vertices in zip(maps, (left, right)):
        codes = tuple(range(3))
        for _ in range(6):
            codes = advance(g, codes)
        check(vertices == {a for a in range(3) if codes[a] == a}, ("periodic letters", words))
    past_endpoints = set(product(left, right))
    check(eventual == legal & past_endpoints, ("eventual edges", words))
    square = len(left) == len(right) == 2 and eventual == past_endpoints
    e_filter = any(len(set(g)) == 3 and len(side) >= 2 for g, side in zip(maps, (left, right)))
    tree = len(eventual) - len(left) - len(right) + 1 == 0
    reached = {min(eventual)}
    while True:
        wider = reached | {p for p in eventual if any(
            p[0] == q[0] or p[1] == q[1] for q in reached)}
        if wider == reached:
            break
        reached = wider
    check(reached == eventual, ("disconnected eventual range", words))
    traces, counts = count_powers(words, maps, legal, matrix, depth)
    check(traces[:3] == [trace, trace**2 - 2 * e2, trace**3 - 3 * trace * e2 + 3 * det],
          ("Newton identities", words))
    if not e_filter and not tree:
        check(square, ("complete eventual range", words))
        check([c % 2 for c in counts] == [p % 2 for p in traces],
              ("count and trace parity", words))
        check((not any(c % 2 for c in counts)) == (trace % 2 == det % 2 == 0),
              ("first and third traces", words))
    return Profile(coeffs, e_filter, tree, square, traces, counts)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mojo-census", type=Path, help="stdout from nonunit_residue_census.mojo")
    parser.add_argument("--mojo-productivity", type=Path, help="stdout from residue_productivity.mojo")
    args = parser.parse_args()

    # Neither of these two controls uses the Pisot screening as the count oracle.
    tm = ((0, 1), (1, 0))
    tm_maps, tm_legal, _ = endpoint_data(tm)
    _, tm_counts = count_powers(tm, tm_maps, tm_legal, [[1, 1], [1, 1]])
    check(tm_counts == [2**n - 2 * (n % 2) for n in range(1, 9)], "Thue–Morse")
    trib = ((0, 1), (0, 2), (0,))
    check(profile(trib).counts[:3] == [0, 2, 6], "Tribonacci")

    # Primitive irreducible Pisot nonunit example outside the length-three corpus.
    odd_det = ((1,), (1, 2, 2, 2), (2, 0, 1, 1))
    control = profile(odd_det)
    check(control.coefficients == (2, -5, 3) and control.square
          and control.traces[:3] == [2, 14, 47] and control.counts[:3] == [0, 14, 45],
          "odd determinant")
    odd_det_result = {"sigma": odd_det, "traces": control.traces[:3],
                      "fixed_counts": control.counts[:3]}
    check(primitive(mat({1: (2,), 2: (2, 3, 3, 3), 3: (3, 1, 2, 2)}))
          and irreducible(*control.coefficients) and pisot(*control.coefficients),
          "odd-determinant Pisot screen")

    totals = Counter()
    survivors = {}
    nilpotent = []
    shape_row = set()
    for sigma in pip_corpus():
        totals["corpus"] += 1
        if abs(charpoly(mat(sigma))[2]) == 1:
            continue
        words = tuple(tuple(x - 1 for x in sigma[a]) for a in (1, 2, 3))
        result = profile(words)
        trace, e2, det = result.coefficients
        e_filter, tree = result.theorem_e_filter, result.tree
        odd = any(c % 2 for c in result.counts)
        totals["nonunit"] += 1
        totals["theorem_e"] += e_filter
        totals["tree"] += tree
        totals["theorem_e_or_tree"] += e_filter or tree
        totals["past_theorem_e_and_tree"] += not e_filter and not tree
        totals["odd_fixed_count"] += odd
        check(det % 2 == 0, ("odd corpus determinant", words))
        matrix = [[word.count(a) % 2 for word in words] for a in range(3)]
        cube = mul(mul(matrix, matrix), matrix)
        nil = all(x % 2 == 0 for row in cube for x in row)
        check(nil == (trace % 2 == e2 % 2 == det % 2 == 0),
              ("nilpotence and cubic coefficients", words))
        if result.square and nil:
            shape_row.add(words)
        if e_filter or tree or odd:
            continue
        survivors[words] = result.coefficients
        if nil:
            nilpotent.append({"substitution": words, "trace": trace, "e2": e2, "det": det,
                              "fixed_counts": result.counts})
    totals["survivors"] = len(survivors)
    totals["nilpotent_mod_two"] = len(nilpotent)
    check(shape_row == {row["substitution"] for row in nilpotent}, "earlier K2,2 shape row")
    check(totals == {"corpus": 4554, "nonunit": 1926, "theorem_e": 840, "tree": 1362,
                     "theorem_e_or_tree": 1794, "past_theorem_e_and_tree": 132,
                     "odd_fixed_count": 1338, "survivors": 72, "nilpotent_mod_two": 24},
          ("corpus totals", totals))

    if args.mojo_census:
        mojo = {}
        reported = {}
        for line in args.mojo_census.read_text().splitlines():
            row = re.fullmatch(r"survivor: [\d ]+ sigma (\[.*\]) tr (-?\d+) e2 (-?\d+) det (-?\d+)", line)
            if row:
                words = tuple(map(tuple, ast.literal_eval(row[1])))
                check(words not in mojo, ("duplicate Mojo substitution", words))
                mojo[words] = tuple(map(int, row.groups()[1:]))
            elif re.fullmatch(r"\w+: \d+", line):
                key, value = line.split(": ")
                reported[key] = int(value)
        expected_keys = ("nonunit", "theorem_e", "tree", "odd_fixed_count", "survivors",
                         "nilpotent_mod_two")
        check(all(reported.get(key) == totals[key] for key in expected_keys), ("Mojo totals", reported))
        check(mojo == survivors, ("Mojo survivor rows", mojo.keys() ^ survivors.keys()))

    productivity = {}
    if args.mojo_productivity:
        for line in args.mojo_productivity.read_text().splitlines():
            if match := re.fullmatch(r"productive: (\[.*\]) states (\d+)", line):
                words = tuple(map(tuple, ast.literal_eval(match[1])))
                check(words not in productivity, ("duplicate productivity record", words))
                productivity[words] = int(match[2])
        check(productivity.keys() == shape_row, "productivity receipt does not match the survivors")
        for row in nilpotent:
            row["productive_box_states"] = productivity[row["substitution"]]

    print(json.dumps({"counts": totals, "word_trace_comparisons": totals["nonunit"] * 8,
                      "mojo_rows_matched": len(survivors) if args.mojo_census else None,
                      "mojo_productivity_rows_matched": len(productivity) if args.mojo_productivity else None,
                      "odd_determinant_control": odd_det_result,
                      "nilpotent_survivors": nilpotent}, indent=2))


if __name__ == "__main__":
    main()
