#!/usr/bin/env python3
"""Independent integer/literal-word oracle for the companion-family controls.

The family arithmetic and literal-word checks import no PSC code and do not
construct the proposed prefixes. They expand the literal words, scan cumulative
letter counts, and check all three shortest witnesses for even r in 2..32 and
the odd parameter r=3 (whose determinant is still two). Optional --corpus-shapes
reuses the existing independent Python corpus and Anderson-Putnam language
enumerator; it remains independent of the canonical Mojo implementation.
Arbitrary-precision incidence arithmetic independently checks the closed
cubic/discriminant formulas and nilpotence by cubing the reduced matrix.
The finite run does not prove the theorem for unbounded r.
"""

import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import sys


WORD_CAP = 100_000


def multiply(a, b):
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def determinant(matrix):
    a = [[Fraction(x) for x in row] for row in matrix]
    out = Fraction(1)
    for col in range(len(a)):
        pivot = next((i for i in range(col, len(a)) if a[i][col]), None)
        if pivot is None:
            return 0
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
            out = -out
        out *= a[col][col]
        for row in range(col + 1, len(a)):
            ratio = a[row][col] / a[col][col]
            a[row] = [x - ratio * y for x, y in zip(a[row], a[col])]
    assert out.denominator == 1
    return int(out)


def inflate(sigma, word):
    length = sum(len(sigma[a]) for a in word)
    if length > WORD_CAP:
        raise RuntimeError("oracle word cap exhausted; no conclusion")
    return tuple(b for a in word for b in sigma[a])


def first_witness(sigma, a, b, max_depth):
    top, bottom = (a,), (b,)
    for depth in range(1, max_depth + 1):
        top, bottom = inflate(sigma, top), inflate(sigma, bottom)
        top_counts, bottom_counts = [0, 0, 0], [0, 0, 0]
        for offset, (x, y) in enumerate(zip(top, bottom)):
            if x == y and top_counts == bottom_counts:
                return depth, offset, x, tuple(top_counts)
            top_counts[x] += 1
            bottom_counts[y] += 1
    raise RuntimeError("oracle depth exhausted; no conclusion")


def check_parameter(r):
    sigma = ((1,), (2,), tuple(map(int, "100" + "2" * r + "1")))
    matrix = [[sigma[col].count(row) for col in range(3)] for row in range(3)]
    cube = multiply(multiply(matrix, matrix), matrix)
    assert all(x > 0 for row in cube for x in row)
    assert cube == [
        [2, 2 * r, 4 + 2 * r**2],
        [2, 2 + 2 * r, 4 + 2 * r + 2 * r**2],
        [r, 2 + r**2, 2 + 4 * r + r**3],
    ]
    trace = sum(matrix[i][i] for i in range(3))
    minors = sum(
        matrix[i][i] * matrix[j][j] - matrix[i][j] * matrix[j][i]
        for i, j in combinations(range(3), 2)
    )
    det = determinant(matrix)
    assert (trace, minors, det) == (r, -2, 2)
    # Coefficients of t^3 + b t^2 + c t + d.
    b, c, d = -trace, minors, -det
    discriminant = b * b * c * c - 4 * c**3 - 4 * b**3 * d - 27 * d * d + 18 * b * c * d
    assert discriminant == -8 * r**3 + 4 * r**2 - 72 * r - 76 < 0
    polynomial = lambda t: t**3 + b * t**2 + c * t + d
    assert polynomial(2) < 0
    assert all(polynomial(t) != 0 for t in (-2, -1, 1, 2))
    reduced = [[x % 2 for x in row] for row in matrix]
    reduced_cube = multiply(multiply(reduced, reduced), reduced)
    nilpotent = all(x % 2 == 0 for row in reduced_cube for x in row)
    assert nilpotent == (r % 2 == 0)

    witnesses = {pair: first_witness(sigma, *pair, 5) for pair in combinations(range(3), 2)}
    assert witnesses[(0, 2)] == (1, 0, 1, (0, 0, 0))
    depth, offset, prefix = (4, 20, (6, 7, 7)) if r == 2 else (3, r + 12, (4, 5, r + 3))
    assert witnesses[(1, 2)] == (depth, offset, 2, prefix)
    assert witnesses[(0, 1)] == (depth + 1, offset, 2, prefix)
    return len(witnesses)


def check_corpus_shapes():
    """Read the existing independent corpus and AP language enumerator.

    This is a finite calibration of original eventual-range graphs, not a
    classification of all possible graphs or of a hypothetical stack factor.
    In particular, a surviving grouped square need not be an original
    complete bipartite graph.
    """
    root = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(root / "reference"))
    from psc_research.pip_screen import pip_corpus
    from h1_census_ap import legal_words

    shapes, examples = Counter(), {}
    for source in pip_corpus():
        sigma = tuple(tuple(x - 1 for x in source[a + 1]) for a in range(3))
        reduced = [[sigma[col].count(row) % 2 for col in range(3)] for row in range(3)]
        cube = multiply(multiply(reduced, reduced), reduced)
        if any(x % 2 for row in cube for x in row):
            continue
        first, last = [w[0] for w in sigma], [w[-1] for w in sigma]
        edges = {w for w in legal_words(sigma, 2) if len(w) == 2}
        for _ in range(10):
            following = {(last[a], first[b]) for a, b in edges}
            if following == edges:
                break
            edges = following
        else:
            raise AssertionError("eventual range failed to stabilize")
        left, right = {a for a, _ in edges}, {b for _, b in edges}
        vertices = {(0, a) for a in left} | {(1, b) for b in right}
        seen = {next(iter(vertices))}
        while True:
            following = seen | {(1, b) for a, b in edges if (0, a) in seen} | {
                (0, a) for a, b in edges if (1, b) in seen
            }
            if following == seen:
                break
            seen = following
        assert seen == vertices
        beta = len(edges) - len(left) - len(right) + 1
        if beta <= 0:
            continue
        key = len(left), len(right), len(edges), beta
        shapes[key] += 1
        examples.setdefault(key, "/".join("".join(map(str, w)) for w in sigma))
    expected = {(2, 2, 4, 1): 24, (2, 3, 5, 1): 6, (2, 3, 6, 2): 24,
                (3, 2, 5, 1): 6, (3, 2, 6, 2): 24, (3, 3, 9, 4): 12}
    assert shapes == expected
    assert sum(shapes.values()) == 96
    complete = sum(count for (left, right, edges, _), count in shapes.items() if left * right == edges)
    assert complete == 84
    print("EVEN_RESIDUE_SHAPES columns=left_vertices,right_vertices,edges,beta1,count,example")
    for key, count in sorted(shapes.items()):
        print(*key, count, examples[key], sep="\t")
    print("EVEN_RESIDUE_SHAPES retained=96 original_complete=84 original_missing_one_edge=12")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus-shapes", action="store_true", help="also check the 96 existing residue graphs")
    args = parser.parse_args()
    pairs = sum(check_parameter(r) for r in range(2, 33, 2))
    assert pairs == 48
    assert check_parameter(3) == 3
    print("EVEN_COMPANION_ORACLE even_r=2..32 specimens=16 unordered_pairs=48 odd_r3_pairs=3")
    print("literal_expansion=independent prefix_count_scan=independent arithmetic=Python_int_Fraction")
    print("PIP_checks=primitive_cube,rational_root_test,negative_discriminant,root_above_2")
    print("nilpotence=direct_matrix_cube all_checks=passed unbounded_claim=false")
    if args.corpus_shapes:
        check_corpus_shapes()


if __name__ == "__main__":
    main()
