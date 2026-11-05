"""Independent Fraction/inverse-matrix oracle for the native residue certificate.

The canonical finite calculation is kernel/psc/c4_nonunit_residue_occupancy.mojo.
This oracle uses rational Gaussian elimination, not the native adjugate keys.
It checks finite words and algebraic identities; it does not execute a proof
of lattice density, Haar measure, an exact tile volume, or general PSC.
"""

from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
import os
from pathlib import Path
import unittest


SIGMA = ("1", "021", "001")
P = (-2, -2, -1, 1)  # beta^3 - beta^2 - 2 beta - 2
F = ((2, 1, 0), (0, 0, 1), (0, 1, 0))
BETA_LO = Q(22695, 10000)
BETA_HI = Q(22696, 10000)


def multiply(a, b):
    return tuple(tuple(sum(x * y for x, y in zip(row, column))
                       for column in zip(*b)) for row in a)


def incidence(words):
    return tuple(tuple(word.count(str(c)) for word in words) for c in range(3))


def inverse(a):
    rows = [[Q(x) for x in a[i]] + [Q(i == j) for j in range(3)]
            for i in range(3)]
    for k in range(3):
        pivot = next((i for i in range(k, 3) if rows[i][k]), None)
        if pivot is None:
            raise ValueError("singular incidence power")
        rows[k], rows[pivot] = rows[pivot], rows[k]
        divisor = rows[k][k]
        rows[k] = [x / divisor for x in rows[k]]
        for i in range(3):
            if i != k:
                factor = rows[i][k]
                rows[i] = [x - factor * y for x, y in zip(rows[i], rows[k])]
    return tuple(tuple(row[3:]) for row in rows)


def residue(inv, prefix):
    """Class in Q^3/Z^3 of (M^q)^-1 prefix; negatives normalized exactly."""
    return tuple(sum(x * y for x, y in zip(row, prefix)) % 1 for row in inv)


def literal_table(sigma, q, word_cap=100000):
    if (len(sigma) != 3 or any(not w or any(c not in "012" for c in w)
                              for w in sigma)):
        raise ValueError("three nonempty words on 012 required")
    if not 0 <= q <= 10 or not 1 <= word_cap <= 100000:
        raise ValueError("bounded oracle input")
    words = ("0", "1", "2")
    for _ in range(q):
        if any(sum(len(sigma[int(c)]) for c in w) > word_cap for w in words):
            raise ValueError("word budget exhausted; no mathematical verdict")
        words = tuple("".join(sigma[int(c)] for c in w) for w in words)
    matrix = incidence(words)
    inv = inverse(matrix)
    counts = defaultdict(lambda: [0, 0, 0])
    representatives = {}
    for d, word in enumerate(words):
        prefix = [0, 0, 0]
        for c in word:
            key = (int(c), residue(inv, prefix))
            counts[key][d] += 1
            representatives.setdefault(key, tuple(prefix))
            prefix[int(c)] += 1
    return words, matrix, inv, dict(counts), representatives


def reduce_poly(poly):
    result = list(poly)
    result.extend([0] * max(0, 3 - len(result)))
    for k in range(len(result) - 1, 2, -1):
        coefficient = result[k]
        for j in range(3):
            result[k - 3 + j] -= coefficient * P[j]
        result[k] = 0
    return tuple(result[:3])


def poly_add(a, b):
    size = max(len(a), len(b))
    return tuple((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                 for i in range(size))


def poly_multiply(a, b):
    result = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return reduce_poly(result)


def weighted(counts):
    return tuple(sum(counts[d] * F[d][j] for d in range(3)) for j in range(3))


def evaluate(poly, x):
    result = Q(0)
    for c in reversed(poly):
        result = result * x + c
    return result


class TestNonunitResidueOccupancy(unittest.TestCase):
    @unittest.skipUnless(os.environ.get("PSC_OCCUPANCY_NATIVE_OUTPUT"),
                         "native driver output not supplied")
    def test_native_driver_tables_against_fraction_oracle(self):
        tables = defaultdict(dict)
        for line in Path(os.environ["PSC_OCCUPANCY_NATIVE_OUTPUT"]).read_text().splitlines():
            if not line.startswith("row "):
                continue
            fields = [int(x) for x in line.split()[1:]]
            self.assertEqual(len(fields), 8)
            q, c, r0, r1, r2, a0, a1, a2 = fields
            self.assertIn(q, range(1, 7))
            key = (c, (r0, r1, r2))
            self.assertNotIn(key, tables[q], "duplicate native residue row")
            tables[q][key] = [a0, a1, a2]
        self.assertEqual(set(tables), set(range(1, 7)), "native replay must contain every depth 1..6")
        for q, native in tables.items():
            exact = literal_table(SIGMA, q)[3]
            expected = {(c, tuple(int((2**q)*x) for x in r)): a
                        for (c, r), a in exact.items()}
            self.assertEqual(native, expected)

    def test_incidence_perron_vector_and_pisot_algebra(self):
        matrix = incidence(SIGMA)
        self.assertEqual(matrix, ((0, 1, 2), (1, 1, 1), (0, 1, 0)))
        square = multiply(matrix, matrix)
        self.assertTrue(all(x > 0 for row in square for x in row))
        for c in range(3):
            self.assertEqual(weighted(matrix[c]), poly_multiply((0, 1), F[c]))
        # Integer-root test for the monic cubic, and exact rational root bracket.
        self.assertTrue(all(evaluate(P, x) != 0 for x in (-2, -1, 1, 2)))
        a, b, c = -1, -2, -2
        self.assertEqual(a*a*b*b - 4*b*b*b - 4*a*a*a*c - 27*c*c + 18*a*b*c, -152)
        self.assertLess(evaluate(P, BETA_LO), 0)
        self.assertGreater(evaluate(P, BETA_HI), 0)
        self.assertGreater(BETA_LO, 2)
        # Negative discriminant gives one real root; conjugate product is 2/beta < 1.

    def test_full_second_level_table(self):
        words, matrix, inv, counts, _ = literal_table(SIGMA, 2)
        self.assertEqual(words, ("021", "1001021", "11021"))
        self.assertEqual(matrix, ((1, 3, 1), (1, 3, 3), (1, 1, 1)))
        scaled = {(c, tuple(int(4*x) for x in r)): a for (c, r), a in counts.items()}
        self.assertEqual(scaled, {
            (0, (0, 0, 0)): [1, 1, 1],
            (0, (2, 0, 2)): [0, 1, 0],
            (0, (2, 2, 0)): [0, 1, 0],
            (1, (0, 0, 0)): [0, 1, 1],
            (1, (2, 0, 2)): [1, 2, 2],
            (2, (0, 2, 2)): [1, 1, 1],
        })
        classes = {residue(inv, x) for x in product(range(4), repeat=3)}
        self.assertEqual(len(classes), 4)
        # The quotient has four classes, not the 64 of coordinatewise mod 4.
        self.assertEqual(residue(inv, (1, 1, 1)), (Q(0), Q(0), Q(0)))

    def test_mass_conservation_at_six_depths(self):
        for q in range(1, 7):
            _, matrix, inv, counts, _ = literal_table(SIGMA, q)
            for c in range(3):
                self.assertEqual(tuple(sum(a[d] for (letter, _), a in counts.items()
                                           if letter == c) for d in range(3)), matrix[c])
            for column in zip(*matrix):
                self.assertEqual(residue(inv, column), (Q(0), Q(0), Q(0)))
            self.assertEqual(residue(inv, (-1, 0, 0)),
                             tuple((-x) % 1 for x in residue(inv, (1, 0, 0))))

    def test_exact_occupancy_bounds_not_volume_equalities(self):
        # Selected rows give denominators W_c in the depth-two theorem.
        weights = [weighted(a) for a in ((1, 1, 1), (1, 2, 2), (1, 1, 1))]
        self.assertEqual(weights, [(2, 2, 1), (2, 3, 2), (2, 2, 1)])
        numerators = [poly_multiply((0, 0, 1), f) for f in F]
        # 4 W_c - 2 beta^2 F_c is positive, using beta > 2 for c=0.
        gaps = [reduce_poly(poly_add(tuple(4*x for x in w), tuple(-2*x for x in n)))
                for w, n in zip(weights, numerators)]
        self.assertEqual(gaps, [(4, 4, -2), (4, 4, 2), (4, 4, 2)])
        # c=0: (beta+2)/(4 beta) < 1/2; c=1 gap = 2 beta^3; c=2 bound = 1/4.
        self.assertEqual(numerators[2], weights[2])
        self.assertEqual(poly_multiply((0, 1), numerators[0]),
                         poly_multiply(weights[0], F[0]))
        for c, w in enumerate(weights):
            upper = BETA_HI**2 * evaluate(F[c], BETA_HI) / (4 * evaluate(w, BETA_LO))
            self.assertLess(upper, Q(1, 2))
        # Neither equality with these upper bounds nor a tile-area value is asserted.

    def test_first_level_half_bound_is_not_strict(self):
        _, _, _, counts, _ = literal_table(SIGMA, 1)
        zero = (Q(0), Q(0), Q(0))
        one = (Q(1, 2), Q(0), Q(1, 2))
        self.assertEqual(counts[1, zero], [1, 1, 1])
        self.assertEqual(counts[2, one], [0, 1, 0])
        for c, r in ((1, zero), (2, one)):
            self.assertEqual(weighted(counts[c, r]), poly_multiply((0, 1), F[c]))

    def test_exact_residue_refinement_consistency(self):
        for q in range(1, 6):
            _, _, coarse_inverse, coarse, _ = literal_table(SIGMA, q)
            _, _, _, fine, representatives = literal_table(SIGMA, q + 1)
            sums = defaultdict(lambda: (0, 0, 0))
            for (c, r), a in fine.items():
                key = (c, residue(coarse_inverse, representatives[c, r]))
                sums[key] = poly_add(sums[key], weighted(a))
            self.assertEqual(set(sums), set(coarse))
            for key, a in coarse.items():
                self.assertEqual(reduce_poly(sums[key]), poly_multiply((0, 1), weighted(a)))

    def test_unimodular_quotient_is_trivial(self):
        for q in (1, 2, 4):
            _, matrix, _, counts, _ = literal_table(("01", "12", "021"), q)
            self.assertEqual({r for _, r in counts}, {(Q(0), Q(0), Q(0))})
            for c in range(3):
                self.assertEqual(counts[c, (Q(0), Q(0), Q(0))], list(matrix[c]))
        # The general formula then gives beta^q f_c/(M^q f)_c = 1.

    def test_word_order_cannot_be_recovered_from_incidence(self):
        changed = ("1", "012", "001")
        self.assertEqual(incidence(changed), incidence(SIGMA))
        original = literal_table(SIGMA, 2)[3]
        altered = literal_table(changed, 2)[3]
        self.assertNotEqual(original, altered)
        self.assertEqual(original[0, (Q(0), Q(0), Q(0))], [1, 1, 1])
        self.assertEqual(altered[0, (Q(0), Q(0), Q(0))], [1, 0, 1])

    def test_literal_strong_coincidence_witnesses(self):
        witnesses = ((1, 2, 1, 0, (0, 0, 0), "0"),
                     (0, 1, 5, 31, (12, 13, 6), "1"),
                     (0, 2, 6, 31, (12, 13, 6), "1"))
        for a, b, q, i, prefix, letter in witnesses:
            words = literal_table(SIGMA, q)[0]
            self.assertEqual(words[a][i], letter)
            self.assertEqual(words[b][i], letter)
            self.assertEqual(tuple(words[a][:i].count(str(c)) for c in range(3)), prefix)
            self.assertEqual(tuple(words[b][:i].count(str(c)) for c in range(3)), prefix)

    def test_invalid_or_exhausted_inputs_refuse(self):
        for sigma, q, cap in ((SIGMA, -1, 100), (SIGMA, 11, 100000),
                              (SIGMA, 2, 6), (("1", "", "001"), 2, 100),
                              (("1", "023", "001"), 2, 100),
                              (("012", "120", "201"), 2, 100)):
            with self.assertRaises(ValueError):
                literal_table(sigma, q, cap)


if __name__ == "__main__":
    unittest.main()
