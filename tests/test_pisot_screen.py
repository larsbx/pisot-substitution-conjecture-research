"""Conformance of the degree-`n` Pisot screen."""

from __future__ import annotations

import random
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from psc_research import pisot_screen as ps  # noqa: E402

# Pisot numbers, by minimal polynomial, low-degree-first.
GOLDEN = [-1, -1, 1]              # x^2 - x - 1,        1.618...
SILVER = [-1, -2, 1]              # x^2 - 2x - 1,       2.414...
GOLDEN_SQUARED = [1, -3, 1]       # x^2 - 3x + 1,       2.618..., reciprocal pair
TWO_PLUS_ROOT_THREE = [1, -4, 1]  # x^2 - 4x + 1,       3.732..., reciprocal pair
PLASTIC = [-1, -1, 0, 1]          # x^3 - x - 1,        1.3247..., smallest Pisot
TRIBONACCI = [-1, -1, -1, 1]      # x^3 - x^2 - x - 1,  1.839...
QUARTIC = [-1, 0, 0, -1, 1]       # x^4 - x^3 - 1,      1.380...

SALEM = [1, -1, -1, -1, 1]        # conjugates on the unit circle, not Pisot
CYCLOTOMIC = [1, 0, 0, 0, 1]      # every root on the unit circle


def _roots(coeffs, iterations: int = 700):
    """Durand-Kerner, used only as an independent oracle in tests."""
    n = len(coeffs) - 1
    values = [complex(c) for c in coeffs]
    guesses = [(0.4 + 0.9j) ** k for k in range(n)]

    def at(x: complex) -> complex:
        acc = 0j
        for c in reversed(values):
            acc = acc * x + c
        return acc

    for _ in range(iterations):
        nxt = []
        for i, zi in enumerate(guesses):
            d = 1 + 0j
            for j, zj in enumerate(guesses):
                if i != j:
                    d *= zi - zj
            nxt.append(zi - at(zi) / d if abs(d) > 1e-300 else zi)
        guesses = nxt
    return guesses


def _oracle(coeffs, tol: float = 1e-6) -> str:
    roots = _roots(coeffs)
    if any(abs(abs(z) - 1) <= tol for z in roots):
        return ps.NOT_PISOT                  # a conjugate on the circle disqualifies
    outside = [z for z in roots if abs(z) > 1 + tol]
    if len(outside) != 1:
        return ps.NOT_PISOT
    beta = outside[0]
    return ps.PISOT if abs(beta.imag) < 1e-6 and beta.real > 1 else ps.NOT_PISOT


# --- the pinned classifications -------------------------------------------------


def test_known_pisot_minimal_polynomials():
    for coeffs in (GOLDEN, SILVER, GOLDEN_SQUARED, TWO_PLUS_ROOT_THREE,
                   PLASTIC, TRIBONACCI, QUARTIC, [-2, 1]):
        assert ps.screen(coeffs) == ps.PISOT, coeffs


def test_reciprocal_pisot_polynomials_are_not_refused():
    # Both have root pairs {beta, 1/beta}, which empties a Routh row. Without
    # the auxiliary-derivative rule the array stops and these are refused,
    # although 2.618... and 3.732... are perfectly ordinary Pisot numbers.
    for coeffs in (GOLDEN_SQUARED, TWO_PLUS_ROOT_THREE):
        assert ps.routh_right_half_plane_count(ps.halfplane_transform(coeffs)) == 1
        assert ps.screen(coeffs) == ps.PISOT


def test_a_conjugate_on_the_unit_circle_is_not_pisot():
    # The Routh count alone reports one root outside for a Salem polynomial and
    # would call it Pisot; the unit-circle test is what refuses it.
    for coeffs in (SALEM, CYCLOTOMIC, [1, 0, 1], [-1, 0, 1]):
        assert ps.has_root_on_unit_circle(coeffs), coeffs
        assert ps.screen(coeffs) == ps.NOT_PISOT, coeffs
    assert ps.roots_outside_unit_circle(SALEM) == 1


def test_non_pisot_classifications():
    for coeffs in ([-3, -1, 1],        # x^2 - x - 3, conjugate outside
                   [-3, 0, 1],         # x^2 - 3, both roots outside
                   [2, 1],             # x + 2, the lone root is below -1
                   [1, 1]):            # x + 1, root on the circle
        assert ps.screen(coeffs) == ps.NOT_PISOT, coeffs


def test_the_screen_refuses_what_it_cannot_accept():
    for coeffs in ([1, 2],             # not monic
                   [3],                # degree zero
                   []):                # empty
        assert ps.screen(coeffs) == ps.REFUSED, coeffs


# --- the method -----------------------------------------------------------------


def test_the_transform_sends_the_unit_circle_to_the_imaginary_axis():
    for coeffs in (GOLDEN, PLASTIC, TRIBONACCI, QUARTIC, SALEM):
        q = ps.halfplane_transform(coeffs)
        for z in _roots(coeffs):
            if abs(z + 1) < 1e-9:
                continue                     # z = -1 maps to infinity
            w = (z - 1) / (z + 1)
            value = sum(complex(c) * w ** k for k, c in enumerate(q))
            assert abs(value) < 1e-6, (coeffs, z)


def test_the_count_outside_matches_an_independent_root_finder():
    for coeffs in (GOLDEN, SILVER, PLASTIC, TRIBONACCI, QUARTIC, [-3, 0, 1], [-1, 2, 1]):
        outside = ps.roots_outside_unit_circle(coeffs)
        if outside is None:
            continue
        expected = sum(1 for z in _roots(coeffs) if abs(z) > 1 + 1e-6)
        assert outside == expected, coeffs


def test_the_screen_agrees_with_the_root_finder_on_random_polynomials():
    random.seed(31)
    agreed = pisot = refused = 0
    for _ in range(300):
        n = random.randint(1, 6)
        coeffs = [random.randint(-4, 4) for _ in range(n)] + [1]
        if coeffs[0] == 0:
            continue
        verdict = ps.screen(coeffs)
        if verdict == ps.REFUSED:
            refused += 1
            continue
        assert verdict == _oracle(coeffs), coeffs
        agreed += 1
        pisot += verdict == ps.PISOT
    assert agreed > 250 and pisot > 20 and refused < 40


def test_a_refusal_is_never_a_negative_result():
    assert ps.screen([1, 2]) == ps.REFUSED
    assert ps.screen([1, 2]) != ps.NOT_PISOT
    assert not ps.refusal_means_not_pisot()


# --- irreducibility, decided only where the test can decide it ------------------


def test_irreducibility_is_decided_below_degree_four_and_refused_above():
    assert ps.irreducibility(GOLDEN) == "irreducible"
    assert ps.irreducibility(PLASTIC) == "irreducible"
    assert ps.irreducibility([-2, 1]) == "reducible"          # x - 2 has a rational root
    assert ps.irreducibility([0, -1, 1]) == "reducible"       # x^2 - x = x(x - 1)
    # A product of two irreducible quadratics has no rational root, so the
    # rational-root test proves nothing at degree four.
    assert ps.irreducibility([1, 0, 2, 0, 1]) == "refused"    # (x^2 + 1)^2
    assert ps.irreducibility(SALEM) == "refused"
    assert not ps.screen_decides_irreducibility()


def test_screening_and_irreducibility_are_independent():
    # Pisot root location, but reducible over the rationals.
    assert ps.screen([-2, 1]) == ps.PISOT
    assert ps.irreducibility([-2, 1]) == "reducible"
