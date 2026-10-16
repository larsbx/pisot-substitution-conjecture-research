"""Exact equivalence and refusal controls for the integer-root shortcut."""
from cProfile import Profile
from fractions import Fraction
from itertools import product

import pytest
from psc_research import pisot_screen as ps


def reference_root(coeffs):
    """Original sorted divisor traversal, ordinary Fraction Horner (no fast path)."""
    if coeffs[0] == 0:
        return True
    value = abs(coeffs[0])
    divisors = set()
    d = 1
    while d * d <= value:
        if value % d == 0:
            divisors.update((d, value // d))
        d += 1
    for divisor in sorted(divisors):
        for x in (Fraction(divisor), Fraction(-divisor)):
            acc = Fraction(0)
            for c in reversed(coeffs):
                acc = acc * x + c
            if acc == 0:
                return True
    return False


@pytest.mark.parametrize('coeffs,expected', [
    ([-6, -1, 1], True),       # positive root 3 and negative root -2
    ([6, 5, 1], True),         # negative roots only
    ([0, -7, 0, 1], True),
    ([49, -14, 1], True),      # repeated root at square divisor
    ([-1000003, 1000003, -1, 1], True),  # small root, large prime constant
    ([-1000003, 1, -1000003, 1], True),  # large complementary divisor
    ([1000003, 1, 1000003, 1], True),    # negative complementary divisor
    ([-1, -1, 1], False), ([-1, -1, 0, 1], False),
    ([1, 0, 2, 0, 1], False),  # reducible, no linear factor
    ([-1, 0, 0, -1, 1], False),
    ([5040, -100, 20, -5, 1], False),
    ([36, 0, 1], False),
    ([1, 2**100, 1], False),   # unbounded intermediate arithmetic
])
def test_root_edge_cases(coeffs, expected):
    for padding in ([], [0, 0]):
        p = coeffs + padding
        snapshot = p.copy()
        assert ps._has_rational_root(p) == reference_root(p) == expected
        assert p == snapshot


def test_deterministic_grid_and_irreducibility():
    # 7^1 + ... + 7^5 = 19,607 monic polynomials, both padded and unpadded.
    optimized = ps._has_rational_root
    for degree in range(1, 6):
        for c in product(range(-3, 4), repeat=degree):
            p = list(c) + [1]
            expected = reference_root(p)
            assert optimized(p) == optimized(p + [0, 0]) == expected, p
            verdict = ('irreducible' if degree == 1 else
                       'reducible' if expected else
                       'irreducible' if degree <= 3 else 'refused')
            assert ps.irreducibility(p) == verdict, p


def test_int_subclass_arithmetic_keeps_exact_fallback():
    class Trap(int):
        def __radd__(self, other):
            raise AssertionError('native subclass addition')
        def __mul__(self, other):
            raise AssertionError('native subclass multiplication')

    for p in ([-6, -1, 1], [-1, -1, 1], [6, 5, 1]):
        wrapped = [Trap(c) for c in p]
        assert ps.is_monic_integer(wrapped)
        assert ps._has_rational_root(wrapped) == reference_root(wrapped)
        assert ps.irreducibility(wrapped) == ps.irreducibility(p)
    assert ps._has_rational_root([True, False, True]) is False


def test_fail_closed_boundaries():
    for p in ([], [0], [1], [1, 2], [1, Fraction(1)], [1, 1.0]):
        assert ps.irreducibility(p) == ps.REFUSED
        assert ps.screen(p) == ps.REFUSED
    for p in ([1, 0, 2, 0, 1], [-1, 0, 0, -1, 1]):
        assert ps.irreducibility(p) == ps.REFUSED
    assert ps.screen(ps.known_first_column_refusal()) == ps.REFUSED
    assert ps.screen([1, -1, -1, -1, 1]) == ps.NOT_PISOT


def test_plain_integer_path_avoids_fraction_construction():
    # An algorithmic-work regression that fails on main, never a timing gate.
    with Profile() as profile:
        assert not ps._has_rational_root([5040, -100, 20, -5, 1])
    assert not any(entry.code is Fraction.__new__.__code__
                   for entry in profile.getstats())
