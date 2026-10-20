"""Exact fixed-size multiplication contract for the independent Python oracle."""
from copy import deepcopy
from fractions import Fraction
from itertools import product
import random
from psc_research.pip_screen import mul


def original_mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(3)) for j in range(3)] for i in range(3)]


def check(a, b):
    snapshot = deepcopy((a, b))
    result = mul(a, b)
    assert result == original_mul(a, b)
    assert (a, b) == snapshot
    assert all(result[i] is not a[j] and result[i] is not b[j] for i in range(3) for j in range(3))


def test_basis_products():
    # Bilinearity plus all 81 basis pairs establishes the integer matrix map.
    basis = []
    for i, j in product(range(3), repeat=2):
        m = [[0] * 3 for _ in range(3)]
        m[i][j] = 1
        basis.append(m)
    for a, b in product(basis, repeat=2):
        check(a, b)


def test_signed_asymmetric_and_boundaries():
    big = 2**256
    matrices = [[[0]*3 for _ in range(3)], [[int(i == j) for j in range(3)] for i in range(3)],
                [[1, -2, 3], [4, 0, -6], [-7, 8, 9]],
                [[big, -big, 1], [0, big + 1, -1], [-big - 1, 2, big]],
                [[Fraction(i*3+j-4, j+2) for j in range(3)] for i in range(3)]]
    for a, b in product(matrices, repeat=2):
        check(a, b)
    rng = random.Random(250)
    for _ in range(1000):
        check(*[[[rng.randrange(-1000, 1001) for _ in range(3)] for _ in range(3)] for _ in range(2)])


def test_complete_ordered_corpus_equivalence(monkeypatch):
    from psc_research import pip_screen
    actual = pip_screen.pip_corpus()
    monkeypatch.setattr(pip_screen, 'mul', original_mul)
    assert actual == pip_screen.pip_corpus()
    assert len(actual) == 4554
