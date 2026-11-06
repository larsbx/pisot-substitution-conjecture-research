"""Independent exact oracle for Proposition Q (docs/c4-general-structure-2026-11-06.md):
the span V of the Parikh vectors of a finite child-closed balanced-pair system is
M-invariant, and every eigenvalue of M on Q^3/V is 0 or a root of unity.

The quotient is computed by an exact rational change of basis (a basis of V
extended by standard vectors) and the characteristic polynomial of the quotient
block -- a different construction from the integer cross-product route of
kernel/psc/c4_quotient_spectrum.mojo. Closures are built from scratch.
"""
import json
import os
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))

# the 28 relabelling x reversal classes of strict carriers with images of length <= 3,
# each with one state of its strict system (seed), its ordered size, rank P and quotient
# polynomial (coefficients, leading first)
CARRIERS = [
    ("01/12/01", "0112", "1201", 2, 1, [1, 0, 0]),
    ("01/120/112", "0112", "1120", 4, 2, [1, -1]),
    ("01/120/12", "0112", "1201", 3, 2, [1, -1]),
    ("01/2/120", "0012", "2001", 20, 3, [1]),
    ("01/2/201", "012", "201", 2, 1, [1, 0, 0]),
    ("01/20/10", "01", "10", 6, 2, [1, 0]),
    ("01/20/12", "012", "120", 2, 1, [1, 0, -1]),
    ("01/20/202", "012", "201", 3, 2, [1, -1]),
    ("01/201/112", "01112", "20111", 4, 2, [1, -1]),
    ("010/102/1", "01", "10", 4, 2, [1, -1]),
    ("010/102/102", "01", "10", 2, 2, [1, -1]),
    ("010/102/201", "01", "10", 4, 2, [1, -1]),
    ("010/121/010", "010121", "121010", 1, 1, [1, -1, 0]),
    ("010/122/01", "01", "10", 4, 2, [1, -1]),
    ("010/122/201", "01", "10", 9, 2, [1, -1]),
    ("010/2/102", "01", "10", 3, 2, [1, -1]),
    ("012/120/201", "012", "120", 3, 1, [1, 0, 0]),
    ("012/201/120", "012", "120", 6, 1, [1, 0, 0]),
    ("1/012/1", "01", "10", 4, 2, [1, 1]),
    ("1/012/101", "01", "10", 6, 2, [1, 1]),
    ("1/012/121", "01", "10", 6, 2, [1, 1]),
    ("1/02/021", "021", "102", 2, 1, [1, 1, 0]),
    ("1/020/020", "0201", "1020", 2, 1, [1, 1, 0]),
    ("101/012/101", "01", "10", 4, 2, [1, 1]),
    ("101/02/021", "01", "10", 6, 2, [1, 1]),
    ("101/020/020", "020101", "101020", 2, 1, [1, 1, 0]),
    ("102/02/10", "021", "102", 6, 2, [1, 1]),
    ("102/210/021", "021", "102", 3, 1, [1, 0, 0]),
]

def polymul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


# x^2 (x^12 - 1)^2, leading first: every monic integer polynomial of degree <= 2 whose
# roots are 0 or roots of unity divides it (the cyclotomic factors of degree <= 2 are
# Phi_1, Phi_2, Phi_3, Phi_4, Phi_6, all dividing x^12 - 1), and conversely
NEUTRAL_MULTIPLE = polymul(polymul([1, 0, 0], [1] + [0] * 11 + [-1]), [1] + [0] * 11 + [-1])


def divides(d, n):
    """Exact long division of n by the monic d (both leading first)."""
    assert d[0] == 1
    r = list(n)
    for i in range(len(n) - len(d) + 1):
        f = r[i]
        for j in range(len(d)):
            r[i + j] -= f * d[j]
    return all(x == 0 for x in r)


def parse(s):
    return [list(map(int, w)) for w in s.split("/")]


def apply(sig, w):
    out = []
    for a in w:
        out.extend(sig[a])
    return out


def parikh(w):
    p = [0, 0, 0]
    for a in w:
        p[a] += 1
    return tuple(p)


def factorise(u, v):
    out, pu, pv, start = [], [0, 0, 0], [0, 0, 0], 0
    for i in range(len(u)):
        pu[u[i]] += 1
        pv[v[i]] += 1
        if pu == pv:
            out.append((tuple(u[start:i + 1]), tuple(v[start:i + 1])))
            start = i + 1
    assert start == len(u)
    return out


def closure(sig, seed):
    states, idx, q = [seed], {seed: 0}, 0
    while q < len(states):
        u, v = states[q]
        q += 1
        for c in factorise(apply(sig, list(u)), apply(sig, list(v))):
            if c[0] == c[1]:
                raise ValueError("coincident factor")
            if c not in idx:
                idx[c] = len(states)
                states.append(c)
    return states


def incidence(sig):
    return [[sig[b].count(a) for b in range(3)] for a in range(3)]


def rref(rows):
    rows = [[Fr(x) for x in r] for r in rows]
    pivots, r = [], 0
    m = len(rows[0]) if rows else 0
    for c in range(m):
        p = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        inv = 1 / rows[r][c]
        rows[r] = [x * inv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        pivots.append(c)
        r += 1
    return rows[:r], pivots


def inverse(B):
    n = len(B)
    aug = [list(map(Fr, B[i])) + [Fr(int(i == j)) for j in range(n)] for i in range(n)]
    red, piv = rref(aug)
    assert piv[:n] == list(range(n)), "singular change of basis"
    return [row[n:] for row in red]


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def charpoly(A):
    """Leading-first coefficients of det(xI - A) for size 0, 1, 2."""
    n = len(A)
    if n == 0:
        return [Fr(1)]
    if n == 1:
        return [Fr(1), -A[0][0]]
    assert n == 2
    return [Fr(1), -(A[0][0] + A[1][1]), A[0][0] * A[1][1] - A[0][1] * A[1][0]]


def quotient_poly(sig, states):
    M = incidence(sig)
    cols = [list(parikh(u)) for (u, v) in states]
    # basis of V: independent columns, found by row reduction of the column matrix transposed
    basis = []
    for c in cols:
        if not basis or len(rref(basis + [c])[1]) > len(basis):
            basis.append(c)
    r = len(basis)
    full = list(basis)
    for j in range(3):
        e = [int(i == j) for i in range(3)]
        if len(rref(full + [e])[1]) > len(full):
            full.append(e)
    assert len(full) == 3
    B = [[full[k][i] for k in range(3)] for i in range(3)]   # columns = basis vectors
    T = matmul(inverse(B), matmul([[Fr(x) for x in row] for row in M], B))
    # V invariant: the lower-left block vanishes
    for i in range(r, 3):
        for j in range(r):
            assert T[i][j] == 0, "V is not M-invariant"
    block = [row[r:] for row in T[r:]]
    poly = charpoly(block)
    assert all(c.denominator == 1 for c in poly)
    return r, [int(c) for c in poly]


def neutral(poly):
    return divides(poly, NEUTRAL_MULTIPLE)


def test_quotient_spectrum_on_all_28_carrier_classes():
    ranks = {}
    for sigma, u, v, size, rank, poly in CARRIERS:
        sig = parse(sigma)
        states = closure(sig, (tuple(map(int, u)), tuple(map(int, v))))
        assert len(states) == size, sigma
        r, q = quotient_poly(sig, states)
        assert (r, q) == (rank, poly), (sigma, r, q)
        assert neutral(q), sigma
        ranks[r] = ranks.get(r, 0) + 1
    assert ranks == {1: 10, 2: 17, 3: 1}


def test_neutrality_by_division():
    for poly in ([1], [1, 0], [1, 1], [1, -1], [1, 0, 0], [1, -2, 1], [1, 2, 1], [1, 0, -1],
                 [1, 1, 1], [1, 0, 1], [1, -1, 1], [1, 1, 0], [1, -1, 0]):
        assert neutral(poly), poly
    for poly in ([1, -2], [1, 2], [1, -2, -2], [1, 0, -2], [1, -1, -1], [1, 3, 1], [1, 0, 2]):
        assert not neutral(poly), poly


def test_rank_three_strict_system_with_singular_incidence():
    sig = parse("01/2/120")
    states = closure(sig, ((0, 0, 1, 2), (2, 0, 0, 1)))
    assert len(states) == 20
    M = incidence(sig)
    assert M == [[1, 0, 1], [1, 0, 1], [0, 1, 1]]
    assert {parikh(u) for u, _ in states} >= {(1, 1, 1), (2, 1, 1), (1, 1, 2)}
    assert quotient_poly(sig, states) == (3, [1])


def test_proposition_q_fails_closed_on_a_non_invariant_span():
    # a set that is not child-closed need not have an invariant span: the check refuses it
    sig = parse("01/12/021")
    try:
        quotient_poly(sig, [((0, 1), (1, 0))])
    except AssertionError:
        pass
    else:
        raise AssertionError("non-invariant span accepted")
