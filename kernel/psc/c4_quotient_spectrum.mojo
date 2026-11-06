"""Quotient spectrum of the Parikh span of a child-closed balanced-pair system.

Contract (docs/c4-general-structure-2026-11-06.md, Proposition Q). For a
finite child-closed system `C` of a primitive substitution on three letters,
the span `V` of the state Parikh vectors is `M`-invariant (`P N = M P`), and
every root of the characteristic polynomial of `M` on `Q^3 / V` is 0 or a root
of unity. This module computes that quotient polynomial with integers only:

* rank 1: `V = Q p` with `M p = lambda p`; the quotient is `chi_M / (x - lambda)`;
* rank 2: `V = ker(n)` with `n = p x q`; `n` is a left eigenvector, `n M = mu n`,
  and the quotient is `x - mu`;
* rank 3: the quotient is trivial.

A failed invariance (a non-integral eigenvalue, a nonzero remainder, a left
vector that is not an eigenvector) raises: on a child-closed system Proposition
Q(a) makes it impossible, so it signals a malformed input (fail closed).
Coefficients are leading first. No C4, PSC or PDS inference is made.
"""

from psc.bpa import substitution_incidence
from psc.c4_cut_attractor import StrictClosure, parikh_matrix


def _cross(p: List[Int], q: List[Int]) -> List[Int]:
    return [p[1] * q[2] - p[2] * q[1], p[2] * q[0] - p[0] * q[2], p[0] * q[1] - p[1] * q[0]]


def _is_zero(v: List[Int]) -> Bool:
    return v[0] == 0 and v[1] == 0 and v[2] == 0


def _dot(a: List[Int], b: List[Int]) -> Int:
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def _column(P: List[List[Int]], s: Int) -> List[Int]:
    return [P[0][s], P[1][s], P[2][s]]


def parikh_span_basis(c: StrictClosure) raises -> List[List[Int]]:
    """An integer basis of the span of the state Parikh vectors (1 to 3 vectors)."""
    var P = parikh_matrix(c)
    var basis = List[List[Int]]()
    for s in range(c.size()):
        var v = _column(P, s)
        if _is_zero(v):
            raise Error("a state has an empty Parikh vector")
        if len(basis) == 0:
            basis.append(v^)
        elif len(basis) == 1:
            if not _is_zero(_cross(basis[0], v)):
                basis.append(v^)
        elif len(basis) == 2:
            if _dot(_cross(basis[0], basis[1]), v) != 0:
                basis.append(v^)
    return basis^


def quotient_charpoly(sigma: List[List[Int]], c: StrictClosure) raises -> List[Int]:
    """Characteristic polynomial of `M` on `Q^3 / V`, leading coefficient first."""
    var m = substitution_incidence(sigma)
    var basis = parikh_span_basis(c)
    var rank = len(basis)
    if rank == 3:
        return [1]
    if rank == 2:
        var n = _cross(basis[0], basis[1])
        var nm: List[Int] = [0, 0, 0]
        for j in range(3):
            for i in range(3):
                nm[j] += n[i] * m[3 * i + j]
        var k = 0
        while n[k] == 0:
            k += 1
        if nm[k] % n[k] != 0:
            raise Error("quotient eigenvalue is not an integer: the span is not invariant")
        var mu = nm[k] // n[k]
        for j in range(3):
            if nm[j] != mu * n[j]:
                raise Error("normal vector is not a left eigenvector: the span is not invariant")
        return [1, -mu]
    var p = basis[0].copy()
    var mp: List[Int] = [0, 0, 0]
    for i in range(3):
        for j in range(3):
            mp[i] += m[3 * i + j] * p[j]
    var k = 0
    while p[k] == 0:
        k += 1
    if mp[k] % p[k] != 0:
        raise Error("Parikh vector is not an integral eigenvector: the span is not invariant")
    var lam = mp[k] // p[k]
    for i in range(3):
        if mp[i] != lam * p[i]:
            raise Error("Parikh vector is not an eigenvector: the span is not invariant")
    # chi_M = x^3 + a2 x^2 + a1 x + a0
    var trace = m[0] + m[4] + m[8]
    var minors = (m[0] * m[4] - m[1] * m[3]) + (m[0] * m[8] - m[2] * m[6]) + (m[4] * m[8] - m[5] * m[7])
    var det = (m[0] * (m[4] * m[8] - m[5] * m[7]) - m[1] * (m[3] * m[8] - m[5] * m[6])
               + m[2] * (m[3] * m[7] - m[4] * m[6]))
    var a2 = -trace
    var a1 = minors
    var a0 = -det
    var b1 = a2 + lam
    var b0 = a1 + lam * b1
    if a0 + lam * b0 != 0:
        raise Error("the Perron factor does not divide chi_M: inconsistent input")
    return [1, b1, b0]


def is_neutral(poly: List[Int]) raises -> Bool:
    """Whether every root of a monic integer polynomial of degree at most 2 is
    0 or a root of unity: a product of `x` and the cyclotomic polynomials of
    degree at most 2."""
    if len(poly) == 0 or poly[0] != 1 or len(poly) > 3:
        raise Error("expected a monic polynomial of degree at most 2")
    if len(poly) == 1:
        return True
    if len(poly) == 2:
        return poly[1] == 0 or poly[1] == 1 or poly[1] == -1
    var c1 = poly[1]
    var c0 = poly[2]
    var allowed: List[List[Int]] = [
        [0, 0], [-1, 0], [1, 0], [-2, 1], [2, 1], [0, -1], [1, 1], [0, 1], [-1, 1],
    ]
    for pair in allowed:
        if pair[0] == c1 and pair[1] == c0:
            return True
    return False
