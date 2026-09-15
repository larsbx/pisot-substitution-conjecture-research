"""Exact Sturm--Tarski queries at real roots, over unbounded rationals.

Polynomials are `List[Q]`, low degree first.  For a squarefree integer
polynomial `P` and any `Qp`, `tarski_query(P, Qp, a, b)` returns the sum over
the real roots `r` of `P` in `(a, b)` of `sign(Qp(r))` (the Cauchy index of
`P' Qp / P`), computed from the signed-remainder sequence of `(P, P' Qp)`;
`a`, `b` must not be roots of `P`, which holds for rational endpoints and an
irreducible `P`.  With `Qp = 1` it counts the roots; on an isolating interval
it is the sign of `Qp` at that root.  `sign_at_perron` covers the Perron root
only; this module serves the two real contracting conjugates of a totally
real cubic Pisot field.  Every operation is exact; a rejected rational
raises (AGENTS.md rules 8 and 9)."""

from finite_exact.rat_q import Q
from psc.exact import midpoint, q_int, q_is_zero, q_poly, q_sign, require_q


def poly_trim(p: List[Q]) -> List[Q]:
    var out = p.copy()
    while len(out) > 0 and q_is_zero(out[len(out) - 1]):
        _ = out.pop()
    return out^


def poly_eval(p: List[Q], x: Q) raises -> Q:
    var acc = Q.zero()
    for i in range(len(p) - 1, -1, -1):
        acc = require_q(acc.mul(x).add(p[i]), "poly eval")
    return acc^


def poly_deriv(p: List[Q]) raises -> List[Q]:
    var out = List[Q]()
    for i in range(1, len(p)):
        out.append(require_q(p[i].mul(q_int(i)), "poly deriv"))
    return poly_trim(out)


def poly_mul(p: List[Q], q: List[Q]) raises -> List[Q]:
    if len(p) == 0 or len(q) == 0:
        return List[Q]()
    var out = List[Q]()
    for _ in range(len(p) + len(q) - 1):
        out.append(Q.zero())
    for i in range(len(p)):
        for j in range(len(q)):
            out[i + j] = require_q(out[i + j].add(p[i].mul(q[j])), "poly mul")
    return poly_trim(out)


def poly_rem(p: List[Q], q: List[Q]) raises -> List[Q]:
    """Remainder of `p` modulo a nonzero `q`."""
    var r = poly_trim(p)
    var qq = poly_trim(q)
    if len(qq) == 0:
        raise Error("polynomial remainder by zero")
    var dq = len(qq) - 1
    var lead = qq[dq].copy()
    while len(r) > dq:
        var dr = len(r) - 1
        var k = require_q(r[dr].div(lead), "poly rem")
        for i in range(len(qq)):
            r[dr - dq + i] = require_q(r[dr - dq + i].sub(k.mul(qq[i])), "poly rem")
        r = poly_trim(r)
    return r^


def _variations(seq: List[List[Q]], x: Q) raises -> Int:
    var prev = 0
    var count = 0
    for i in range(len(seq)):
        var s = q_sign(poly_eval(seq[i], x))
        if s == 0:
            continue
        if prev != 0 and s != prev:
            count += 1
        prev = s
    return count


def tarski_query(P: List[Q], Qp: List[Q], a: Q, b: Q) raises -> Int:
    """Sum of `sign(Qp(r))` over the real roots `r` of `P` in `(a, b)`."""
    if not a.lt(b):
        raise Error("Tarski query needs a < b")
    var p0 = poly_trim(P)
    if len(p0) < 2:
        raise Error("Tarski query needs a nonconstant P")
    if q_is_zero(poly_eval(p0, a)) or q_is_zero(poly_eval(p0, b)):
        raise Error("Tarski query endpoint is a root of P")
    var seq = List[List[Q]]()
    seq.append(p0.copy())
    var f1 = poly_mul(poly_deriv(p0), Qp)
    if len(f1) == 0:
        return 0
    seq.append(f1^)
    while True:
        var r = poly_rem(seq[len(seq) - 2], seq[len(seq) - 1])
        if len(r) == 0:
            break
        for i in range(len(r)):
            r[i] = r[i].neg()
        seq.append(r^)
    return _variations(seq, a) - _variations(seq, b)


def count_real_roots(P: List[Q], a: Q, b: Q) raises -> Int:
    var one = List[Q]()
    one.append(Q.one())
    return tarski_query(P, one, a, b)


def isolate_real_roots(P: List[Q], a: Q, b: Q, expected: Int) raises -> List[List[Q]]:
    """Isolating rational brackets for the real roots of `P` in `(a, b)`.

    Bisects until each bracket holds one root and raises if the count of
    roots in `(a, b)` is not `expected` (fail closed)."""
    if count_real_roots(P, a, b) != expected:
        raise Error("unexpected number of real roots in the isolation interval")
    var stack = List[List[Q]]()
    var first = List[Q]()
    first.append(a.copy())
    first.append(b.copy())
    stack.append(first^)
    var out = List[List[Q]]()
    while len(stack) > 0:
        var box = stack.pop()
        var n = count_real_roots(P, box[0], box[1])
        if n == 0:
            continue
        if n == 1:
            out.append(box^)
            continue
        var mid = midpoint(box[0], box[1])
        if q_is_zero(poly_eval(P, mid)):
            raise Error("rational root during isolation")
        var left = List[Q]()
        left.append(box[0].copy())
        left.append(mid.copy())
        var right = List[Q]()
        right.append(mid.copy())
        right.append(box[1].copy())
        stack.append(left^)
        stack.append(right^)
    if len(out) != expected:
        raise Error("root isolation produced the wrong number of brackets")
    return out^


def sign_at_isolated_root(P: List[Q], Qp: List[Q], lo: Q, hi: Q) raises -> Int:
    """Sign of `Qp` at the unique root of `P` in `(lo, hi)`; `0` iff `Qp(r) = 0`."""
    var s = tarski_query(P, Qp, lo, hi)
    if s < -1 or s > 1:
        raise Error("sign query did not isolate one root")
    return s
