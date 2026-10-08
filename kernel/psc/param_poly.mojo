"""Polynomials in two parameters `s, d` over Q, for `psc.symbolic_line`.

docs/p1c-symbolic-wedge-2026-10-08.md. A `P2` is `List[List[Q]]`: entry `j` is
the coefficient of `d^j`, itself a `qpoly` polynomial in `s` (ascending,
normalized); the list is normalized so its last entry is nonzero, and the
empty list is zero. A polynomial without `d` is a one-entry list, so a
one-parameter line (`q = s`) is the special case `d`-degree `0` and costs one
`qpoly` call per operation.

The one question asked of a `P2` beyond arithmetic is its sign on a quadrant
`{s > S, d > D}`; `quadrant_sign` answers it with a Polya certificate (all
coefficients of `(1 + u + v)^N P(S + u, D + v)` of one sign) or not at all.
"""

from finite_exact.rat_q import Q
from finite_linear_algebra.qpoly import add, evaluate, mul, neg, normalize, scale, sign_of
from finite_linear_algebra.scalar import q_int, q_is_zero
from psc.exact import q_string

comptime P2 = List[List[Q]]


def p2_norm(p: P2) -> P2:
    var width = len(p)
    while width > 0 and len(normalize(p[width - 1])) == 0:
        width -= 1
    var out = P2()
    for j in range(width):
        out.append(normalize(p[j]))
    return out^


def p2_is_zero(p: P2) -> Bool:
    return len(p2_norm(p)) == 0


def p2_from_s(f: List[Q]) -> P2:
    """A polynomial in `s` alone."""
    return p2_norm([f.copy()])


def p2_const(c: Int) -> P2:
    return p2_from_s([q_int(c)])


def p2_affine(c0: Int, cs: Int, cd: Int = 0) -> P2:
    """`c0 + cs s + cd d`."""
    return p2_norm([[q_int(c0), q_int(cs)], [q_int(cd)]])


def p2_coeff(p: P2, j: Int) -> List[Q]:
    if j < len(p):
        return p[j].copy()
    return List[Q]()


def p2_add(a: P2, b: P2) -> P2:
    var width = len(a) if len(a) > len(b) else len(b)
    var out = P2()
    for j in range(width):
        out.append(add(p2_coeff(a, j), p2_coeff(b, j)))
    return p2_norm(out)


def p2_scale(p: P2, c: Q) -> P2:
    var out = P2()
    for j in range(len(p)):
        out.append(scale(p[j], c))
    return p2_norm(out)


def p2_neg(p: P2) -> P2:
    var out = P2()
    for j in range(len(p)):
        out.append(neg(p[j]))
    return out^


def p2_sub(a: P2, b: P2) -> P2:
    return p2_add(a, p2_neg(b))


def p2_mul(a: P2, b: P2) -> P2:
    var x = p2_norm(a)
    var y = p2_norm(b)
    if len(x) == 0 or len(y) == 0:
        return P2()
    var out = P2()
    for _ in range(len(x) + len(y) - 1):
        out.append(List[Q]())
    for i in range(len(x)):
        for j in range(len(y)):
            out[i + j] = add(out[i + j], mul(x[i], y[j]))
    return p2_norm(out)


def p2_at(p: P2, s: Q, d: Q) -> Q:
    var total = Q.zero()
    for index in range(len(p)):
        total = total.mul(d).add(evaluate(p[len(p) - 1 - index], s))
    return total^


def p2_at_int(p: P2, s: Int, d: Int) -> Q:
    return p2_at(p, q_int(s), q_int(d))


def p2_has_d(p: P2) -> Bool:
    return len(p2_norm(p)) > 1


def p2_is_const(p: P2) -> Bool:
    var f = p2_norm(p)
    return len(f) == 0 or (len(f) == 1 and len(f[0]) <= 1)


def p2_const_value(p: P2) -> Q:
    """The value of a constant polynomial (zero for zero)."""
    var f = p2_norm(p)
    if len(f) == 0 or len(f[0]) == 0:
        return Q.zero()
    return f[0][0].copy()


def p2_key(p: P2) -> String:
    var out = String("")
    for j in range(len(p)):
        out += "{"
        for k in range(len(p[j])):
            out += q_string(p[j][k]) + ","
        out += "}"
    return out^


def _shift_s(f: List[Q], a: Q) -> List[Q]:
    """`f(a + u)` as a polynomial in `u` (Horner)."""
    var total = List[Q]()
    var lin = normalize([a.copy(), Q.one()])
    for index in range(len(f)):
        total = add(mul(total, lin), normalize([f[len(f) - 1 - index].copy()]))
    return total^


def p2_shift(p: P2, a: Q, b: Q) -> P2:
    """`p(a + u, b + v)` in the variables `(u, v)` (stored as `(s, d)`)."""
    var total = P2()
    var lin = p2_norm([[b.copy()], [Q.one()]])
    for index in range(len(p)):
        total = p2_add(p2_mul(total, lin), p2_from_s(_shift_s(p[len(p) - 1 - index], a)))
    return total^


def _one_sign(p: P2) -> Int:
    """`+1` or `-1` if every coefficient is `>= 0` (resp. `<= 0`) and `p != 0`, else `0`."""
    var pos = False
    var negs = False
    for j in range(len(p)):
        for k in range(len(p[j])):
            var s = sign_of(p[j][k])
            if s > 0:
                pos = True
            elif s < 0:
                negs = True
    if pos and not negs:
        return 1
    if negs and not pos:
        return -1
    return 0


def quadrant_sign(p: P2, a: Q, b: Q, polya: Int) -> Int:
    """A certified sign of `p` on the open quadrant `{s > a, d > b}`, or `0` for
    no certificate. With `u = s - a`, `v = d - b`: if every coefficient of
    `(1 + u + v)^N p(a + u, b + v)` has one sign for some `N <= polya`, then
    `p` has that sign wherever `u, v > 0` (every monomial is positive there,
    and the multiplier is). Sound, not complete."""
    var f = p2_shift(p, a, b)
    var mult = p2_affine(1, 1, 1)
    for _ in range(polya + 1):
        var s = _one_sign(f)
        if s != 0:
            return s
        f = p2_mul(f, mult)
    return 0
