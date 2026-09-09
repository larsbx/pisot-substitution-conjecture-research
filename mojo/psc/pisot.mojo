"""An exact decision procedure for the standing PIP regime.

A substitution sigma on `{1,2,3}` is *primitive irreducible Pisot* when its
incidence matrix `M` is a primitive non-negative integer matrix whose
characteristic polynomial is irreducible over Q and whose Perron root beta > 1
is Pisot (all other conjugates in the open unit disc).

Every test here is exact: rational-root enumeration for irreducibility, Sturm
sequences over Q for real-root location, and an exact determinant identity for
the complex-conjugate case. No floating point is used anywhere.
"""

from psc.rational import Rat, rat_zero, rat_one
from psc.mat3 import Mat3, has_rational_root


def poly_eval(p: List[Rat], x: Rat) -> Rat:
    """Horner evaluation; `p` is low-degree-first."""
    var acc = rat_zero()
    for i in range(len(p) - 1, -1, -1):
        acc = acc * x + p[i]
    return acc


def poly_degree(p: List[Rat]) -> Int:
    for i in range(len(p) - 1, -1, -1):
        if not p[i].is_zero():
            return i
    return -1


def poly_derivative(p: List[Rat]) -> List[Rat]:
    var out = List[Rat]()
    for i in range(1, len(p)):
        out.append(p[i] * Rat(i, 1))
    if len(out) == 0:
        out.append(rat_zero())
    return out^


def poly_rem(a: List[Rat], b: List[Rat]) -> List[Rat]:
    """Remainder of `a` on division by `b` over Q."""
    var r = a.copy()
    var db = poly_degree(b)
    if db < 0:
        return r^
    while True:
        var dr = poly_degree(r)
        if dr < db:
            return r^
        var f = r[dr] / b[db]
        for i in range(db + 1):
            r[dr - db + i] = r[dr - db + i] - f * b[i]
        r[dr] = rat_zero()


def sturm_chain(p: List[Rat]) -> List[List[Rat]]:
    """`p_0 = p`, `p_1 = p'`, `p_{k+1} = -rem(p_{k-1}, p_k)`."""
    var chain = List[List[Rat]]()
    chain.append(p.copy())
    chain.append(poly_derivative(p))
    while poly_degree(chain[len(chain) - 1]) > 0:
        var r = poly_rem(chain[len(chain) - 2], chain[len(chain) - 1])
        var neg = List[Rat]()
        for i in range(len(r)):
            neg.append(-r[i])
        if poly_degree(neg) < 0:
            break
        chain.append(neg^)
    return chain^


def _sign_changes(chain: List[List[Rat]], x: Rat) -> Int:
    var last = 0
    var count = 0
    for i in range(len(chain)):
        var v = poly_eval(chain[i], x)
        if v.is_zero():
            continue
        var s = 1 if v.num > 0 else -1
        if last != 0 and s != last:
            count += 1
        last = s
    return count


def count_roots_in(p: List[Rat], a: Rat, b: Rat) -> Int:
    """Number of distinct real roots of `p` in the half-open interval `(a, b]`."""
    var chain = sturm_chain(p)
    return _sign_changes(chain, a) - _sign_changes(chain, b)


def cauchy_bound(p: List[Rat]) -> Rat:
    """A rational `B` with every real root of monic `p` strictly inside `(-B, B)`."""
    var d = poly_degree(p)
    var m = 0
    for i in range(d):
        var c = p[i] / p[d]
        var a = c.num if c.num >= 0 else -c.num
        var q = a // c.den + 1
        if q > m:
            m = q
    return Rat(m + 2, 1)


def rat_poly(coeffs: List[Int]) -> List[Rat]:
    var out = List[Rat]()
    for i in range(len(coeffs)):
        out.append(Rat(coeffs[i], 1))
    return out^


def is_irreducible_cubic(coeffs: List[Int]) -> Bool:
    """A monic integer cubic is irreducible over Q iff it has no rational root."""
    return not has_rational_root(coeffs)


def is_nonnegative(m: Mat3) -> Bool:
    for i in range(9):
        if m.e[i] < 0:
            return False
    return True


def is_primitive(m: Mat3) -> Bool:
    """Some power of `m` is strictly positive. Wielandt: `k <= n^2 - 2n + 2 = 5`."""
    if not is_nonnegative(m):
        return False
    var p = m.copy()
    for _ in range(5):
        var pos = True
        for i in range(9):
            if p.e[i] <= 0:
                pos = False
        if pos:
            return True
        p = p * m
    return False


def is_pisot_charpoly(coeffs: List[Int]) -> Bool:
    """Exactly one root of the monic integer cubic lies outside the closed unit disc,
    and it is real and greater than 1.

    Case A (three real roots): decided entirely by Sturm counting.
    Case B (one real root, one conjugate pair): `beta * |beta_2|^2 = det`, so
    `|beta_2| < 1` iff `det < beta`, and since `beta` is the only real root that
    is equivalent to `chi(det) < 0`.
    """
    var p = rat_poly(coeffs)
    var b = cauchy_bound(p)
    var one = rat_one()
    var minus_one = -one
    var nreal = count_roots_in(p, -b, b)
    var above_one = count_roots_in(p, one, b)
    if above_one != 1:
        return False
    if nreal == 3:
        return count_roots_in(p, minus_one, one) == 2
    if nreal != 1:
        return False
    # det = -coeffs[0] for a monic cubic chi(t) = t^3 + c2 t^2 + c1 t + c0
    var det = -coeffs[0]
    if det <= 0:
        return False
    return poly_eval(p, Rat(det, 1)).num < 0


def is_pip(m: Mat3) -> Bool:
    """Primitive, irreducible characteristic cubic, Pisot Perron root."""
    var chi = m.charpoly()
    return is_primitive(m) and is_irreducible_cubic(chi) and is_pisot_charpoly(chi)


def has_equal_row_sums(m: Mat3) -> Bool:
    var s0 = m.at(0, 0) + m.at(0, 1) + m.at(0, 2)
    for i in range(1, 3):
        if m.at(i, 0) + m.at(i, 1) + m.at(i, 2) != s0:
            return False
    return True
