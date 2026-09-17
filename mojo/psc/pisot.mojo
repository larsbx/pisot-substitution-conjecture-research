"""An exact decision procedure for the standing PIP regime.

A substitution sigma on `{1,2,3}` is *primitive irreducible Pisot* when its
incidence matrix `M` is a primitive non-negative integer matrix whose
characteristic polynomial is irreducible over Q and whose Perron root beta > 1
is Pisot (all other conjugates in the open unit disc).

Every test here is exact: rational-root enumeration for irreducibility, Sturm
sequences over Q for real-root location, and an exact determinant identity for
the complex-conjugate case. No floating point is used anywhere; rationals are
the unbounded `finite_exact` values, so no coefficient growth can overflow.
"""

from finite_exact.rat_q import Q
from psc.exact import q_floor_abs, q_int, q_is_zero, q_poly, q_sign
from finite_linear_algebra.mat3 import Mat3, has_rational_root


def poly_eval(p: List[Q], x: Q) -> Q:
    """Horner evaluation; `p` is low-degree-first."""
    var acc = Q.zero()
    for i in range(len(p) - 1, -1, -1):
        acc = acc.mul(x).add(p[i])
    return acc^


def poly_degree(p: List[Q]) -> Int:
    for i in range(len(p) - 1, -1, -1):
        if not q_is_zero(p[i]):
            return i
    return -1


def poly_derivative(p: List[Q]) -> List[Q]:
    var out = List[Q]()
    for i in range(1, len(p)):
        out.append(p[i].mul(q_int(i)))
    if len(out) == 0:
        out.append(Q.zero())
    return out^


def poly_rem(a: List[Q], b: List[Q]) -> List[Q]:
    """Remainder of `a` on division by `b` over Q."""
    var r = a.copy()
    var db = poly_degree(b)
    if db < 0:
        return r^
    while True:
        var dr = poly_degree(r)
        if dr < db:
            return r^
        var f = r[dr].div(b[db])
        for i in range(db + 1):
            r[dr - db + i] = r[dr - db + i].sub(f.mul(b[i]))
        r[dr] = Q.zero()


def sturm_chain(p: List[Q]) -> List[List[Q]]:
    """`p_0 = p`, `p_1 = p'`, `p_{k+1} = -rem(p_{k-1}, p_k)`."""
    var chain = List[List[Q]]()
    chain.append(p.copy())
    chain.append(poly_derivative(p))
    while poly_degree(chain[len(chain) - 1]) > 0:
        var r = poly_rem(chain[len(chain) - 2], chain[len(chain) - 1])
        var neg = List[Q]()
        for i in range(len(r)):
            neg.append(r[i].neg())
        if poly_degree(neg) < 0:
            break
        chain.append(neg^)
    return chain^


def _sign_changes(chain: List[List[Q]], x: Q) -> Int:
    var last = 0
    var count = 0
    for i in range(len(chain)):
        var s = q_sign(poly_eval(chain[i], x))
        if s == 0:
            continue
        if last != 0 and s != last:
            count += 1
        last = s
    return count


def count_roots_in(p: List[Q], a: Q, b: Q) -> Int:
    """Number of distinct real roots of `p` in the half-open interval `(a, b]`."""
    var chain = sturm_chain(p)
    return _sign_changes(chain, a) - _sign_changes(chain, b)


def cauchy_bound(p: List[Q]) -> Q:
    """A rational `B` with every real root of monic `p` strictly inside `(-B, B)`."""
    var d = poly_degree(p)
    var m = Q.zero()
    for i in range(d):
        var q = q_floor_abs(p[i].div(p[d])).add(Q.one())
        if m.lt(q):
            m = q^
    return m.add(q_int(2))


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
    var p = q_poly(coeffs)
    var b = cauchy_bound(p)
    var one = Q.one()
    var minus_one = one.neg()
    var nreal = count_roots_in(p, b.neg(), b)
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
    return q_sign(poly_eval(p, q_int(det))) < 0


struct CubicKey(ImplicitlyCopyable, Copyable, Movable, Equatable, Hashable):
    """A monic integer cubic `c0 + c1 x + c2 x^2 + x^3` as a dictionary key."""

    var c0: Int
    var c1: Int
    var c2: Int

    def __init__(out self, coeffs: List[Int]):
        self.c0 = coeffs[0]
        self.c1 = coeffs[1]
        self.c2 = coeffs[2]

    def __eq__(self, other: CubicKey) -> Bool:
        return self.c0 == other.c0 and self.c1 == other.c1 and self.c2 == other.c2

    def __ne__(self, other: CubicKey) -> Bool:
        return not (self == other)


struct CubicScreen(Copyable, Movable):
    """`is_pip` with the two characteristic-polynomial tests memoized.

    Primitivity is a property of the matrix, but irreducibility and the Pisot
    property are functions of the characteristic polynomial alone. Those two
    are the expensive half: rational-root enumeration and Sturm sequences over
    unbounded rationals. Screening the standing corpus evaluates them on
    33,318 primitive candidates that carry only 177 distinct cubics, so the
    verdict is decided once per cubic and reused.

    This changes no verdict. It is the same exact decision procedure, asked
    once per distinct question instead of once per candidate, so a memoized
    screen and a bare `is_pip` accept exactly the same matrices; the
    regression in `test_census_library.mojo` pins that.
    """

    var verdicts: Dict[CubicKey, Bool]

    def __init__(out self):
        self.verdicts = Dict[CubicKey, Bool]()

    def accepts_cubic(mut self, coeffs: List[Int]) raises -> Bool:
        """Whether the cubic is irreducible with a Pisot Perron root."""
        var key = CubicKey(coeffs)
        if key in self.verdicts:
            return self.verdicts[key]
        var verdict = is_irreducible_cubic(coeffs) and is_pisot_charpoly(coeffs)
        self.verdicts[key] = verdict
        return verdict

    def is_pip(mut self, m: Mat3) raises -> Bool:
        """Primitivity first, as in the free function: it is the cheap test and
        it rejects most candidates before any cubic work."""
        if not is_primitive(m):
            return False
        return self.accepts_cubic(m.charpoly())

    def distinct_cubics(self) -> Int:
        return len(self.verdicts)


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
