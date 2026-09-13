"""Exact cubic Perron-field arithmetic for the standing alphabet-three PIP regime.

Elements are stored in the integral power basis ``1, beta, beta^2`` modulo the
monic characteristic polynomial of the incidence matrix.  Order is evaluated
at the unique Perron root by exact Sturm isolation; no floating point or
Euclidean stable-space lattice is used.

This is executable finite-research arithmetic over Mojo ``Int``.  It is not an
unbounded-integer proof kernel: callers must not turn successful finite runs
into a universal overflow-safety claim.
"""

from psc.mat3 import Mat3
from psc.pisot import cauchy_bound, count_roots_in, is_pip, poly_eval, rat_poly
from psc.rational import Rat


struct CubicElt(ImplicitlyCopyable, Copyable, Movable, Equatable, Hashable, Writable):
    var a0: Int
    var a1: Int
    var a2: Int

    def __init__(out self, a0: Int = 0, a1: Int = 0, a2: Int = 0):
        self.a0 = a0
        self.a1 = a1
        self.a2 = a2

    def __eq__(self, other: CubicElt) -> Bool:
        return self.a0 == other.a0 and self.a1 == other.a1 and self.a2 == other.a2

    def __ne__(self, other: CubicElt) -> Bool:
        return not (self == other)

    def __add__(self, other: CubicElt) -> CubicElt:
        return CubicElt(self.a0 + other.a0, self.a1 + other.a1, self.a2 + other.a2)

    def __sub__(self, other: CubicElt) -> CubicElt:
        return CubicElt(self.a0 - other.a0, self.a1 - other.a1, self.a2 - other.a2)

    def __neg__(self) -> CubicElt:
        return CubicElt(-self.a0, -self.a1, -self.a2)

    def scale(self, n: Int) -> CubicElt:
        return CubicElt(n * self.a0, n * self.a1, n * self.a2)

    def is_zero(self) -> Bool:
        return self.a0 == 0 and self.a1 == 0 and self.a2 == 0

    def write_to[W: Writer](self, mut w: W):
        w.write("(", self.a0, ",", self.a1, ",", self.a2, ")")


struct PerronField3(ImplicitlyCopyable, Copyable, Movable):
    """One irreducible cubic field with a distinguished Pisot Perron root."""

    var chi0: Int
    var chi1: Int
    var chi2: Int

    def __init__(out self, chi0: Int, chi1: Int, chi2: Int):
        self.chi0 = chi0
        self.chi1 = chi1
        self.chi2 = chi2

    def charpoly(self) -> List[Int]:
        return [self.chi0, self.chi1, self.chi2, 1]


struct TileLengths3(ImplicitlyCopyable, Copyable, Movable):
    """Positive left-Perron tile lengths, up to one common positive scale."""

    var l0: CubicElt
    var l1: CubicElt
    var l2: CubicElt

    def __init__(out self, l0: CubicElt, l1: CubicElt, l2: CubicElt):
        self.l0 = l0
        self.l1 = l1
        self.l2 = l2

    def at(self, letter: Int) raises -> CubicElt:
        if letter == 0:
            return self.l0
        if letter == 1:
            return self.l1
        if letter == 2:
            return self.l2
        raise Error("tile-length letter lies outside 0..2")


def build_perron_field3(m: Mat3) raises -> PerronField3:
    if not is_pip(m):
        raise Error("cubic Perron field requires a primitive irreducible Pisot matrix")
    var chi = m.charpoly()
    return PerronField3(chi[0], chi[1], chi[2])


def cubic_mul_beta(field: PerronField3, x: CubicElt) -> CubicElt:
    """Multiply by beta using beta^3 = -chi2 beta^2 - chi1 beta - chi0."""
    return CubicElt(
        -field.chi0 * x.a2,
        x.a0 - field.chi1 * x.a2,
        x.a1 - field.chi2 * x.a2,
    )


def cubic_mul(field: PerronField3, x: CubicElt, y: CubicElt) -> CubicElt:
    var v: List[Int] = [
        x.a0 * y.a0,
        x.a0 * y.a1 + x.a1 * y.a0,
        x.a0 * y.a2 + x.a1 * y.a1 + x.a2 * y.a0,
        x.a1 * y.a2 + x.a2 * y.a1,
        x.a2 * y.a2,
    ]
    for degree in range(4, 2, -1):
        var c = v[degree]
        if c == 0:
            continue
        v[degree - 1] -= c * field.chi2
        v[degree - 2] -= c * field.chi1
        v[degree - 3] -= c * field.chi0
        v[degree] = 0
    return CubicElt(v[0], v[1], v[2])


def sign_at_perron(field: PerronField3, x: CubicElt) raises -> Int:
    """Return sign of x(beta) by exact rational isolation of the Perron root.

    A nonzero polynomial of degree at most two cannot vanish at the irreducible
    cubic beta.  We refine the unique root interval until the degree-two
    polynomial has no real root in it.  Failure to isolate inside the finite
    execution guard raises rather than guesses.
    """
    if x.is_zero():
        return 0

    var p = rat_poly(field.charpoly())
    var qints: List[Int] = [x.a0, x.a1, x.a2]
    var q = rat_poly(qints)
    var lo = Rat(1, 1)
    var hi = cauchy_bound(p)
    if count_roots_in(p, lo, hi) != 1:
        raise Error("Perron root isolation precondition failed")

    for _ in range(192):
        if count_roots_in(q, lo, hi) == 0:
            var value = poly_eval(q, hi)
            if value.num > 0:
                return 1
            if value.num < 0:
                return -1
            raise Error("Perron sign interval ended at an unexpected quadratic root")
        var mid = (lo + hi) / Rat(2, 1)
        var left = count_roots_in(p, lo, mid)
        if left == 1:
            hi = mid
        elif left == 0:
            lo = mid
        else:
            raise Error("Perron root interval lost uniqueness")
    raise Error("Perron sign isolation exceeded the finite refinement guard")


def _row_entry(m: Mat3, row: Int, col: Int) -> CubicElt:
    # Row of M^T - beta I.
    return CubicElt(m.at(col, row), -1 if row == col else 0, 0)


def _cross(
    field: PerronField3,
    a0: CubicElt,
    a1: CubicElt,
    a2: CubicElt,
    b0: CubicElt,
    b1: CubicElt,
    b2: CubicElt,
) -> TileLengths3:
    return TileLengths3(
        cubic_mul(field, a1, b2) - cubic_mul(field, a2, b1),
        cubic_mul(field, a2, b0) - cubic_mul(field, a0, b2),
        cubic_mul(field, a0, b1) - cubic_mul(field, a1, b0),
    )


def _all_zero(lengths: TileLengths3) -> Bool:
    return lengths.l0.is_zero() and lengths.l1.is_zero() and lengths.l2.is_zero()


def _negate_lengths(lengths: TileLengths3) -> TileLengths3:
    return TileLengths3(-lengths.l0, -lengths.l1, -lengths.l2)


def left_perron_tile_lengths(m: Mat3) raises -> TileLengths3:
    """Construct and verify a positive left Perron eigenvector exactly."""
    var field = build_perron_field3(m)
    var lengths = TileLengths3(CubicElt(), CubicElt(), CubicElt())
    var found = False
    for r in range(3):
        for s in range(r + 1, 3):
            var candidate = _cross(
                field,
                _row_entry(m, r, 0),
                _row_entry(m, r, 1),
                _row_entry(m, r, 2),
                _row_entry(m, s, 0),
                _row_entry(m, s, 1),
                _row_entry(m, s, 2),
            )
            if not _all_zero(candidate):
                lengths = candidate
                found = True
                break
        if found:
            break
    if not found:
        raise Error("failed to construct a nonzero left Perron eigenvector")

    var s0 = sign_at_perron(field, lengths.l0)
    var s1 = sign_at_perron(field, lengths.l1)
    var s2 = sign_at_perron(field, lengths.l2)
    if s0 < 0 and s1 < 0 and s2 < 0:
        lengths = _negate_lengths(lengths)
        s0 = -s0
        s1 = -s1
        s2 = -s2
    if s0 <= 0 or s1 <= 0 or s2 <= 0:
        raise Error("constructed Perron tile lengths are not strictly positive")

    for parent in range(3):
        var total = CubicElt()
        for child in range(3):
            total = total + lengths.at(child).scale(m.at(child, parent))
        var expected = cubic_mul_beta(field, lengths.at(parent))
        if total != expected:
            raise Error("left Perron tile-length scaling identity failed")
    return lengths
