"""Exact cubic Perron-field arithmetic for the standing alphabet-three PIP regime.

Elements are stored in the integral power basis ``1, beta, beta^2`` modulo the
monic characteristic polynomial of the incidence matrix. Order at the Perron
embedding is decided by a specialized Sturm--Tarski signed-remainder query with
checked fixed-width integer arithmetic. No floating point, rational bisection,
or Euclidean stable-space lattice is used.

The implementation is an executable finite-research kernel over Mojo ``Int``.
Every theorem-facing arithmetic operation used by the overlap diagnostic checks
for overflow and raises on an unsafe intermediate rather than wrapping. A
successful finite run is exact; failure is inconclusive, not mathematical
evidence.
"""

from psc.mat3 import Mat3
from psc.pisot import is_pip


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


def _checked_abs(x: Int) raises -> Int:
    if x == Int.MIN:
        raise Error("exact cubic arithmetic cannot take abs(Int.MIN)")
    return -x if x < 0 else x


def _checked_add(a: Int, b: Int) raises -> Int:
    if b > 0 and a > Int.MAX - b:
        raise Error("exact cubic integer addition overflow")
    if b < 0 and a < Int.MIN - b:
        raise Error("exact cubic integer addition overflow")
    return a + b


def _checked_sub(a: Int, b: Int) raises -> Int:
    if b > 0 and a < Int.MIN + b:
        raise Error("exact cubic integer subtraction overflow")
    if b < 0 and a > Int.MAX + b:
        raise Error("exact cubic integer subtraction overflow")
    return a - b


def _checked_neg(a: Int) raises -> Int:
    if a == Int.MIN:
        raise Error("exact cubic integer negation overflow")
    return -a


def _checked_mul(a: Int, b: Int) raises -> Int:
    if a == 0 or b == 0:
        return 0
    var aa = _checked_abs(a)
    var bb = _checked_abs(b)
    if aa > Int.MAX // bb:
        raise Error("exact cubic integer multiplication overflow")
    return a * b


def _mul3(a: Int, b: Int, c: Int) raises -> Int:
    return _checked_mul(_checked_mul(a, b), c)


def _mul4(a: Int, b: Int, c: Int, d: Int) raises -> Int:
    return _checked_mul(_mul3(a, b, c), d)


def _mul5(a: Int, b: Int, c: Int, d: Int, e: Int) raises -> Int:
    return _checked_mul(_mul4(a, b, c, d), e)


def _sign_int(x: Int) -> Int:
    if x > 0:
        return 1
    if x < 0:
        return -1
    return 0


def cubic_add_checked(x: CubicElt, y: CubicElt) raises -> CubicElt:
    return CubicElt(
        _checked_add(x.a0, y.a0),
        _checked_add(x.a1, y.a1),
        _checked_add(x.a2, y.a2),
    )


def cubic_sub_checked(x: CubicElt, y: CubicElt) raises -> CubicElt:
    return CubicElt(
        _checked_sub(x.a0, y.a0),
        _checked_sub(x.a1, y.a1),
        _checked_sub(x.a2, y.a2),
    )


def cubic_scale_checked(x: CubicElt, n: Int) raises -> CubicElt:
    return CubicElt(
        _checked_mul(n, x.a0),
        _checked_mul(n, x.a1),
        _checked_mul(n, x.a2),
    )


def build_perron_field3(m: Mat3) raises -> PerronField3:
    if not is_pip(m):
        raise Error("cubic Perron field requires a primitive irreducible Pisot matrix")
    var chi = m.charpoly()
    return PerronField3(chi[0], chi[1], chi[2])


def cubic_mul_beta(field: PerronField3, x: CubicElt) raises -> CubicElt:
    """Multiply by beta using beta^3 = -chi2 beta^2 - chi1 beta - chi0."""
    var c0 = _checked_neg(_checked_mul(field.chi0, x.a2))
    var c1 = _checked_sub(x.a0, _checked_mul(field.chi1, x.a2))
    var c2 = _checked_sub(x.a1, _checked_mul(field.chi2, x.a2))
    return CubicElt(c0, c1, c2)


def cubic_mul(field: PerronField3, x: CubicElt, y: CubicElt) raises -> CubicElt:
    var v0 = _checked_mul(x.a0, y.a0)
    var v1 = _checked_add(_checked_mul(x.a0, y.a1), _checked_mul(x.a1, y.a0))
    var v2 = _checked_add(
        _checked_add(_checked_mul(x.a0, y.a2), _checked_mul(x.a1, y.a1)),
        _checked_mul(x.a2, y.a0),
    )
    var v3 = _checked_add(_checked_mul(x.a1, y.a2), _checked_mul(x.a2, y.a1))
    var v4 = _checked_mul(x.a2, y.a2)
    var v: List[Int] = [v0, v1, v2, v3, v4]

    for degree in range(4, 2, -1):
        var coefficient = v[degree]
        if coefficient == 0:
            continue
        v[degree - 1] = _checked_sub(
            v[degree - 1], _checked_mul(coefficient, field.chi2)
        )
        v[degree - 2] = _checked_sub(
            v[degree - 2], _checked_mul(coefficient, field.chi1)
        )
        v[degree - 3] = _checked_sub(
            v[degree - 3], _checked_mul(coefficient, field.chi0)
        )
        v[degree] = 0
    return CubicElt(v[0], v[1], v[2])


def _eval_monic_cubic(field: PerronField3, z: Int) raises -> Int:
    var value = _checked_add(z, field.chi2)
    value = _checked_add(_checked_mul(value, z), field.chi1)
    value = _checked_add(_checked_mul(value, z), field.chi0)
    return value


def _eval_quadratic(a: Int, b: Int, c: Int, z: Int) raises -> Int:
    return _checked_add(_checked_mul(_checked_add(_checked_mul(a, z), b), z), c)


def _eval_linear(a: Int, b: Int, z: Int) raises -> Int:
    return _checked_add(_checked_mul(a, z), b)


def _variations(signs: List[Int]) -> Int:
    var previous = 0
    var count = 0
    for i in range(len(signs)):
        var current = signs[i]
        if current == 0:
            continue
        if previous != 0 and current != previous:
            count += 1
        previous = current
    return count


def _sequence_variations_at(
    field: PerronField3,
    a: Int,
    b: Int,
    c: Int,
    d: Int,
    e: Int,
    terminal_sign: Int,
    z: Int,
) raises -> Int:
    var signs = List[Int]()
    signs.append(_sign_int(_eval_monic_cubic(field, z)))
    signs.append(_sign_int(_eval_quadratic(a, b, c, z)))
    if a != 0:
        signs.append(_sign_int(_eval_linear(d, e, z)))
        if d != 0:
            signs.append(terminal_sign)
    elif b != 0:
        signs.append(terminal_sign)
    return _variations(signs)


def _perron_integer_bound(field: PerronField3) raises -> Int:
    var m = _checked_abs(field.chi0)
    var t = _checked_abs(field.chi1)
    if t > m:
        m = t
    t = _checked_abs(field.chi2)
    if t > m:
        m = t
    return _checked_add(m, 1)


def _signed_remainder_coefficients(
    field: PerronField3, x: CubicElt
) raises -> Tuple[Int, Int, Int]:
    # S1 = rem(P' * Q, P), where P is the monic characteristic cubic and
    # Q = x.a2 X^2 + x.a1 X + x.a0.
    var a = field.chi2
    var b = field.chi1
    var c = field.chi0
    var u = x.a2
    var v = x.a1
    var w = x.a0

    var A = _checked_mul(_checked_mul(a, a), u)
    A = _checked_sub(A, _checked_mul(a, v))
    A = _checked_sub(A, _checked_mul(2, _checked_mul(b, u)))
    A = _checked_add(A, _checked_mul(3, w))

    var B = _checked_mul(_checked_mul(a, b), u)
    B = _checked_add(B, _checked_mul(2, _checked_mul(a, w)))
    B = _checked_sub(B, _checked_mul(2, _checked_mul(b, v)))
    B = _checked_sub(B, _checked_mul(3, _checked_mul(c, u)))

    var C = _checked_mul(_checked_mul(a, c), u)
    C = _checked_add(C, _checked_mul(b, w))
    C = _checked_sub(C, _checked_mul(3, _checked_mul(c, v)))
    return (A, B, C)


def _quadratic_terminal_sign(
    field: PerronField3,
    A: Int,
    B: Int,
    C: Int,
) raises -> Tuple[Int, Int, Int]:
    # For A != 0, S2 has the sign of D X + E. If D != 0, the final constant
    # S3 has sign -sign(R), where R is the resultant-like factor below. All
    # omitted pseudo-division scales are positive, so signs are unchanged.
    var a = field.chi2
    var b = field.chi1
    var c = field.chi0
    var A2 = _checked_mul(A, A)
    var B2 = _checked_mul(B, B)

    var D = _checked_neg(_checked_mul(A2, b))
    D = _checked_add(D, _mul3(A, B, a))
    D = _checked_add(D, _checked_mul(A, C))
    D = _checked_sub(D, B2)

    var E = _checked_neg(_checked_mul(A2, c))
    E = _checked_add(E, _mul3(A, C, a))
    E = _checked_sub(E, _checked_mul(B, C))

    if D == 0:
        if E == 0:
            raise Error("Sturm-Tarski sequence lost coprimality")
        return (D, E, _sign_int(E))

    var R = _mul5(A, A, A, c, c)
    R = _checked_sub(R, _mul5(A, A, B, b, c))
    R = _checked_sub(R, _checked_mul(2, _mul5(A, A, C, a, c)))
    R = _checked_add(R, _mul5(A, A, C, b, b))
    R = _checked_add(R, _mul5(A, B, B, a, c))
    R = _checked_sub(R, _mul5(A, B, C, a, b))
    R = _checked_add(R, _checked_mul(3, _mul4(A, B, C, c)))
    R = _checked_add(R, _mul5(A, C, C, a, a))
    R = _checked_sub(R, _checked_mul(2, _mul4(A, C, C, b)))
    R = _checked_sub(R, _mul4(B, B, B, c))
    R = _checked_add(R, _mul4(B, B, C, b))
    R = _checked_sub(R, _mul4(B, C, C, a))
    R = _checked_add(R, _mul3(C, C, C))
    if R == 0:
        raise Error("Sturm-Tarski terminal resultant unexpectedly vanished")
    return (D, E, -_sign_int(R))


def _linear_terminal_sign(field: PerronField3, B: Int, C: Int) raises -> Int:
    # For S1 = B X + C, S2 = -P(-C/B). Its sign is
    # -sign(N)*sign(B), with N = B^3 P(-C/B).
    var a = field.chi2
    var b = field.chi1
    var c = field.chi0
    var N = _checked_neg(_mul3(C, C, C))
    N = _checked_add(N, _mul4(a, C, C, B))
    N = _checked_sub(N, _mul4(b, C, B, B))
    N = _checked_add(N, _mul4(c, B, B, B))
    if N == 0:
        raise Error("Sturm-Tarski linear resultant unexpectedly vanished")
    return -_sign_int(N) * _sign_int(B)


def sign_at_perron(field: PerronField3, x: CubicElt) raises -> Int:
    """Return the exact sign of ``x(beta)`` without rational refinement.

    For nonzero Q of degree at most two, the irreducible cubic Perron root beta
    cannot be a zero of Q. We use the Sturm--Tarski query for the Cauchy index of
    ``P' Q / P`` on ``(1,B]``. Because P has exactly one root in that interval,
    the variation difference is precisely ``sign(Q(beta))``. The signed
    remainder sequence is specialized symbolically to degree 3/2 so every
    operation is checked fixed-width integer arithmetic.
    """
    if x.is_zero():
        return 0

    var coeffs = _signed_remainder_coefficients(field, x)
    var A = coeffs[0]
    var B = coeffs[1]
    var C = coeffs[2]
    if A == 0 and B == 0 and C == 0:
        raise Error("Sturm-Tarski first remainder unexpectedly vanished")

    var D = 0
    var E = 0
    var terminal_sign = 0
    if A != 0:
        var tail = _quadratic_terminal_sign(field, A, B, C)
        D = tail[0]
        E = tail[1]
        terminal_sign = tail[2]
    elif B != 0:
        terminal_sign = _linear_terminal_sign(field, B, C)

    var hi = _perron_integer_bound(field)
    if hi <= 1:
        raise Error("invalid Perron root bound")
    var lower = _sequence_variations_at(field, A, B, C, D, E, terminal_sign, 1)
    var upper = _sequence_variations_at(field, A, B, C, D, E, terminal_sign, hi)
    var answer = lower - upper
    if answer != 1 and answer != -1:
        raise Error("Sturm-Tarski Perron sign query did not isolate one signed root")
    return answer


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
) raises -> TileLengths3:
    return TileLengths3(
        cubic_sub_checked(cubic_mul(field, a1, b2), cubic_mul(field, a2, b1)),
        cubic_sub_checked(cubic_mul(field, a2, b0), cubic_mul(field, a0, b2)),
        cubic_sub_checked(cubic_mul(field, a0, b1), cubic_mul(field, a1, b0)),
    )


def _all_zero(lengths: TileLengths3) -> Bool:
    return lengths.l0.is_zero() and lengths.l1.is_zero() and lengths.l2.is_zero()


def _negate_lengths(lengths: TileLengths3) raises -> TileLengths3:
    return TileLengths3(
        CubicElt(_checked_neg(lengths.l0.a0), _checked_neg(lengths.l0.a1), _checked_neg(lengths.l0.a2)),
        CubicElt(_checked_neg(lengths.l1.a0), _checked_neg(lengths.l1.a1), _checked_neg(lengths.l1.a2)),
        CubicElt(_checked_neg(lengths.l2.a0), _checked_neg(lengths.l2.a1), _checked_neg(lengths.l2.a2)),
    )


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
            total = cubic_add_checked(
                total,
                cubic_scale_checked(lengths.at(child), m.at(child, parent)),
            )
        var expected = cubic_mul_beta(field, lengths.at(parent))
        if total != expected:
            raise Error("left Perron tile-length scaling identity failed")
    return lengths
