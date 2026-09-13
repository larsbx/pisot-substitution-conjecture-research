"""Checked exact rational interval arithmetic for finite certificate kernels.

Intervals are closed rational boxes with normalized exact endpoints.  Every
integer operation is checked against Mojo ``Int`` overflow.  An operation that
cannot be represented safely raises rather than widening, wrapping, or guessing.

The intended proof-support discipline is:

* natural interval extension is the first enclosure layer;
* a strict sign is certified only when the entire interval excludes zero;
* an interval containing zero means *unknown*, never equality or failure;
* callers may delegate unknown cases to an independent exact algebraic oracle.

This is finite executable arithmetic, not arbitrary-precision arithmetic.
"""


def _checked_abs(x: Int) raises -> Int:
    if x == Int.MIN:
        raise Error("rational interval cannot take abs(Int.MIN)")
    return -x if x < 0 else x


def _checked_neg(x: Int) raises -> Int:
    if x == Int.MIN:
        raise Error("rational interval integer negation overflow")
    return -x


def _checked_add(a: Int, b: Int) raises -> Int:
    if b > 0 and a > Int.MAX - b:
        raise Error("rational interval integer addition overflow")
    if b < 0 and a < Int.MIN - b:
        raise Error("rational interval integer addition overflow")
    return a + b


def _checked_sub(a: Int, b: Int) raises -> Int:
    if b > 0 and a < Int.MIN + b:
        raise Error("rational interval integer subtraction overflow")
    if b < 0 and a > Int.MAX + b:
        raise Error("rational interval integer subtraction overflow")
    return a - b


def _checked_mul(a: Int, b: Int) raises -> Int:
    if a == 0 or b == 0:
        return 0
    var aa = _checked_abs(a)
    var bb = _checked_abs(b)
    if aa > Int.MAX // bb:
        raise Error("rational interval integer multiplication overflow")
    return a * b


def _gcd(a: Int, b: Int) raises -> Int:
    var x = _checked_abs(a)
    var y = _checked_abs(b)
    while y != 0:
        var t = x % y
        x = y
        y = t
    return x


struct CheckedRat(ImplicitlyCopyable, Copyable, Movable, Equatable, Writable):
    """Normalized exact rational with checked fixed-width arithmetic."""

    var num: Int
    var den: Int

    def __init__(out self, num: Int, den: Int = 1) raises:
        if den == 0:
            raise Error("rational interval denominator must be nonzero")
        var n = num
        var d = den
        if d < 0:
            n = _checked_neg(n)
            d = _checked_neg(d)
        var g = _gcd(n, d)
        if g == 0:
            self.num = 0
            self.den = 1
        else:
            self.num = n // g
            self.den = d // g

    def __eq__(self, other: CheckedRat) -> Bool:
        return self.num == other.num and self.den == other.den

    def __ne__(self, other: CheckedRat) -> Bool:
        return not (self == other)

    def compare(self, other: CheckedRat) raises -> Int:
        # Cancel the denominator gcd before cross multiplication.
        var g = _gcd(self.den, other.den)
        var left = _checked_mul(self.num, other.den // g)
        var right = _checked_mul(other.num, self.den // g)
        if left < right:
            return -1
        if left > right:
            return 1
        return 0

    def add(self, other: CheckedRat) raises -> CheckedRat:
        var g = _gcd(self.den, other.den)
        var a = other.den // g
        var b = self.den // g
        var n = _checked_add(_checked_mul(self.num, a), _checked_mul(other.num, b))
        var d = _checked_mul(self.den, a)
        return CheckedRat(n, d)

    def sub(self, other: CheckedRat) raises -> CheckedRat:
        var g = _gcd(self.den, other.den)
        var a = other.den // g
        var b = self.den // g
        var n = _checked_sub(_checked_mul(self.num, a), _checked_mul(other.num, b))
        var d = _checked_mul(self.den, a)
        return CheckedRat(n, d)

    def mul(self, other: CheckedRat) raises -> CheckedRat:
        # Cross-cancel before multiplying to reduce overflow pressure.
        var g1 = _gcd(self.num, other.den)
        var g2 = _gcd(other.num, self.den)
        var an = self.num // g1
        var bd = other.den // g1
        var bn = other.num // g2
        var ad = self.den // g2
        return CheckedRat(_checked_mul(an, bn), _checked_mul(ad, bd))

    def reciprocal(self) raises -> CheckedRat:
        if self.num == 0:
            raise Error("rational interval reciprocal of zero")
        return CheckedRat(self.den, self.num)

    def div(self, other: CheckedRat) raises -> CheckedRat:
        return self.mul(other.reciprocal())

    def midpoint(self, other: CheckedRat) raises -> CheckedRat:
        return self.add(other).div(CheckedRat(2, 1))

    def sign(self) -> Int:
        if self.num > 0:
            return 1
        if self.num < 0:
            return -1
        return 0

    def write_to[W: Writer](self, mut w: W):
        if self.den == 1:
            w.write(self.num)
        else:
            w.write(self.num, "/", self.den)


struct RatInterval(ImplicitlyCopyable, Copyable, Movable, Equatable, Writable):
    """Closed rational interval ``[lo, hi]`` with exact checked endpoints."""

    var lo: CheckedRat
    var hi: CheckedRat

    def __init__(out self, lo: CheckedRat, hi: CheckedRat) raises:
        if lo.compare(hi) > 0:
            raise Error("rational interval endpoints are reversed")
        self.lo = lo
        self.hi = hi

    def __eq__(self, other: RatInterval) -> Bool:
        return self.lo == other.lo and self.hi == other.hi

    def __ne__(self, other: RatInterval) -> Bool:
        return not (self == other)

    def contains_zero(self) raises -> Bool:
        var z = CheckedRat(0, 1)
        return self.lo.compare(z) <= 0 and self.hi.compare(z) >= 0

    def strict_sign(self) raises -> Int:
        """Return +/-1 only when every point has that sign; otherwise 0/unknown."""
        var z = CheckedRat(0, 1)
        if self.lo.compare(z) > 0:
            return 1
        if self.hi.compare(z) < 0:
            return -1
        return 0

    def add(self, other: RatInterval) raises -> RatInterval:
        return RatInterval(self.lo.add(other.lo), self.hi.add(other.hi))

    def sub(self, other: RatInterval) raises -> RatInterval:
        return RatInterval(self.lo.sub(other.hi), self.hi.sub(other.lo))

    def mul(self, other: RatInterval) raises -> RatInterval:
        var p0 = self.lo.mul(other.lo)
        var p1 = self.lo.mul(other.hi)
        var p2 = self.hi.mul(other.lo)
        var p3 = self.hi.mul(other.hi)
        var lo = p0
        var hi = p0
        if p1.compare(lo) < 0:
            lo = p1
        if p2.compare(lo) < 0:
            lo = p2
        if p3.compare(lo) < 0:
            lo = p3
        if p1.compare(hi) > 0:
            hi = p1
        if p2.compare(hi) > 0:
            hi = p2
        if p3.compare(hi) > 0:
            hi = p3
        return RatInterval(lo, hi)

    def reciprocal(self) raises -> RatInterval:
        if self.contains_zero():
            raise Error("rational interval division by an interval containing zero")
        return RatInterval(self.hi.reciprocal(), self.lo.reciprocal())

    def div(self, other: RatInterval) raises -> RatInterval:
        return self.mul(other.reciprocal())

    def write_to[W: Writer](self, mut w: W):
        w.write("[", self.lo, ",", self.hi, "]")


def point_interval(x: CheckedRat) raises -> RatInterval:
    return RatInterval(x, x)


def integer_interval(lo: Int, hi: Int) raises -> RatInterval:
    return RatInterval(CheckedRat(lo, 1), CheckedRat(hi, 1))


def interval_horner_int(coeffs: List[Int], x: RatInterval) raises -> RatInterval:
    """Natural interval extension of an integer polynomial, low degree first."""
    if len(coeffs) == 0:
        return point_interval(CheckedRat(0, 1))
    var acc = point_interval(CheckedRat(coeffs[len(coeffs) - 1], 1))
    for i in range(len(coeffs) - 2, -1, -1):
        acc = acc.mul(x).add(point_interval(CheckedRat(coeffs[i], 1)))
    return acc


def eval_int_poly_at_rat(coeffs: List[Int], x: CheckedRat) raises -> CheckedRat:
    """Exact checked Horner evaluation at one rational endpoint."""
    if len(coeffs) == 0:
        return CheckedRat(0, 1)
    var acc = CheckedRat(coeffs[len(coeffs) - 1], 1)
    for i in range(len(coeffs) - 2, -1, -1):
        acc = acc.mul(x).add(CheckedRat(coeffs[i], 1))
    return acc
