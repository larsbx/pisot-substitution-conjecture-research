"""Exact rational arithmetic over Z, normalised (denominator > 0, gcd 1).

Every linear-algebra fact in the Spectral module certificate is a statement
over Q about integer data, so the kernel needs no floating point anywhere.
"""


def igcd(a: Int, b: Int) -> Int:
    var x = abs(a)
    var y = abs(b)
    while y != 0:
        var t = x % y
        x = y
        y = t
    return x


struct Rat(ImplicitlyCopyable, Copyable, Movable, Writable, Equatable):
    """A normalised rational: `den > 0` and `gcd(num, den) == 1`."""

    var num: Int
    var den: Int

    def __init__(out self, num: Int, den: Int = 1):
        if den == 0:
            self.num = 0
            self.den = 1
            return
        var s = 1 if den > 0 else -1
        var g = igcd(num, den)
        if g == 0:
            self.num = 0
            self.den = 1
        else:
            self.num = s * num // g
            self.den = s * den // g

    def __add__(self, o: Rat) -> Rat:
        return Rat(self.num * o.den + o.num * self.den, self.den * o.den)

    def __sub__(self, o: Rat) -> Rat:
        return Rat(self.num * o.den - o.num * self.den, self.den * o.den)

    def __mul__(self, o: Rat) -> Rat:
        return Rat(self.num * o.num, self.den * o.den)

    def __truediv__(self, o: Rat) -> Rat:
        return Rat(self.num * o.den, self.den * o.num)

    def __neg__(self) -> Rat:
        return Rat(-self.num, self.den)

    def __eq__(self, o: Rat) -> Bool:
        return self.num == o.num and self.den == o.den

    def __ne__(self, o: Rat) -> Bool:
        return not (self == o)

    def is_zero(self) -> Bool:
        return self.num == 0

    def write_to[W: Writer](self, mut w: W):
        if self.den == 1:
            w.write(self.num)
        else:
            w.write(self.num, "/", self.den)


def rat_zero() -> Rat:
    return Rat(0, 1)


def rat_one() -> Rat:
    return Rat(1, 1)


def rat_vec(v: List[Int]) -> List[Rat]:
    """Lift an integer vector into Q^n."""
    var out = List[Rat]()
    for i in range(len(v)):
        out.append(Rat(v[i], 1))
    return out^
