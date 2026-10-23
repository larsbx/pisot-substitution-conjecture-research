"""Residue rays of the determinant-two class-A lines `(p,q,r) = (n+d, n, n+eps)`.

  sigma(x) = x y^(n+d) x,   sigma(c) = c y^n x,   sigma(y) = x y^(n+eps) c,   eps = +-1, d >= 1.

A *ray* fixes `d`, `eps` and a residue `0 <= r < d`, and parametrizes
`n = d l + r` by the integer `l`. Carrier rows, run positions and row indices
are affine in `l` (for `d = 1`, `l = n`). An affine form `a l + b` equals
`(a n + (d b - a r)) / d`, so `d` times it is affine in `n` with integer
coefficients (`to_n`); every Perron sign below is the sign of such a
positive multiple.

With `h = 1/(beta-1)` the Perron root satisfies
`P(n,h) = 1 - (n+eps) h - (n+d+1-eps) h^2 - d h^3 = 0`, so

  n h (1+h) = 1 - eps h - (d+1-eps) h^2 - d h^3,

and the left Perron eigenvector, scaled by `1+h`, is
`L = (1 + (d+1-eps) h + d h^2, 1 + (1-eps) h, 1 + h)` (the identity
`h M^T L - (1+h) L = -P (1,1,1)` is checked coefficient-wise by
`psc.class_a_carrier_closure.check_line_identity`). Since
`n^3 P(n, 1/n) < 0` for both signs and every `d`, `(0, 1/n0]` contains `h_n`
for all `n >= n0`; on the gap-one plus line the sharper `(0, 1/(n0+1)]` of
the original certificate is kept. The certificate re-proves
`P(n0, bound) < 0` exactly before using either.

Source notes: docs/class-a-carrier-closure-2026-10-22.md (d=1, eps=+1),
docs/class-a-minus-line-2026-10-22.md (d=1, eps=-1),
docs/class-a-residue-rays-2026-10-22.md (d >= 2).
"""
from a1_normal_form_census import class_member, CLASS_A
from finite_exact.rat_q import Q


struct ALine(ImplicitlyCopyable, Copyable, Movable):
    var d: Int
    var eps: Int
    var r: Int

    def __init__(out self, d: Int, eps: Int, r: Int):
        self.d = d
        self.eps = eps
        self.r = r

    def check(self) raises:
        if self.eps != 1 and self.eps != -1:
            raise Error("class-A line requires eps = +-1")
        if self.d < 1 or self.d > 32 or self.r < 0 or self.r >= self.d:
            raise Error("class-A residue ray requires 1<=d<=32 and 0<=r<d")

    def n_of(self, l: Int) -> Int:
        return self.d * l + self.r

    def l_of(self, n: Int) raises -> Int:
        if n < 0 or n % self.d != self.r:
            raise Error("parameter n is not on this residue ray")
        return n // self.d

    def check_domain(self, n: Int) raises:
        """Determinant-two PIP domain of the run-index note:
        `q >= 0`, `q + eps >= 0`, `1 <= d <= 2q+6eps+5` with `q = n`."""
        self.check()
        if n < 0 or n + self.eps < 0 or self.d > 2 * n + 6 * self.eps + 5:
            raise Error("parameter outside the determinant-two class-A PIP domain")

    def line_name(self) -> String:
        return "(n+" + String(self.d) + ",n," + ("n+1" if self.eps == 1 else "n-1") + ")"

    def name(self) -> String:
        var line = self.line_name()
        if self.d == 1:
            return line
        return line + " n=" + String(self.d) + "l+" + String(self.r)

    def member(self, n: Int) raises -> List[List[Int]]:
        self.check()
        if n < 0 or n > 256:
            raise Error("class-A finite replay budget requires 0<=n<=256")
        self.check_domain(n)
        return class_member(CLASS_A, n + self.d, n, n + self.eps)

    def to_n(self, coefficient: List[Int]) -> List[Int]:
        """`d (a l + b) = a n + (d b - a r)` as `[n coefficient, constant]`."""
        return [coefficient[0], self.d * coefficient[1] - coefficient[0] * self.r]

    def run(self, letter: Int) -> List[Int]:
        """Affine length `[a, b]` (= a l + b) of the y run of `sigma(letter)`."""
        if letter == 0:
            return [self.d, self.r + self.d]
        if letter == 1:
            return [self.d, self.r]
        return [self.d, self.r + self.eps]

    def elimination(self) -> List[Int]:
        """Ascending coefficients of `n h (1+h)` as a polynomial in `h` alone."""
        return [1, -self.eps, self.eps - self.d - 1, -self.d]

    def length(self, letter: Int) raises -> List[Int]:
        """Scaled tile length `L_letter` as an ascending polynomial in `h`."""
        if letter == 0:
            return [1, self.d + 1 - self.eps, self.d]
        if letter == 1:
            return [1, 1 - self.eps]
        if letter == 2:
            return [1, 1]
        raise Error("tile letter outside 0..2")

    def bound(self, n0: Int) raises -> Q:
        """Right end `q` of an interval `(0, q]` containing `h_n` for all `n >= n0`."""
        self.check()
        return Q(1, Int64(n0 + 1)) if self.eps == 1 and self.d == 1 else Q(1, Int64(n0))


def plus_line() -> ALine:
    return ALine(1, 1, 0)


def minus_line() -> ALine:
    return ALine(1, -1, 0)
