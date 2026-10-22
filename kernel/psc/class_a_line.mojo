"""The two gap-one determinant-two class-A lines `(p,q,r) = (n+1, n, n+eps)`.

  sigma(x) = x y^(n+1) x,   sigma(c) = c y^n x,   sigma(y) = x y^(n+eps) c,   eps = +-1.

With `h = 1/(beta-1)` the Perron root satisfies
`P(n,h) = 1 - (n+eps) h - (n+2-eps) h^2 - h^3 = 0`, so

  n h (1+h) = 1 - eps h - (2-eps) h^2 - h^3,

and the left Perron eigenvector, scaled by `1+h`, is
`L = (1 + (2-eps) h + h^2, 1 + (1-eps) h, 1 + h)` (the identity
`h M^T L - (1+h) L = -P (1,1,1)` is checked coefficient-wise by
`psc.class_a_carrier_closure.check_line_identity`). The positive root lies in
`(1/(n+2), 1/(n+1))` for `eps=+1` and in `(1/(n+1), 1/n)` for `eps=-1`, so
`bound(n0)` contains `h_n` for every `n >= n0`; the closure certificate
re-proves `P(n0, bound) < 0` exactly before using it.

Only `eps = +-1` with gap `d = p - q = 1` is represented: for `d >= 2` the
child run index `y'` is no longer unit-slope in the row index and the
interval realizability of the closure certificate does not apply.
Source notes: docs/class-a-carrier-closure-2026-10-22.md (eps=+1),
docs/class-a-minus-line-2026-10-22.md (eps=-1).
"""
from a1_normal_form_census import class_member, CLASS_A
from finite_exact.rat_q import Q


struct ALine(ImplicitlyCopyable, Copyable, Movable):
    var eps: Int

    def __init__(out self, eps: Int):
        self.eps = eps

    def check(self) raises:
        if self.eps != 1 and self.eps != -1:
            raise Error("gap-one class-A line requires eps = +-1")

    def name(self) -> String:
        return "(n+1,n,n+1)" if self.eps == 1 else "(n+1,n,n-1)"

    def member(self, n: Int) raises -> List[List[Int]]:
        self.check()
        if n < 1 or n > 256:
            raise Error("class-A finite replay budget requires 1<=n<=256")
        return class_member(CLASS_A, n + 1, n, n + self.eps)

    def run(self, letter: Int) -> List[Int]:
        """Affine length `[a, b]` (= a n + b) of the y run of `sigma(letter)`."""
        if letter == 0:
            return [1, 1]
        if letter == 1:
            return [1, 0]
        return [1, self.eps]

    def elimination(self) -> List[Int]:
        """Ascending coefficients of `n h (1+h)` as a polynomial in `h` alone."""
        return [1, -self.eps, self.eps - 2, -1]

    def length(self, letter: Int) raises -> List[Int]:
        """Scaled tile length `L_letter` as an ascending polynomial in `h`."""
        if letter == 0:
            return [1, 2 - self.eps, 1]
        if letter == 1:
            return [1, 1 - self.eps]
        if letter == 2:
            return [1, 1]
        raise Error("tile letter outside 0..2")

    def bound(self, n0: Int) raises -> Q:
        """Right end `q` of an interval `(0, q]` containing `h_n` for all `n >= n0`."""
        self.check()
        return Q(1, Int64(n0 + 1)) if self.eps == 1 else Q(1, Int64(n0))


def plus_line() -> ALine:
    return ALine(1)


def minus_line() -> ALine:
    return ALine(-1)
