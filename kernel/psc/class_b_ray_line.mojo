"""Residue rays of class B's top layer, `sigma(x) = x y^p x, sigma(c) = c y^q x, sigma(y) = c y^r x`.

  plus  (eps = +1):  r = q + 1,  p = 3q + 12 - g,
  minus (eps = -1):  r = q - 1,  p = 3q - g,       i.e.  p = 3q + 6 + 6 eps - g,

with `g >= 1` the distance to the PIP boundary
(docs/class-b-top-layer-stopgo-2026-10-23.md). A *ray* fixes `(eps, g, r0)`,
`0 <= r0 < g`, and writes `q = g l + r0`; run lengths and carrier rows are
affine in `l`.

The incidence matrix has columns `(2,0,p)`, `(1,1,q)`, `(1,1,r)`, so
`chi(t) = (t-2)(t-1)(t-r) - q(t-2) - p t = A(t) - q t(t+1)` with

  A(t) = (t-2)(t-1)(t-eps) - (6 + 6 eps - g) t,

and the Perron root satisfies `q beta(beta+1) = A(beta)`. Scaled by
`beta+1` and normalized at `L_y = beta(beta+1)`, the left Perron eigenvector is

  L = (3 beta^2 + (3 + 3 eps - g) beta + 3 eps,  (beta+1)(beta-eps),  beta(beta+1)),

(checked modulo `chi` by `check_line_identity`). In the unimodular coordinates
`u = 3k + c + y`, `d = c - 3k` of an integral offset `w = (k, c, y)` the
displacement is

  T(w) = L . w = (beta+1)(u beta - eps d) - g beta k,

so the growth direction `(1,3,-6)` (fixed `u, d`) moves `T` by `-g beta`.

Every Perron sign is the sign of `E = a(beta) + l b(beta)` with integer
polynomials `a, b`. Since `g l beta(beta+1) = A(beta) - r0 beta(beta+1)`, its
sign is that of the integer polynomial `g a beta(beta+1) + b (A - r0 beta(beta+1))`
(`numerator`), decided for every `beta >= beta_low` by the Sturm sign of
`h^D N(1/h)` on `(0, 1/beta_low]` (`sign`). `chi_q(t)` decreases in `q` for
`t > 0`, so `chi_{q0}(beta_low) < 0` (`check_bound`) puts the Perron root of
every member `q >= q0` above `beta_low = q0 + 3 + eps`.

Source note: docs/class-b-ray-certificate-2026-10-27.md.
"""
from a1_normal_form_census import class_member, CLASS_B
from finite_exact.rat_q import Q
from finite_linear_algebra.qpoly import evaluate
from psc.exact import q_poly, q_sign
from psc.class_a_carrier_closure import AffH, pnorm, padd, psub, pscale, pmul, sign_on_interval


struct BRay(ImplicitlyCopyable, Copyable, Movable):
    var eps: Int
    var g: Int
    var r: Int

    def __init__(out self, eps: Int, g: Int, r: Int):
        self.eps = eps
        self.g = g
        self.r = r

    def check(self) raises:
        if self.eps != 1 and self.eps != -1:
            raise Error("class-B ray requires eps = +-1")
        if self.g < 1 or self.g > 16 or self.r < 0 or self.r >= self.g:
            raise Error("class-B residue ray requires 1<=g<=16 and 0<=r<g")

    def q_of(self, l: Int) -> Int:
        return self.g * l + self.r

    def l_of(self, q: Int) raises -> Int:
        if q < 0 or q % self.g != self.r:
            raise Error("parameter q is not on this residue ray")
        return q // self.g

    def p_of(self, q: Int) -> Int:
        return 3 * q + 6 + 6 * self.eps - self.g

    def name(self) -> String:
        return ("plus" if self.eps == 1 else "minus") + " g=" + String(self.g) + " q=" + String(self.g) + "l+" + String(self.r)

    def check_domain(self, q: Int) raises:
        """Open top layer: `max(2q+13, (5q+10)/2) < p < 3q+12` (plus) or
        `max(2q+7, (5q-5)/2) < p < 3q` (minus)."""
        self.check()
        var p = self.p_of(q)
        var inside = (p > 2 * q + 13 and 2 * p > 5 * q + 10) if self.eps == 1 else (p > 2 * q + 7 and 2 * p > 5 * q - 5)
        if q < 1 or not inside:
            raise Error("parameter outside the open class-B top layer")

    def member(self, q: Int) raises -> List[List[Int]]:
        if q < 1 or q > 48:
            raise Error("class-B finite replay budget requires 1<=q<=48")
        self.check_domain(q)
        return class_member(CLASS_B, self.p_of(q), q, q + self.eps)

    def run(self, letter: Int) raises -> List[Int]:
        """Affine length `[a, b]` (= a l + b) of the y run of `sigma(letter)`."""
        if letter == 0:
            return [3 * self.g, 3 * self.r + 6 + 6 * self.eps - self.g]
        if letter == 1:
            return [self.g, self.r]
        if letter == 2:
            return [self.g, self.r + self.eps]
        raise Error("tile letter outside 0..2")

    def length(self, letter: Int) raises -> List[Int]:
        """Scaled tile length `L_letter` as an ascending polynomial in beta."""
        if letter == 0:
            return [3 * self.eps, 3 + 3 * self.eps - self.g, 3]
        if letter == 1:
            return [-self.eps, 1 - self.eps, 1]
        if letter == 2:
            return [0, 1, 1]
        raise Error("tile letter outside 0..2")

    def perron_a(self) -> List[Int]:
        """`A(beta) = (beta-2)(beta-1)(beta-eps) - (6+6eps-g) beta`."""
        return psub(pmul(pmul([-2, 1], [-1, 1]), [-self.eps, 1]), [0, 6 + 6 * self.eps - self.g])

    def numerator(self, e: AffH) -> List[Int]:
        """`g a beta(beta+1) + b (A - r0 beta(beta+1))`, whose sign is that of `a + l b`."""
        var bb = List[Int]([0, 1, 1])
        return padd(pscale(pmul(e.a, bb), self.g), pmul(e.b, psub(self.perron_a(), pscale(bb, self.r))))

    def beta_low(self, q0: Int) -> Int:
        return q0 + 3 + self.eps

    def sign(self, e: AffH, q0: Int) raises -> Int:
        """Sign of `a(beta_q) + l b(beta_q)` for every member `q >= q0` of the ray;
        raises when Sturm does not decide it on the whole interval."""
        var f = pnorm(self.numerator(e))
        if len(f) == 0:
            return 0
        var h = List[Int]()
        for i in range(len(f)):
            h.append(f[len(f) - 1 - i])
        return sign_on_interval(h, Q(1, Int64(self.beta_low(q0))))


def check_line_identity(ray: BRay) raises:
    """`(L M)_j = beta L_j` modulo `q beta(beta+1) = A(beta)` for each column `j`
    of the incidence matrix, coefficient-wise in `beta`: with `p = 3q + 6+6eps-g`
    and `r = q + eps`, `(L M)_j - beta L_j = a + q b`, and `a beta(beta+1) + b A`
    must vanish identically."""
    ray.check()
    var lx = ray.length(0)
    var lc = ray.length(1)
    var ly = ray.length(2)
    var cols = List[List[Int]]([List[Int]([2, 0, 6 + 6 * ray.eps - ray.g, 3]), List[Int]([1, 1, 0, 1]), List[Int]([1, 1, ray.eps, 1])])
    var ls = List[List[Int]]([lx.copy(), lc.copy(), ly.copy()])
    for j in range(3):
        var col = cols[j].copy()
        var a = psub(padd(padd(pscale(lx, col[0]), pscale(lc, col[1])), pscale(ly, col[2])), pmul(ls[j], [0, 1]))
        var b = pscale(ly, col[3])
        if len(padd(pmul(a, [0, 1, 1]), pmul(b, ray.perron_a()))) != 0:
            raise Error("scaled lengths are not the left Perron eigenvector of the ray")


def check_bound(ray: BRay, q0: Int) raises:
    """`chi_{q0}(beta_low) < 0`, so every member `q >= q0` has `beta_q > beta_low`."""
    var bl = ray.beta_low(q0)
    var chi = psub(ray.perron_a(), pscale([0, 1, 1], q0))
    if q_sign(evaluate(q_poly(chi), Q(Int64(bl), 1))) >= 0:
        raise Error("beta_low does not bound the Perron root from below")
