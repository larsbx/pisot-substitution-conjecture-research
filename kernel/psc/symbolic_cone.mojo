"""The seed-patch overlap graph of a two-parameter cone, for every member at once.

docs/p1b-symbolic-cone-2026-10-08.md. A *cone* is a family `sigma_s`,
`s = (s1, s2)` in a shifted orthant `{s1 >= n1, s2 >= n2}`, on three letters
whose images are `f_a y^(n_a(s)) l_a`: a first letter, a run of `y` whose length
is affine in `s`, and a last letter. A line (`psc.symbolic_line`) is the case
where one coordinate does not occur. This module computes the overlap graph
reachable from the swap seeds as a function of `s`: vertices `(a, b, w)` with
`w` a vector of polynomials in `Q[s1, s2]`, each child decided on the whole
region at once.

Signs on the region. A polynomial `f(s)` is certified positive on the region
when `f(n1 + u, n2 + v)` has nonnegative coefficients and positive constant
term, possibly after multiplication by a power of `1 + u + v` (Polya's
multiplier; `1 + u` or `1 + v` when only one coordinate occurs). The sign is
guessed at one point of the region and then certified; an uncertified sign is
**not** a verdict and raises.

Signs at beta. In two parameters the Sturm--Tarski sequence of the line engine
has entries whose signs need not be constant on the region, so this module does
not use it. Instead the Perron root is **bracketed**: the caller supplies
rational functions `L(s) < U(s)` and the module certifies `chi(L) < 0 < chi(U)`
with `L > |det M|`. Together with the Jury conditions on the quotient
`chi(t) / (t - beta)` this proves that the family is PIP on the region and that
`beta` is the root of `chi` in `(L, U)`; where Rouche's dominant-coefficient
condition is certified on the region it replaces the Jury reads (`rouche_disc`).
An element `G` of `Q[s][t] / (chi)`,
reduced to degree at most 2, then has the sign at `beta` of `G(L)` and `G(U)`
when those agree and `G` is monotone on `[L, U]` (its derivative has one sign at
both ends) or bends away from zero (`sign(lc G) != sign G(L)`). Several brackets
may be supplied, tightest last; an undecided sign raises.

Run positions are fitted at three sample points as affine functions of `s` and
certified by sign queries, exactly as on a line; the concrete samples are
decided by the line engine's exact Sturm queries with constant coefficients.

What the closure means. If the run finishes, then for every integer point of
the region the exact seed-reachable overlap graph of `sigma_s`
(`psc.overlap_seed_patch`) is the symbolic graph with `s` substituted; the proof
is Lemma S of docs/p1b-symbolic-line-2026-10-07.md with the region in place of
`{q > q0}`.
"""

from std.collections import Dict
from finite_exact.rat_q import Q
from finite_linear_algebra.qpoly import add, evaluate, mul, neg, normalize, scale, sign_of, sub
from finite_linear_algebra.scalar import q_int
from psc.exact import q_string
from psc.symbolic_line import TPoly, LineField, least_integer_at, primitive_support, qx_of, zero_descendants

comptime UX = List[Q]  # a polynomial in s2, ascending (the rows of P2)


def ux_const(c: Int) -> UX:
    return normalize([q_int(c)])


def ux_affine(c0: Int, c1: Int) -> UX:
    """`c0 + c1 s2`."""
    return normalize([q_int(c0), q_int(c1)])

comptime P2 = List[UX]  # sum_i row_i(s2) s1^i
comptime TP2 = List[P2]  # a polynomial in t over Q[s1, s2], ascending
comptime CONE_SAMPLE = 200
comptime CONE_VERTEX_CAP = 20000
comptime POLYA_MAX = 24


# ---------------------------------------------------------------------------
# Polynomials in s = (s1, s2).
# ---------------------------------------------------------------------------


def p2_norm(p: P2) -> P2:
    var width = len(p)
    while width > 0 and len(normalize(p[width - 1])) == 0:
        width -= 1
    var out = P2()
    for i in range(width):
        out.append(normalize(p[i]))
    return out^


def p2_row(p: P2, i: Int) -> UX:
    if i < len(p):
        return p[i].copy()
    return UX()


def p2_add(a: P2, b: P2) -> P2:
    var width = len(a) if len(a) > len(b) else len(b)
    var out = P2()
    for i in range(width):
        out.append(add(p2_row(a, i), p2_row(b, i)))
    return p2_norm(out)


def p2_neg(p: P2) -> P2:
    var out = P2()
    for i in range(len(p)):
        out.append(neg(p[i]))
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
        out.append(UX())
    for i in range(len(x)):
        for j in range(len(y)):
            out[i + j] = add(out[i + j], mul(x[i], y[j]))
    return p2_norm(out)


def p2_scale(p: P2, c: Q) -> P2:
    var out = P2()
    for i in range(len(p)):
        out.append(scale(p[i], c))
    return p2_norm(out)


def p2_const(c: Int) -> P2:
    return p2_norm([ux_const(c)])


def p2_affine(c0: Int, c1: Int, c2: Int) -> P2:
    """`c0 + c1 s1 + c2 s2`."""
    return p2_norm([ux_affine(c0, c2), ux_const(c1)])


def p2_deg(p: P2) -> Int:
    """Total degree; -1 for the zero polynomial."""
    var f = p2_norm(p)
    var d = -1
    for i in range(len(f)):
        if len(f[i]) > 0 and i + len(f[i]) - 1 > d:
            d = i + len(f[i]) - 1
    return d


def p2_constant(p: P2) -> Q:
    var f = p2_norm(p)
    if len(f) == 0 or len(f[0]) == 0:
        return Q.zero()
    return f[0][0].copy()


def p2_at(p: P2, s1: Int, s2: Int) -> Q:
    var total = Q.zero()
    for index in range(len(p)):
        total = total.mul(q_int(s1)).add(evaluate(p[len(p) - 1 - index], q_int(s2)))
    return total^


def p2_key(p: P2) -> String:
    var f = p2_norm(p)
    var out = String("")
    for i in range(len(f)):
        out += "["
        for j in range(len(f[i])):
            out += q_string(f[i][j]) + ","
        out += "]"
    return out^


def _ux_shift(f: UX, n: Int) -> UX:
    """`f(n + v)` as a polynomial in `v`."""
    var out = UX()
    var x = ux_affine(n, 1)
    for index in range(len(f)):
        out = add(mul(out, x), [f[len(f) - 1 - index].copy()])
    return normalize(out)


def p2_shift(p: P2, n1: Int, n2: Int) -> P2:
    """`p(n1 + u, n2 + v)` as a polynomial in `(u, v)`."""
    var out = P2()
    var x = p2_affine(n1, 1, 0)
    for index in range(len(p)):
        out = p2_add(p2_mul(out, x), p2_norm([_ux_shift(p[len(p) - 1 - index], n2)]))
    return out^


def _uses(p: P2) -> List[Bool]:
    """Which coordinates occur in `p`."""
    var f = p2_norm(p)
    var out = List[Bool](length=2, fill=False)
    if len(f) > 1:
        out[0] = True
    for i in range(len(f)):
        if len(f[i]) > 1:
            out[1] = True
    return out^


def _positive_coefficients(p: P2) -> Bool:
    """Every coefficient nonnegative and the constant term positive."""
    var f = p2_norm(p)
    if len(f) == 0 or len(f[0]) == 0 or not Q.zero().lt(f[0][0]):
        return False
    for i in range(len(f)):
        for j in range(len(f[i])):
            if f[i][j].lt(Q.zero()):
                return False
    return True


# ---------------------------------------------------------------------------
# Signs on the region.
# ---------------------------------------------------------------------------


struct Region(Copyable, Movable):
    """The integer points `s1 >= n1`, `s2 >= n2` (all of them, or a line of them
    when one coordinate does not occur)."""

    var n1: Int
    var n2: Int
    var queries: Int
    var polya: Int  # the largest Polya exponent a certificate used
    var memo: Dict[String, Int]

    def __init__(out self, n1: Int, n2: Int):
        self.n1 = n1
        self.n2 = n2
        self.queries = 0
        self.polya = 0
        self.memo = Dict[String, Int]()

    def positive(mut self, p: P2) -> Bool:
        """`p > 0` at every real point of the region, certified."""
        var h = p2_shift(p, self.n1, self.n2)
        var uses = _uses(h)
        var lift = p2_affine(1, 1 if uses[0] else 0, 1 if uses[1] else 0)
        for k in range(POLYA_MAX + 1):
            if _positive_coefficients(h):
                if k > self.polya:
                    self.polya = k
                return True
            h = p2_mul(h, lift)
        return False

    def try_sign(mut self, p: P2) -> Int:
        """The constant sign of `p` on the region, or 2 when none is certified."""
        var f = p2_norm(p)
        if len(f) == 0:
            return 0
        var k = p2_key(f)
        var hit = self.memo.get(k)
        if hit:
            return hit.value()
        self.queries += 1
        var s = sign_of(p2_at(f, self.n1 + 7, self.n2 + 13))
        if s == 0:
            s = sign_of(p2_at(f, self.n1 + 11, self.n2 + 5))
        var out = 2
        if s != 0 and self.positive(f.copy() if s > 0 else p2_neg(f)):
            out = s
        self.memo[k] = out
        return out

    def sign(mut self, p: P2) raises -> Int:
        var s = self.try_sign(p)
        if s == 2:
            raise Error("a sign is not certified on the region (", self.n1, ", ", self.n2, "): ", p2_key(p))
        return s


# ---------------------------------------------------------------------------
# Polynomials in t over Q[s].
# ---------------------------------------------------------------------------


def t2_norm(p: TP2) -> TP2:
    var width = len(p)
    while width > 0 and len(p2_norm(p[width - 1])) == 0:
        width -= 1
    var out = TP2()
    for i in range(width):
        out.append(p2_norm(p[i]))
    return out^


def t2_coeff(p: TP2, k: Int) -> P2:
    if k < len(p):
        return p[k].copy()
    return P2()


def t2_add(a: TP2, b: TP2) -> TP2:
    var width = len(a) if len(a) > len(b) else len(b)
    var out = TP2()
    for k in range(width):
        out.append(p2_add(t2_coeff(a, k), t2_coeff(b, k)))
    return t2_norm(out)


def t2_scale(p: TP2, c: P2) -> TP2:
    var out = TP2()
    for k in range(len(p)):
        out.append(p2_mul(p[k], c))
    return t2_norm(out)


def t2_neg(p: TP2) -> TP2:
    return t2_scale(p, p2_const(-1))


def t2_sub(a: TP2, b: TP2) -> TP2:
    return t2_add(a, t2_neg(b))


def t2_mul(a: TP2, b: TP2) -> TP2:
    var x = t2_norm(a)
    var y = t2_norm(b)
    if len(x) == 0 or len(y) == 0:
        return TP2()
    var out = TP2()
    for _ in range(len(x) + len(y) - 1):
        out.append(P2())
    for i in range(len(x)):
        for j in range(len(y)):
            out[i + j] = p2_add(out[i + j], p2_mul(x[i], y[j]))
    return t2_norm(out)


def t2_const(c: P2) -> TP2:
    return t2_norm([c.copy()])


def t2_t() -> TP2:
    return t2_norm([P2(), p2_const(1)])


def t2_key(p: TP2) -> String:
    var out = String("")
    for k in range(len(p)):
        out += "{" + p2_key(p[k]) + "}"
    return out^


def t2_deriv(p: TP2) -> TP2:
    var out = TP2()
    for k in range(1, len(p)):
        out.append(p2_scale(p[k], q_int(k)))
    return t2_norm(out)


def t2_mod_monic(a: TP2, b: TP2) raises -> TP2:
    """`a mod b` for `b` monic in `t`."""
    var bb = t2_norm(b)
    var db = len(bb) - 1
    if db < 0 or p2_deg(p2_sub(bb[db], p2_const(1))) >= 0:
        raise Error("reduction modulo a polynomial that is not monic")
    var r = t2_norm(a)
    while len(r) - 1 >= db and len(r) > 0:
        var dr = len(r) - 1
        var top = r[dr].copy()
        var shifted = TP2()
        for _ in range(dr - db):
            shifted.append(P2())
        for i in range(len(bb)):
            shifted.append(p2_mul(bb[i], top))
        r = t2_sub(r, shifted)
    return r^


def t2_homog_at(p: TP2, num: P2, den: P2, d: Int) -> P2:
    """`den^d p(num / den)` for `deg p <= d`: the sign of `p(num / den)` when `den > 0`."""
    var total = P2()
    var dpow = p2_const(1)
    var parts = List[P2]()  # parts[k] = num^k
    parts.append(p2_const(1))
    for k in range(1, len(p)):
        parts.append(p2_mul(parts[k - 1], num))
    for j in range(d + 1):
        var k = d - j  # term p_k num^k den^(d - k), accumulated from k = d down
        if k < len(p):
            total = p2_add(total, p2_mul(p2_mul(p[k], parts[k]), dpow))
        dpow = p2_mul(dpow, den)
    return total^


def t2_at_point(p: TP2, s1: Int, s2: Int) -> TPoly:
    """Substitute integers for `s`: a polynomial in `t` with constant coefficients,
    in the line engine's representation."""
    var out = TPoly()
    for k in range(len(p)):
        out.append(qx_of(p2_at(p[k], s1, s2)))
    var width = len(out)
    while width > 0 and len(out[width - 1]) == 0:
        width -= 1
    var trimmed = TPoly()
    for k in range(width):
        trimmed.append(out[k].copy())
    return trimmed^


# ---------------------------------------------------------------------------
# Rational functions and brackets of the Perron root.
# ---------------------------------------------------------------------------


struct Frac2(Copyable, Movable):
    """`num / den`; `den` is certified positive on the region before use."""

    var num: P2
    var den: P2

    def __init__(out self, var num: P2, var den: P2):
        self.num = num^
        self.den = den^


def r2_const(p: P2) -> Frac2:
    return Frac2(p.copy(), p2_const(1))


def r2_add(a: Frac2, b: Frac2) -> Frac2:
    return Frac2(p2_add(p2_mul(a.num, b.den), p2_mul(b.num, a.den)), p2_mul(a.den, b.den))


def r2_sub(a: Frac2, b: Frac2) -> Frac2:
    return Frac2(p2_sub(p2_mul(a.num, b.den), p2_mul(b.num, a.den)), p2_mul(a.den, b.den))


def r2_mul(a: Frac2, b: Frac2) -> Frac2:
    return Frac2(p2_mul(a.num, b.num), p2_mul(a.den, b.den))


def r2_div(a: Frac2, b: Frac2) -> Frac2:
    return Frac2(p2_mul(a.num, b.den), p2_mul(a.den, b.num))


struct Bracket(Copyable, Movable):
    var lo: Frac2
    var hi: Frac2

    def __init__(out self, var lo: Frac2, var hi: Frac2):
        self.lo = lo^
        self.hi = hi^


# ---------------------------------------------------------------------------
# The cone.
# ---------------------------------------------------------------------------


def w2_add(a: List[P2], b: List[P2]) -> List[P2]:
    var out = List[P2]()
    for i in range(3):
        out.append(p2_add(a[i], b[i]))
    return out^


def w2_sub(a: List[P2], b: List[P2]) -> List[P2]:
    var out = List[P2]()
    for i in range(3):
        out.append(p2_sub(a[i], b[i]))
    return out^


def w2_unit(i: Int, c: P2) -> List[P2]:
    var out = List[P2]()
    for k in range(3):
        out.append(c.copy() if k == i else P2())
    return out^


def w2_zero() -> List[P2]:
    return w2_unit(0, P2())


struct ConeVertex(Copyable, Movable):
    var top: Int
    var bottom: Int
    var w: List[P2]

    def __init__(out self, top: Int, bottom: Int, var w: List[P2]):
        self.top = top
        self.bottom = bottom
        self.w = w^

    def key(self) -> String:
        var out = String(self.top) + "|" + String(self.bottom)
        for i in range(3):
            out += "|" + p2_key(self.w[i])
        return out^

    def is_zero_offset(self) -> Bool:
        for i in range(3):
            if len(p2_norm(self.w[i])) > 0:
                return False
        return True


struct Cone(Copyable, Movable):
    """Images `first[a] y^(run[a]) last[a]`, `run[a]` affine in `s`, with brackets of `beta`."""

    var first: List[Int]
    var last: List[Int]
    var run: List[P2]
    var y: Int
    var m: List[List[P2]]
    var chi: TP2
    var ell: List[TP2]
    var brackets: List[Bracket]

    def __init__(out self, first: List[Int], last: List[Int], run: List[P2], y: Int, var brackets: List[Bracket]) raises:
        self.first = first.copy()
        self.last = last.copy()
        self.run = run.copy()
        self.y = y
        self.brackets = brackets^
        self.m = List[List[P2]]()
        for _ in range(3):
            var row = List[P2]()
            for _ in range(3):
                row.append(P2())
            self.m.append(row^)
        for b in range(3):
            self.m[first[b]][b] = p2_add(self.m[first[b]][b], p2_const(1))
            self.m[last[b]][b] = p2_add(self.m[last[b]][b], p2_const(1))
            self.m[y][b] = p2_add(self.m[y][b], run[b])
        var a = List[List[TP2]]()  # t I - M
        for i in range(3):
            var row = List[TP2]()
            for j in range(3):
                var e = t2_neg(t2_const(self.m[i][j]))
                if i == j:
                    e = t2_add(e, t2_t())
                row.append(e^)
            a.append(row^)
        self.chi = t2_sub(
            t2_add(
                t2_mul(a[0][0], t2_sub(t2_mul(a[1][1], a[2][2]), t2_mul(a[1][2], a[2][1]))),
                t2_mul(a[0][2], t2_sub(t2_mul(a[1][0], a[2][1]), t2_mul(a[1][1], a[2][0]))),
            ),
            t2_mul(a[0][1], t2_sub(t2_mul(a[1][0], a[2][2]), t2_mul(a[1][2], a[2][0]))),
        )
        # left null vector of M - t I: the cross product of its first two columns
        var col = List[List[TP2]]()
        for j in range(3):
            var c = List[TP2]()
            for i in range(3):
                c.append(t2_neg(a[i][j]))
            col.append(c^)
        self.ell = List[TP2]()
        self.ell.append(t2_sub(t2_mul(col[0][1], col[1][2]), t2_mul(col[0][2], col[1][1])))
        self.ell.append(t2_sub(t2_mul(col[0][2], col[1][0]), t2_mul(col[0][0], col[1][2])))
        self.ell.append(t2_sub(t2_mul(col[0][0], col[1][1]), t2_mul(col[0][1], col[1][0])))

    def mw(self, w: List[P2]) -> List[P2]:
        var out = List[P2]()
        for i in range(3):
            var s = P2()
            for j in range(3):
                s = p2_add(s, p2_mul(self.m[i][j], w[j]))
            out.append(s^)
        return out^

    def t_of(self, w: List[P2]) -> TP2:
        var s = TP2()
        for i in range(3):
            s = t2_add(s, t2_scale(self.ell[i], w[i]))
        return s^

    def sign_at_beta(self, g: TP2, mut region: Region) raises -> Int:
        """The sign of `g(beta)` on the region, decided on a bracket; raises when undecided."""
        var r = t2_mod_monic(g, self.chi)
        if len(r) == 0:
            return 0
        if len(r) == 1:
            return region.sign(r[0])
        var dr = t2_deriv(r)
        for i in range(len(self.brackets)):
            ref br = self.brackets[i]
            var sl = region.try_sign(t2_homog_at(r, br.lo.num, br.lo.den, 2))
            if sl != 1 and sl != -1:
                continue
            if region.try_sign(t2_homog_at(r, br.hi.num, br.hi.den, 2)) != sl:
                continue
            if len(r) == 2:
                return sl
            var lead = region.try_sign(r[2])
            if (lead == 1 or lead == -1) and lead != sl:
                return sl  # bends away from zero: the minimum of |g| is at an end
            var dl = region.try_sign(t2_homog_at(dr, br.lo.num, br.lo.den, 1))
            if (dl == 1 or dl == -1) and region.try_sign(t2_homog_at(dr, br.hi.num, br.hi.den, 1)) == dl:
                return sl  # monotone on the bracket
        raise Error("a sign at beta is not decided on any bracket: ", t2_key(r))


struct ConeCertificate(Copyable, Movable):
    var holds: Bool
    var ell_sign: Int
    var reason: String

    def __init__(out self, holds: Bool, ell_sign: Int, reason: String):
        self.holds = holds
        self.ell_sign = ell_sign
        self.reason = reason


def certify_cone(cone: Cone, mut region: Region) raises -> ConeCertificate:
    """PIP at every integer point of the region, and the root in each bracket is beta.

    Support fixed and primitive; `det M` a nonzero constant whose divisors are not
    roots of `chi`; for every bracket `|det M| < L`, `chi(L) < 0 < chi(U)` (a
    root in `(L, U)`); and the other two roots in the open unit disc, by Rouche
    (`rouche_disc`) where its three signs are certified, else by the Jury
    conditions `|v| < 1`, `|u| < 1 + v` on the quotient
    `t^2 + u t + v = chi / (t - beta)` (`u = c_2 + beta`, `v = det M / beta`). Then `chi` is
    irreducible, `beta` is its only root outside the disc and the root in every
    bracket. Also fixes the sign that makes the tile lengths positive."""
    var chi = cone.chi.copy()
    if len(chi) != 4 or p2_deg(p2_sub(chi[3], p2_const(1))) >= 0:
        raise Error("the characteristic polynomial is not a monic cubic")
    var det_p = p2_neg(chi[0])
    if p2_deg(det_p) > 0:
        raise Error("the cone's determinant is not constant")
    var det = p2_constant(det_p)
    if det.eq(Q.zero()):
        return ConeCertificate(False, 0, "det M = 0")
    var support = List[Int]()
    for i in range(3):
        for j in range(3):
            var s = region.sign(cone.m[i][j])
            if s < 0:
                return ConeCertificate(False, 0, "a negative matrix entry")
            support.append(1 if s > 0 else 0)
    if not primitive_support(support):
        return ConeCertificate(False, 0, "support not primitive")
    var dabs = det.copy() if Q.zero().lt(det) else det.neg()
    var dn = 1
    while q_int(dn).le(dabs):
        if dabs.div(q_int(dn)).mul(q_int(dn)).eq(dabs):
            for sgn in range(2):
                var x = q_int(dn) if sgn == 0 else q_int(-dn)
                if region.sign(t2_homog_at(chi, p2_norm([[x.copy()]]), p2_const(1), 3)) == 0:
                    return ConeCertificate(False, 0, "a rational root")
        dn += 1
        if dn > 1000:
            raise Error("determinant too large for the rational-root screen")
    if len(cone.brackets) == 0:
        raise Error("a cone needs at least one bracket of its Perron root")
    for i in range(len(cone.brackets)):
        ref br = cone.brackets[i]
        if region.sign(br.lo.den) <= 0 or region.sign(br.hi.den) <= 0:
            return ConeCertificate(False, 0, "a bracket denominator is not positive")
        if region.sign(p2_sub(br.lo.num, p2_scale(br.lo.den, dabs))) <= 0:
            return ConeCertificate(False, 0, "a bracket does not lie above |det M|")
        if region.sign(t2_homog_at(chi, br.lo.num, br.lo.den, 3)) >= 0:
            return ConeCertificate(False, 0, "chi(L) is not negative")
        if region.sign(t2_homog_at(chi, br.hi.num, br.hi.den, 3)) <= 0:
            return ConeCertificate(False, 0, "chi(U) is not positive")
    if not rouche_disc(chi, region):
        var c2 = chi[2].copy()
        var dpoly = p2_norm([[det.copy()]])
        var jury_plus = t2_norm([dpoly.copy(), p2_add(c2, p2_const(1)), p2_const(1)])  # beta^2 + (c2 + 1) beta + det
        var jury_minus = t2_norm([dpoly.copy(), p2_sub(p2_const(1), c2), p2_const(-1)])  # -beta^2 + (1 - c2) beta + det
        if cone.sign_at_beta(jury_plus, region) <= 0 or cone.sign_at_beta(jury_minus, region) <= 0:
            return ConeCertificate(False, 0, "a Jury condition fails")
    var s = cone.sign_at_beta(cone.ell[cone.y], region)
    if s == 0:
        return ConeCertificate(False, 0, "a tile length vanishes")
    for i in range(3):
        if cone.sign_at_beta(cone.ell[i], region) != s:
            return ConeCertificate(False, 0, "tile lengths of mixed sign")
    return ConeCertificate(True, s, "")


def rouche_disc(chi: TP2, mut region: Region) -> Bool:
    """`chi = t^3 + c2 t^2 + c1 t + c0` with `|c2| > 1 + |c1| + |c0|` on the
    region, certified by three plain region signs and none at beta. On
    `|t| = 1` the term `c2 t^2` then dominates the rest strictly, so (Rouche)
    `chi` has two roots in the open unit disc and none on the circle, as
    `c2 t^2` does. This is what the Jury conditions give, read without a bracket.
    `False` when a sign is not certified: the caller falls back to Jury."""
    var margin = p2_const(-1)
    for k in range(3):
        var sk = region.try_sign(chi[k])
        if sk == 2 or (k == 2 and sk == 0):
            return False
        margin = p2_add(margin, chi[k]) if (k == 2) == (sk > 0) else p2_sub(margin, chi[k])
    return region.try_sign(margin) == 1


struct ConeGraph(Copyable, Movable):
    var vertices: List[ConeVertex]
    var adj: List[List[Int]]
    var pip: Bool
    var reason: String
    var queries: Int
    var polya: Int

    def __init__(out self):
        self.vertices = List[ConeVertex]()
        self.adj = List[List[Int]]()
        self.pip = False
        self.reason = ""
        self.queries = 0
        self.polya = 0

    def size(self) -> Int:
        return len(self.vertices)


struct _ConeClosure:
    var cone: Cone
    var sign: Int  # orientation that makes ell positive at beta
    var region: Region
    var index: Dict[String, Int]
    var vertices: List[ConeVertex]
    var adj: List[List[Int]]
    var queue: List[Int]
    var memo: Dict[String, Int]

    def __init__(out self, var cone: Cone, sign: Int, var region: Region):
        self.cone = cone^
        self.sign = sign
        self.region = region^
        self.index = Dict[String, Int]()
        self.vertices = List[ConeVertex]()
        self.adj = List[List[Int]]()
        self.queue = List[Int]()
        self.memo = Dict[String, Int]()

    def positive(mut self, g: TP2) raises -> Int:
        var h = t2_scale(g, p2_const(self.sign))
        var k = t2_key(h)
        var hit = self.memo.get(k)
        if hit:
            return hit.value()
        var s = self.cone.sign_at_beta(h, self.region)
        self.memo[k] = s
        return s

    def real(mut self, a: Int, b: Int, w: List[P2]) raises -> Bool:
        """`-ell_b < <ell, w> < ell_a`."""
        var t = self.cone.t_of(w)
        if self.positive(t2_add(self.cone.ell[b], t)) <= 0:
            return False
        return self.positive(t2_sub(self.cone.ell[a], t)) > 0

    def intern(mut self, var v: ConeVertex) raises -> Int:
        var k = v.key()
        var hit = self.index.get(k)
        if hit:
            return hit.value()
        if len(self.vertices) >= CONE_VERTEX_CAP:
            raise Error("symbolic cone closure exceeded its vertex cap")
        var i = len(self.vertices)
        self.index[k] = i
        self.vertices.append(v^)
        self.adj.append(List[Int]())
        self.queue.append(i)
        return i

    def prefix(self, a: Int, seg: Int) -> List[P2]:
        """Parikh vector of `sigma(a)` before segment `seg` (0 first letter, 1 run, 2 last letter)."""
        var v = w2_zero()
        if seg >= 1:
            v = w2_add(v, w2_unit(self.cone.first[a], p2_const(1)))
        if seg >= 2:
            v = w2_add(v, w2_unit(self.cone.y, self.cone.run[a]))
        return v^

    def has_run(mut self, a: Int) raises -> Bool:
        var s = self.region.sign(self.cone.run[a])
        if s < 0:
            raise Error("a run length is negative on the region")
        return s > 0

    def letter(self, a: Int, seg: Int) -> Int:
        if seg == 0:
            return self.cone.first[a]
        if seg == 1:
            return self.cone.y
        return self.cone.last[a]

    def _least_at(self, h0: TP2, h1: TP2, s1: Int, s2: Int, strict: Bool) raises -> Int:
        var field = LineField(t2_at_point(self.cone.chi, s1, s2))
        var g0 = t2_at_point(t2_scale(h0, p2_const(self.sign)), s1, s2)
        var g1 = t2_at_point(t2_scale(h1, p2_const(self.sign)), s1, s2)
        return least_integer_at(field, g0, g1, strict)

    def least_m(mut self, h0: TP2, h1: TP2, strict: Bool) raises -> P2:
        """The least integer `m(s)` with `h0 + m h1 > 0` (`>= 0` if not `strict`) at
        beta (`h1 > 0`), affine in `s`, fitted at three sample points and certified."""
        var a1 = self.region.n1 + CONE_SAMPLE
        var a2 = self.region.n2 + CONE_SAMPLE
        var v0 = self._least_at(h0, h1, a1, a2, strict)
        var v1 = self._least_at(h0, h1, a1 + CONE_SAMPLE, a2, strict)
        var v2 = self._least_at(h0, h1, a1, a2 + CONE_SAMPLE, strict)
        var k1 = (v1 - v0) // CONE_SAMPLE
        var k2 = (v2 - v0) // CONE_SAMPLE
        if v1 - v0 != k1 * CONE_SAMPLE or v2 - v0 != k2 * CONE_SAMPLE:
            raise Error("a run-position bound is not affine in s at the samples")
        var mu = p2_affine(v0 - k1 * a1 - k2 * a2, k1, k2)
        var floor_sign = 1 if strict else 0
        if self.positive(t2_add(h0, t2_scale(h1, mu))) < floor_sign:
            raise Error("a fitted run-position bound fails certification (low side)")
        if self.positive(t2_add(h0, t2_scale(h1, p2_sub(mu, p2_const(1))))) >= floor_sign:
            raise Error("a fitted run-position bound fails certification (high side)")
        return mu^

    def expand(mut self, i: Int) raises:
        var v = self.vertices[i].copy()
        if v.top == v.bottom and v.is_zero_offset():
            return
        var mw = self.cone.mw(v.w)
        var ell = self.cone.ell.copy()
        var y = self.cone.y
        for sa in range(3):
            if sa == 1 and not self.has_run(v.top):
                continue
            for sb in range(3):
                if sb == 1 and not self.has_run(v.bottom):
                    continue
                var base = w2_sub(w2_add(mw, self.prefix(v.bottom, sb)), self.prefix(v.top, sa))
                var a2 = self.letter(v.top, sa)
                var b2 = self.letter(v.bottom, sb)
                if sa != 1 and sb != 1:
                    if self.real(a2, b2, base):
                        var c = self.intern(ConeVertex(a2, b2, base^))
                        self.adj[i].append(c)
                    continue
                # offset base + m e_y, m = k_b - k_a in [rlo, rhi]; real iff lower(m) > 0 and upper(m) < 0
                var t = self.cone.t_of(base)
                var lower = t2_add(ell[b2], t)
                var upper = t2_sub(t, ell[a2])
                var rlo = p2_neg(p2_sub(self.cone.run[v.top], p2_const(1))) if sa == 1 else P2()
                var rhi = p2_sub(self.cone.run[v.bottom], p2_const(1)) if sb == 1 else P2()
                if self.positive(t2_add(lower, t2_scale(ell[y], rhi))) <= 0:
                    continue  # even the last run position is not real
                if self.positive(t2_add(upper, t2_scale(ell[y], rlo))) >= 0:
                    continue  # even the first run position is not real
                # a run end inside the real interval clips it; otherwise the interval's end is fitted
                var low = rlo.copy()
                if self.positive(t2_add(lower, t2_scale(ell[y], rlo))) <= 0:
                    low = self.least_m(lower, ell[y], True)
                var high = rhi.copy()
                if self.positive(t2_add(upper, t2_scale(ell[y], rhi))) >= 0:
                    high = p2_sub(self.least_m(upper, ell[y], False), p2_const(1))
                var gap = p2_sub(high, low)
                if p2_deg(gap) > 0:
                    if self.region.sign(gap) < 0:
                        continue
                    raise Error("a run-position range grows with s")
                var g0 = p2_constant(gap)
                if g0.lt(Q.zero()):
                    continue
                var width = 0
                while q_int(width + 1).le(g0):
                    width += 1
                for d in range(width + 1):
                    var child = w2_add(base, w2_unit(y, p2_add(low, p2_const(d))))
                    var c = self.intern(ConeVertex(a2, b2, child^))
                    self.adj[i].append(c)

    def seeds(mut self) raises:
        for a in range(3):
            for b in range(a + 1, 3):
                var tops = List[Int]([a, b])
                var bots = List[Int]([b, a])
                var top_pos = List[List[P2]]()
                top_pos.append(w2_zero())
                top_pos.append(w2_unit(a, p2_const(1)))
                var bot_pos = List[List[P2]]()
                bot_pos.append(w2_zero())
                bot_pos.append(w2_unit(b, p2_const(1)))
                for i in range(2):
                    for j in range(2):
                        var w = w2_sub(bot_pos[j], top_pos[i])
                        if self.real(tops[i], bots[j], w):
                            _ = self.intern(ConeVertex(tops[i], bots[j], w^))


def symbolic_cone_graph(var cone: Cone, var region: Region) raises -> ConeGraph:
    """The swap-seed overlap graph on every integer point of the region; see the module docstring."""
    var cert = certify_cone(cone, region)
    var out = ConeGraph()
    if not cert.holds:
        out.reason = cert.reason
        return out^
    var cl = _ConeClosure(cone^, cert.ell_sign, region^)
    cl.seeds()
    var done = 0
    while done < len(cl.queue):
        var i = cl.queue[done]
        done += 1
        cl.expand(i)
    out.pip = True
    out.queries = cl.region.queries
    out.polya = cl.region.polya
    out.vertices = cl.vertices.copy()
    out.adj = cl.adj.copy()
    return out^


def cone_offset_zero_reachable(g: ConeGraph) -> List[Bool]:
    """Whether each vertex has an offset-zero descendant (itself included)."""
    var zero = List[Bool]()
    for i in range(g.size()):
        zero.append(g.vertices[i].is_zero_offset())
    return zero_descendants(g.adj, zero)
