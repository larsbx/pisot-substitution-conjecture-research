"""The seed-patch overlap graph of a one-parameter line, for every large q at once.

docs/p1b-symbolic-line-2026-10-07.md. A *line* is a family `sigma_q` on three
letters whose images are `f_a y^(n_a(q)) l_a`, a first letter, a run of the
letter `y` of length affine in `q`, and a last letter. This module computes the
overlap graph reachable from the swap seeds of `sigma_q` **as a function of q**:
vertices are `(a, b, w)` with `w` a vector of integer polynomials in `q`, and
every child is decided for all `q >= q0` at once, with `q0` certified.

Decisions. Every question the closure asks is the sign of an element
`G(q, beta)` of `Q[q][t] / (chi)` at the Perron root `beta = beta(q)`: whether a
child overlap is real (both open-interval conditions), and the integer range of
run positions a child can occupy. A sign is decided by a *parametric
Sturm--Tarski query*: the signed pseudo-remainder sequence of `(chi, chi' G)`
over `Q[q]`, read at `t = 1` and `t = +infinity`. Pseudo-division multiplies by
an even power of a leading coefficient, so every term is a positive multiple of
the classical one wherever those coefficients do not vanish. Each entry of the
sequence is then a polynomial in `q`, and its sign for every `q` above its
largest real root is the sign of its leading coefficient; that root is isolated
exactly (`largest_root_bracket`) and the maximum over all queries is the
threshold `q0`. Under the line's certified PIP property (one root of `chi` in
`(1, infinity)`), the query is the sign of `G(beta)`.

Run positions. A child inside a run sits at an integer offset `m` whose real
range is an open interval of bounded length. The integer endpoints are
**guessed** by exact evaluation at sample values of `q`, fitted as affine
functions of `q`, and then **certified** by two sign queries each. A guess that
fails certification raises: the search only proposes.

What the closure means. If every decision holds for `q >= q0`, then for every
such `q` the exact seed-reachable overlap graph of `sigma_q`
(`psc.overlap_seed_patch`) is the symbolic graph with `q` substituted: the seeds
agree, and each vertex has the same children. A run that meets a decision it
cannot certify, a range that grows with `q`, or the vertex cap, raises; nothing
here returns a partial graph as if it were complete.
"""

from std.collections import Dict
from finite_exact.rat_q import Q
from finite_linear_algebra.qpoly import degree, evaluate, normalize, sign_of
from finite_linear_algebra.scalar import q_int, q_is_zero
from finite_linear_algebra.cauchy_bound import root_bound
from finite_linear_algebra.sturm_sequence import largest_root_bracket, sturm_chain, variation_difference
from psc.exact import q_string
from psc.param_poly import (
    P2,
    p2_add,
    p2_affine,
    p2_at,
    p2_at_int,
    p2_const,
    p2_const_value,
    p2_from_s,
    p2_has_d,
    p2_is_const,
    p2_is_zero,
    p2_key,
    p2_mul,
    p2_neg,
    p2_norm,
    p2_scale,
    p2_sub,
    quadrant_sign,
)

comptime QX = P2  # a polynomial in the parameters: q (= s) for a line, (s, d) for a wedge
comptime TPoly = List[QX]  # a polynomial in t whose coefficients are polynomials in the parameters
comptime SAMPLE_BASE = 200  # sample points for fitting run-position ranges: once and twice this
comptime SYMBOLIC_VERTEX_CAP = 20000
comptime ROOT_STEPS = 400
comptime QUADRANT_STEPS = 10  # quadrant enlargements tried, up to 2^9 on each axis
comptime POLYA_DEGREE = 4  # largest Polya multiplier exponent tried
comptime OPEN_SIGN = 2  # a sign the quadrant does not certify
comptime MAX_BRACKET_LEVEL = 4
comptime BRACKET_SEED_RANGE = 8


# ---------------------------------------------------------------------------
# Polynomials in q, and eventual signs with a certified threshold.
# ---------------------------------------------------------------------------


def qx_const(c: Int) -> QX:
    return p2_const(c)


def qx_affine(c0: Int, c1: Int, c2: Int = 0) -> QX:
    """`c0 + c1 s + c2 d`; on a line `s = q` and `c2 = 0`."""
    return p2_affine(c0, c1, c2)


def qx_at(p: QX, q: Int, d: Int = 0) -> Q:
    return p2_at_int(p, q, d)


struct Eventual(Copyable, Movable):
    """Signs of polynomials in the parameters on a running region.

    On a line the region is `q > threshold`: `threshold` is a rational strictly
    above every real root of every polynomial in `q` whose sign was read. On a
    wedge (parameters `s = q` and `d`) it is the open quadrant
    `{s > threshold, d > d_threshold}`: a polynomial without `d` is read as on a
    line, one with `d` by a Polya certificate on the quadrant
    (`psc.param_poly.quadrant_sign`), enlarging the quadrant geometrically until
    one holds; none within `QUADRANT_STEPS` raises. The region only ever
    shrinks, so every sign read earlier still holds on it. `queries` counts
    the polynomials read."""

    var threshold: Q
    var d_threshold: Q
    var queries: Int

    def __init__(out self):
        self.threshold = Q.zero()
        self.d_threshold = Q.zero()
        self.queries = 0

    def sign(mut self, p: QX) raises -> Int:
        var s = self.try_sign(p)
        if s == OPEN_SIGN:
            raise Error("no quadrant certificate for a sign: it may change with the ratio of the parameters")
        return s

    def try_sign(mut self, p: QX) raises -> Int:
        """As `sign`, but `OPEN_SIGN` where a polynomial in `d` has no quadrant
        certificate, leaving the region unchanged."""
        var f2 = p2_norm(p)
        self.queries += 1
        if len(f2) == 0:
            return 0
        if p2_has_d(f2):
            return self._quadrant(f2)
        var f = f2[0].copy()
        if degree(f) >= 1 and not self._no_root_above(f, self.threshold):
            var bracket = largest_root_bracket(f, Q.one(), ROOT_STEPS)
            var above = bracket.hi.copy() if bracket.found else root_bound(f)
            if self.threshold.lt(above):
                self.threshold = above^
        return sign_of(f[len(f) - 1])

    def _no_root_above(self, f: List[Q], x: Q) -> Bool:
        """No real root of `f` in `[x, infinity)`: one Sturm count, the common case
        once the threshold has grown past the roots that matter."""
        if q_is_zero(evaluate(f, x)):
            return False
        var chain = sturm_chain(f)
        return variation_difference(chain, x, root_bound(f)) == 0

    def _quadrant(mut self, f: QX) raises -> Int:
        for k in range(QUADRANT_STEPS):
            for i in range(k + 1):
                var a = _grown(self.threshold, i)
                var b = _grown(self.d_threshold, k - i)
                var s = quadrant_sign(f, a, b, POLYA_DEGREE)
                if s != 0:
                    self.threshold = a^
                    self.d_threshold = b^
                    return s
        return OPEN_SIGN

    def first_integer_above(self) -> Int:
        """The least integer `q0` with `q0 > threshold`."""
        return _first_integer_above(self.threshold)

    def first_integer_above_d(self) -> Int:
        """The least integer `d0` with `d0 > d_threshold`."""
        return _first_integer_above(self.d_threshold)


def _grown(x: Q, i: Int) -> Q:
    """`x` for `i = 0`, else `max(x, 1) 2^i`."""
    if i == 0:
        return x.copy()
    var base = x.copy() if Q.one().lt(x) else Q.one()
    return base.mul(q_int(1 << i))


def _first_integer_above(x: Q) -> Int:
    var n = 0
    while not x.lt(q_int(n)):
        n += 1
    return n


# ---------------------------------------------------------------------------
# Polynomials in t over Q[q].
# ---------------------------------------------------------------------------


def tp_norm(p: TPoly) -> TPoly:
    var width = len(p)
    while width > 0 and p2_is_zero(p[width - 1]):
        width -= 1
    var out = TPoly()
    for i in range(width):
        out.append(p2_norm(p[i]))
    return out^


def tp_deg(p: TPoly) -> Int:
    return len(tp_norm(p)) - 1


def tp_coeff(p: TPoly, k: Int) -> QX:
    if k < len(p):
        return p[k].copy()
    return QX()


def tp_add(a: TPoly, b: TPoly) -> TPoly:
    var width = len(a) if len(a) > len(b) else len(b)
    var out = TPoly()
    for k in range(width):
        out.append(p2_add(tp_coeff(a, k), tp_coeff(b, k)))
    return tp_norm(out)


def tp_scale(p: TPoly, c: QX) -> TPoly:
    var out = TPoly()
    for k in range(len(p)):
        out.append(p2_mul(p[k], c))
    return tp_norm(out)


def tp_neg(p: TPoly) -> TPoly:
    return tp_scale(p, qx_const(-1))


def tp_sub(a: TPoly, b: TPoly) -> TPoly:
    return tp_add(a, tp_neg(b))


def tp_mul(a: TPoly, b: TPoly) -> TPoly:
    var x = tp_norm(a)
    var y = tp_norm(b)
    if len(x) == 0 or len(y) == 0:
        return TPoly()
    var out = TPoly()
    for _ in range(len(x) + len(y) - 1):
        out.append(QX())
    for i in range(len(x)):
        for j in range(len(y)):
            out[i + j] = p2_add(out[i + j], p2_mul(x[i], y[j]))
    return tp_norm(out)


def tp_shift(p: TPoly, k: Int) -> TPoly:
    """`t^k p`."""
    var out = TPoly()
    for _ in range(k):
        out.append(QX())
    for i in range(len(p)):
        out.append(p[i].copy())
    return tp_norm(out)


def tp_const(c: QX) -> TPoly:
    return tp_norm([c.copy()])


def tp_t() -> TPoly:
    return tp_norm([QX(), qx_const(1)])


def tp_key(p: TPoly) -> String:
    var out = String("")
    for k in range(len(p)):
        out += "[" + p2_key(p[k]) + "]"
    return out^


def tp_deriv(p: TPoly) -> TPoly:
    var out = TPoly()
    for k in range(1, len(p)):
        out.append(p2_scale(p[k], q_int(k)))
    return tp_norm(out)


def tp_at_t(p: TPoly, x: Q) -> QX:
    """Substitute a rational for `t`: a polynomial in the parameters."""
    var total = QX()
    for index in range(len(p)):
        total = p2_add(p2_scale(total, x), p[len(p) - 1 - index])
    return total^


def tp_at_q(p: TPoly, q: Int, d: Int = 0) -> TPoly:
    """Substitute integers for the parameters: a polynomial in `t` with constant coefficients."""
    var out = TPoly()
    for k in range(len(p)):
        out.append(p2_from_s([qx_at(p[k], q, d)]))
    return tp_norm(out)


def tp_prem(a: TPoly, b: TPoly) raises -> TPoly:
    """`lc(b)^e a mod b` with `e` even, so the result has the sign of `a` at
    every root of `b` where `lc(b) != 0`."""
    var bb = tp_norm(b)
    var db = len(bb) - 1
    if db < 0:
        raise Error("pseudo-division by the zero polynomial")
    var lead = bb[db].copy()
    var r = tp_norm(a)
    var steps = 0
    while len(r) - 1 >= db and len(r) > 0:
        var dr = len(r) - 1
        var top = r[dr].copy()
        r = tp_sub(tp_scale(r, lead), tp_scale(tp_shift(bb, dr - db), top))
        steps += 1
    if steps % 2 == 1:
        r = tp_scale(r, lead)
    return r^


# ---------------------------------------------------------------------------
# Signs at the Perron root, for all large q.
# ---------------------------------------------------------------------------


struct RatP2(Copyable, Movable):
    """`num / den`, a rational function of the parameters with `den > 0` certified on the region."""

    var num: QX
    var den: QX

    def __init__(out self, var num: QX, var den: QX):
        self.num = num^
        self.den = den^


def tp_at_rat(p: TPoly, x: RatP2) -> QX:
    """`p(x) den^deg p`: the sign of `p` at `x`, since `den > 0`."""
    var top = len(p) - 1
    var total = QX()
    for k in range(len(p)):
        var term = p[k].copy()
        for _ in range(k):
            term = p2_mul(term, x.num)
        for _ in range(top - k):
            term = p2_mul(term, x.den)
        total = p2_add(total, term)
    return total^


def _r_sub(a: RatP2, b: RatP2) -> RatP2:
    return RatP2(p2_sub(p2_mul(a.num, b.den), p2_mul(b.num, a.den)), p2_mul(a.den, b.den))


def _r_mul(a: RatP2, b: RatP2) -> RatP2:
    return RatP2(p2_mul(a.num, b.num), p2_mul(a.den, b.den))


def _r_div(a: RatP2, b: RatP2, mut ev: Eventual) raises -> RatP2:
    var sb = ev.sign(b.num)
    if sb == 0:
        raise Error("bracket refinement divides by zero")
    var num = p2_mul(a.num, b.den)
    var den = p2_mul(a.den, b.num)
    if sb < 0:
        return RatP2(p2_neg(num), p2_neg(den))
    return RatP2(num^, den^)


def _r_pow(x: QX, n: Int) -> QX:
    var out = qx_const(1)
    for _ in range(n):
        out = p2_mul(out, x)
    return out^


struct Bracket(Copyable, Movable):
    """`lo < beta < hi` on the region, each certified by the sign of `chi`."""

    var lo: RatP2
    var hi: RatP2

    def __init__(out self, var lo: RatP2, var hi: RatP2):
        self.lo = lo^
        self.hi = hi^


struct LineField(Copyable, Movable):
    """`chi(q, t)` with a certified single root in `(1, infinity)` for `q > threshold`.

    On a wedge, signs at `beta` are read from `brackets` instead of a
    Sturm--Tarski chain (whose intermediate signs change inside a wedge even
    when the answer does not): level `k + 1` refines level `k` by a Newton step
    from above and a chord step from below, each new end certified by the sign
    of `chi` there."""

    var chi: TPoly
    var dchi: TPoly
    var brackets: List[Bracket]

    def __init__(out self, chi: TPoly):
        self.chi = tp_norm(chi)
        self.dchi = tp_deriv(self.chi)
        self.brackets = List[Bracket]()

    def _chi_at(self, x: RatP2) -> RatP2:
        return RatP2(tp_at_rat(self.chi, x), _r_pow(x.den, tp_deg(self.chi)))

    def _refine(mut self, mut ev: Eventual) raises -> Bool:
        """Append the next bracket level; `False` if a new end is not certified."""
        ref b = self.brackets[len(self.brackets) - 1]
        var chi_hi = self._chi_at(b.hi)
        var chi_lo = self._chi_at(b.lo)
        var dchi_hi = RatP2(tp_at_rat(self.dchi, b.hi), _r_pow(b.hi.den, tp_deg(self.dchi)))
        if ev.try_sign(dchi_hi.num) != 1:
            return False
        var hi = _r_sub(b.hi, _r_div(chi_hi, dchi_hi, ev))
        var lo = _r_sub(b.lo, _r_div(_r_mul(chi_lo, _r_sub(b.hi, b.lo)), _r_sub(chi_hi, chi_lo), ev))
        # chi < 0 at a point puts it below beta; chi > 0 does so above beta only
        # past 1, since chi < 0 on (1, beta) and the other roots lie below 1
        if ev.try_sign(tp_at_rat(self.chi, lo)) != -1:
            return False
        if ev.try_sign(tp_at_rat(self.chi, hi)) != 1 or ev.try_sign(p2_sub(hi.num, hi.den)) != 1:
            return False
        self.brackets.append(Bracket(lo^, hi^))
        return True

    def _sign_bracketed(mut self, r: TPoly, mut ev: Eventual) raises -> Int:
        """The sign of `r(beta)`, `deg r <= 2`, from a bracket where `r` has one
        certified sign at both ends and none in between: `r` is monotone there
        (`r'` has one sign at both ends), or its vertex value has that sign, or
        it is convex against it (the extremum inside is the other kind)."""
        var dr = tp_deriv(r)
        var level = 0
        while True:
            var lo = self.brackets[level].lo.copy()
            var hi = self.brackets[level].hi.copy()
            var s = ev.try_sign(tp_at_rat(r, lo))
            if (s == 1 or s == -1) and ev.try_sign(tp_at_rat(r, hi)) == s:
                if tp_deg(r) <= 1:
                    return s
                var dl = ev.try_sign(tp_at_rat(dr, lo))
                if (dl == 1 or dl == -1) and ev.try_sign(tp_at_rat(dr, hi)) == dl:
                    return s
                var sa = ev.try_sign(tp_coeff(r, 2))  # OPEN_SIGN matches neither test below
                if sa == -s:
                    return s
                # vertex value (4 A C - B^2) / (4 A)
                var disc = p2_sub(p2_scale(p2_mul(tp_coeff(r, 2), tp_coeff(r, 0)), q_int(4)), p2_mul(tp_coeff(r, 1), tp_coeff(r, 1)))
                if ev.try_sign(disc) * sa == s:
                    return s
            level += 1
            if level == len(self.brackets):
                if level > MAX_BRACKET_LEVEL or not self._refine(ev):
                    raise Error("no bracket of beta decides a sign")

    def reduce(self, g: TPoly) raises -> TPoly:
        """`g` modulo `chi`, up to a positive factor (an even power of `lc(chi)`)."""
        return tp_prem(g, self.chi)

    def _variations(self, chain: List[TPoly], at_one: Bool, mut ev: Eventual) raises -> Int:
        var previous = 0
        var count = 0
        for i in range(len(chain)):
            var value = tp_at_t(chain[i], Q.one()) if at_one else tp_coeff(chain[i], len(chain[i]) - 1)
            var s = ev.sign(value)
            if s == 0:
                continue
            if previous != 0 and s != previous:
                count += 1
            previous = s
        return count

    def tarski_above_one(self, g: TPoly, mut ev: Eventual) raises -> Int:
        """`sum over roots x of chi in (1, infinity) of sign g(x)`, for every `q > ev.threshold`."""
        var chain = List[TPoly]()
        chain.append(self.chi.copy())
        var second = tp_prem(tp_mul(self.dchi, g), self.chi)
        if tp_deg(second) < 0:
            return 0
        chain.append(second^)
        while True:
            var nxt = tp_neg(tp_prem(chain[len(chain) - 2], chain[len(chain) - 1]))
            if tp_deg(nxt) < 0:
                break
            chain.append(nxt^)
        return self._variations(chain, True, ev) - self._variations(chain, False, ev)

    def sign_at_beta(mut self, g: TPoly, mut ev: Eventual) raises -> Int:
        var r = self.reduce(g)
        if tp_deg(r) < 0:
            return 0
        if len(self.brackets) > 0:
            return self._sign_bracketed(r, ev)
        return self.tarski_above_one(g, ev)


# ---------------------------------------------------------------------------
# The line.
# ---------------------------------------------------------------------------


struct SymVertex(Copyable, Movable):
    var top: Int
    var bottom: Int
    var w: List[QX]

    def __init__(out self, top: Int, bottom: Int, var w: List[QX]):
        self.top = top
        self.bottom = bottom
        self.w = w^

    def key(self) -> String:
        var out = String(self.top) + "|" + String(self.bottom)
        for i in range(3):
            out += "|" + p2_key(p2_norm(self.w[i]))
        return out^

    def is_zero_offset(self) -> Bool:
        for i in range(3):
            if not p2_is_zero(self.w[i]):
                return False
        return True


def w_add(a: List[QX], b: List[QX]) -> List[QX]:
    var out = List[QX]()
    for i in range(3):
        out.append(p2_add(a[i], b[i]))
    return out^


def w_sub(a: List[QX], b: List[QX]) -> List[QX]:
    var out = List[QX]()
    for i in range(3):
        out.append(p2_sub(a[i], b[i]))
    return out^


def w_unit(i: Int, c: QX) -> List[QX]:
    var out = List[QX]()
    for k in range(3):
        out.append(c.copy() if k == i else QX())
    return out^


def w_zero() -> List[QX]:
    return w_unit(0, QX())


struct Line(Copyable, Movable):
    """Images `first[a] y^(run[a]) last[a]`; `run[a]` an affine polynomial in `q`."""

    var first: List[Int]
    var last: List[Int]
    var run: List[QX]
    var y: Int
    var wedge: Bool  # some run involves the second parameter `d`
    var m: List[List[QX]]
    var field: LineField
    var ell: List[TPoly]

    def __init__(out self, first: List[Int], last: List[Int], run: List[QX], y: Int) raises:
        self.first = first.copy()
        self.last = last.copy()
        self.run = run.copy()
        self.y = y
        self.wedge = False
        for b in range(3):
            if p2_has_d(run[b]):
                self.wedge = True
        self.m = List[List[QX]]()
        for _ in range(3):
            var row = List[QX]()
            for _ in range(3):
                row.append(QX())
            self.m.append(row^)
        for b in range(3):
            self.m[first[b]][b] = p2_add(self.m[first[b]][b], qx_const(1))
            self.m[last[b]][b] = p2_add(self.m[last[b]][b], qx_const(1))
            self.m[y][b] = p2_add(self.m[y][b], run[b])
        # chi(t) = det(t I - M)
        var a = List[List[TPoly]]()
        for i in range(3):
            var row = List[TPoly]()
            for j in range(3):
                var e = tp_neg(tp_const(self.m[i][j]))
                if i == j:
                    e = tp_add(e, tp_t())
                row.append(e^)
            a.append(row^)
        var det = tp_sub(
            tp_add(
                tp_mul(a[0][0], tp_sub(tp_mul(a[1][1], a[2][2]), tp_mul(a[1][2], a[2][1]))),
                tp_mul(a[0][2], tp_sub(tp_mul(a[1][0], a[2][1]), tp_mul(a[1][1], a[2][0]))),
            ),
            tp_mul(a[0][1], tp_sub(tp_mul(a[1][0], a[2][2]), tp_mul(a[1][2], a[2][0]))),
        )
        self.field = LineField(det)
        # left null vector of (M - t I): orthogonal to its columns, a cross product of two of them
        var col = List[List[TPoly]]()
        for j in range(3):
            var c = List[TPoly]()
            for i in range(3):
                c.append(tp_neg(a[i][j]))
            col.append(c^)
        self.ell = List[TPoly]()
        self.ell.append(tp_sub(tp_mul(col[0][1], col[1][2]), tp_mul(col[0][2], col[1][1])))
        self.ell.append(tp_sub(tp_mul(col[0][2], col[1][0]), tp_mul(col[0][0], col[1][2])))
        self.ell.append(tp_sub(tp_mul(col[0][0], col[1][1]), tp_mul(col[0][1], col[1][0])))

    def mw(self, w: List[QX]) -> List[QX]:
        var out = List[QX]()
        for i in range(3):
            var s = QX()
            for j in range(3):
                s = p2_add(s, p2_mul(self.m[i][j], w[j]))
            out.append(s^)
        return out^

    def t_of(self, w: List[QX]) -> TPoly:
        var s = TPoly()
        for i in range(3):
            s = tp_add(s, tp_scale(self.ell[i], w[i]))
        return s^


struct LineCertificate(Copyable, Movable):
    """The PIP property of the line for every `q > threshold`, and the sign of the tile lengths."""

    var holds: Bool
    var ell_sign: Int

    def __init__(out self, holds: Bool, ell_sign: Int):
        self.holds = holds
        self.ell_sign = ell_sign


def _sturm_chain(field: LineField) raises -> List[TPoly]:
    var chain = List[TPoly]()
    chain.append(field.chi.copy())
    chain.append(field.dchi.copy())
    while True:
        var nxt = tp_neg(tp_prem(chain[len(chain) - 2], chain[len(chain) - 1]))
        if tp_deg(nxt) < 0:
            break
        chain.append(nxt^)
    return chain^


def _variations_at(chain: List[TPoly], x: Q, mut ev: Eventual) raises -> Int:
    var previous = 0
    var count = 0
    for i in range(len(chain)):
        var s = ev.sign(tp_at_t(chain[i], x))
        if s == 0:
            continue
        if previous != 0 and s != previous:
            count += 1
        previous = s
    return count


def _variations_at_infinity(chain: List[TPoly], positive: Bool, mut ev: Eventual) raises -> Int:
    """Sign changes at `t = +infinity` (leading coefficients) or `-infinity`."""
    var previous = 0
    var count = 0
    for i in range(len(chain)):
        var d = tp_deg(chain[i])
        var s = ev.sign(tp_coeff(chain[i], d))
        if not positive and d % 2 == 1:
            s = -s
        if s == 0:
            continue
        if previous != 0 and s != previous:
            count += 1
        previous = s
    return count


def roots_above(field: LineField, a: Q, mut ev: Eventual) raises -> Int:
    """Sturm count of the real roots of `chi` in `(a, infinity)`, for `q > threshold`."""
    var chain = _sturm_chain(field)
    return _variations_at(chain, a, ev) - _variations_at_infinity(chain, True, ev)


def roots_below(field: LineField, a: Q, mut ev: Eventual) raises -> Int:
    """Sturm count of the real roots of `chi` in `(-infinity, a)`, for `q > threshold`."""
    var chain = _sturm_chain(field)
    return _variations_at_infinity(chain, False, ev) - _variations_at(chain, a, ev)


def certify_line(mut line: Line, mut ev: Eventual) raises -> LineCertificate:
    """PIP for every `q > threshold`: the support of `M` is eventually fixed and
    primitive; `chi` has no rational root (the determinant must be a constant,
    whose divisors are the only candidates); exactly one root lies in
    `(1, infinity)`, `chi(1) != 0`; and the other two lie in the open unit disc
    (two real roots in `(-1, 1)`, or a complex pair with `beta > |det M|`, since
    `|beta_2|^2 = |det M| / beta`). Also fixes the sign that makes the tile
    lengths positive at `beta`."""
    var chi = line.field.chi.copy()
    var det = p2_neg(tp_coeff(chi, 0))  # chi(0) = -det M
    if not p2_is_const(det):
        raise Error("the line's determinant is not constant")
    if p2_is_zero(det):
        return LineCertificate(False, 0)
    # support of M: every entry eventually positive or identically zero
    var support = List[Int]()
    for i in range(3):
        for j in range(3):
            var s = ev.sign(line.m[i][j])
            if s < 0:
                return LineCertificate(False, 0)
            support.append(1 if s > 0 else 0)
    if not _primitive_support(support):
        return LineCertificate(False, 0)
    # rational roots divide the (constant) determinant
    var d = p2_const_value(det)
    var dn = 1
    while q_int(dn).le(d) or q_int(dn).le(d.neg()):
        if d.div(q_int(dn)).mul(q_int(dn)).eq(d):
            for sgn in range(2):
                var r = q_int(dn) if sgn == 0 else q_int(-dn)
                if ev.sign(tp_at_t(chi, r)) == 0:
                    return LineCertificate(False, 0)
        dn += 1
        if dn > 1000:
            raise Error("determinant too large for the rational-root screen")
    if ev.sign(tp_at_t(chi, Q.one())) == 0:
        return LineCertificate(False, 0)
    if line.wedge:
        if not _rouche_pisot(chi, ev) or not _seed_bracket(line.field, ev):
            return LineCertificate(False, 0)
    elif not _sturm_pisot(line, d, ev):
        return LineCertificate(False, 0)
    var s = line.field.sign_at_beta(line.ell[line.y], ev)
    if s == 0:
        return LineCertificate(False, 0)
    for i in range(3):
        if line.field.sign_at_beta(line.ell[i], ev) != s:
            return LineCertificate(False, 0)
    return LineCertificate(True, s)


def _rouche_pisot(chi: TPoly, mut ev: Eventual) raises -> Bool:
    """`chi = t^3 + c2 t^2 + c1 t + c0` with `|c2| > 1 + |c1| + |c0|`: on `|t| = 1`
    the term `c2 t^2` dominates the rest strictly, so (Rouche) `chi` has two
    roots in the open unit disc and none on the circle, like `c2 t^2`. The third
    root is then real, and it is the Perron root, which is `> 1`. Unlike the
    Sturm count, this reads no sign that tells a real pair from a complex one,
    which changes inside a wedge."""
    if tp_deg(chi) != 3 or not p2_is_const(p2_sub(tp_coeff(chi, 3), qx_const(1))):
        return False
    var margin = qx_const(-1)
    for k in range(3):
        var c = tp_coeff(chi, k)
        var sk = ev.sign(c)
        if k == 2 and sk == 0:
            return False
        margin = p2_add(margin, c) if (k == 2) == (sk > 0) else p2_sub(margin, c)
    return ev.sign(margin) > 0


def _seed_bracket(mut field: LineField, mut ev: Eventual) raises -> Bool:
    """`trace - k < beta < trace + j` for the least `k >= 1`, `j >= 0` (at most
    `BRACKET_SEED_RANGE`) certified by the sign of `chi`, with the lower end `> 1`."""
    var trace = p2_neg(tp_coeff(field.chi, 2))
    var one = qx_const(1)
    for j in range(BRACKET_SEED_RANGE):
        var hi = p2_add(trace, qx_const(j))
        if ev.try_sign(tp_at_rat(field.chi, RatP2(hi.copy(), one.copy()))) != 1:
            continue
        for k in range(1, BRACKET_SEED_RANGE):
            var lo = p2_sub(trace, qx_const(k))
            if ev.try_sign(p2_sub(lo, one)) != 1:
                break
            if ev.try_sign(tp_at_rat(field.chi, RatP2(lo.copy(), one.copy()))) == -1:
                field.brackets.append(Bracket(RatP2(lo^, one.copy()), RatP2(hi^, one.copy())))
                return True
        return False
    return False


def _sturm_pisot(mut line: Line, d: Q, mut ev: Eventual) raises -> Bool:
    """One root of `chi` in `(1, infinity)` and two in the open unit disc, by Sturm counts."""
    if roots_above(line.field, Q.one(), ev) != 1:
        return False
    var inside = roots_above(line.field, Q(-1, 1), ev) - roots_above(line.field, Q.one(), ev)
    if inside != 2:
        if inside != 0:
            return False
        var dd = d.copy() if Q.zero().lt(d) else d.neg()
        var over = tp_sub(tp_t(), tp_const(p2_from_s([dd.copy()])))
        if line.field.sign_at_beta(over, ev) <= 0:
            return False
        # and the two non-Perron roots are not real outside the disc: no root below -1
        if roots_below(line.field, Q(-1, 1), ev) != 0:
            return False
    return True


def _primitive_support(s: List[Int]) -> Bool:
    """Some power of the 0/1 support matrix is positive (Wielandt: power 5 suffices)."""
    var p = s.copy()
    for _ in range(5):
        var all_pos = True
        for k in range(9):
            if p[k] == 0:
                all_pos = False
        if all_pos:
            return True
        var nxt = List[Int](length=9, fill=0)
        for i in range(3):
            for j in range(3):
                var v = 0
                for k in range(3):
                    if p[i * 3 + k] != 0 and s[k * 3 + j] != 0:
                        v = 1
                nxt[i * 3 + j] = v
        p = nxt^
    for k in range(9):
        if p[k] == 0:
            return False
    return True


struct SymbolicLineGraph(Copyable, Movable):
    var vertices: List[SymVertex]
    var adj: List[List[Int]]
    var threshold: Q
    var d_threshold: Q
    var queries: Int
    var pip: Bool

    def __init__(out self):
        self.vertices = List[SymVertex]()
        self.adj = List[List[Int]]()
        self.threshold = Q.zero()
        self.d_threshold = Q.zero()
        self.queries = 0
        self.pip = False

    def size(self) -> Int:
        return len(self.vertices)


struct _Closure:
    var line: Line
    var sign: Int  # +1 or -1: the orientation that makes ell positive at beta
    var ev: Eventual
    var index: Dict[String, Int]
    var vertices: List[SymVertex]
    var adj: List[List[Int]]
    var queue: List[Int]
    var memo: Dict[String, Int]

    def __init__(out self, var line: Line, sign: Int, var ev: Eventual):
        self.line = line^
        self.sign = sign
        self.ev = ev^
        self.index = Dict[String, Int]()
        self.vertices = List[SymVertex]()
        self.adj = List[List[Int]]()
        self.queue = List[Int]()
        self.memo = Dict[String, Int]()

    def positive(mut self, g: TPoly) raises -> Int:
        """Sign of `g(beta)` with the tile lengths oriented positive. A repeated
        query returns its first answer, whose threshold is already recorded."""
        var h = tp_scale(g, qx_const(self.sign))
        var k = tp_key(h)
        if k in self.memo:
            return self.memo[k]
        var s = self.line.field.sign_at_beta(h, self.ev)
        self.memo[k] = s
        return s

    def real(mut self, a: Int, b: Int, w: List[QX]) raises -> Bool:
        """`-ell_b < <ell, w> < ell_a`."""
        var t = self.line.t_of(w)
        if self.positive(tp_add(self.line.ell[b], t)) <= 0:
            return False
        return self.positive(tp_sub(self.line.ell[a], t)) > 0

    def intern(mut self, var v: SymVertex) raises -> Int:
        var k = v.key()
        if k in self.index:
            return self.index[k]
        if len(self.vertices) >= SYMBOLIC_VERTEX_CAP:
            raise Error("symbolic line closure exceeded its vertex cap")
        var i = len(self.vertices)
        self.index[k] = i
        self.vertices.append(v^)
        self.adj.append(List[Int]())
        self.queue.append(i)
        return i

    def prefix(self, a: Int, seg: Int) -> List[QX]:
        """Parikh vector of `sigma(a)` before segment `seg` (0 first letter, 1 run, 2 last letter)."""
        var v = w_zero()
        if seg >= 1:
            v = w_add(v, w_unit(self.line.first[a], qx_const(1)))
        if seg >= 2:
            v = w_add(v, w_unit(self.line.y, self.line.run[a]))
        return v^

    def has_run(mut self, a: Int) raises -> Bool:
        var s = self.ev.sign(self.line.run[a])
        if s < 0:
            raise Error("a run length is eventually negative")
        return s > 0

    def letter(self, a: Int, seg: Int) -> Int:
        if seg == 0:
            return self.line.first[a]
        if seg == 1:
            return self.line.y
        return self.line.last[a]

    def least_m(mut self, h0: TPoly, h1: TPoly, strict: Bool) raises -> QX:
        """The least integer `m(q)` with `h0 + m h1 > 0` (`>= 0` if not `strict`) at
        beta (`h1 > 0`), as an affine polynomial in `q`, fitted at sample points and
        certified."""
        var b = SAMPLE_BASE
        var v1 = _least_at(self.line, self.sign, h0, h1, b, b, strict)
        var v2 = _least_at(self.line, self.sign, h0, h1, 2 * b, b, strict)
        var slope = (v2 - v1) // b
        if v2 - v1 != slope * b:
            raise Error("a run-position bound is not affine in q at the samples")
        var d_slope = 0
        if self.line.wedge:
            var v3 = _least_at(self.line, self.sign, h0, h1, b, 2 * b, strict)
            d_slope = (v3 - v1) // b
            if v3 - v1 != d_slope * b:
                raise Error("a run-position bound is not affine in d at the samples")
        var c0 = v1 - slope * b - d_slope * b
        var mu = qx_affine(c0, slope, d_slope)
        var floor_sign = 1 if strict else 0
        if self.positive(tp_add(h0, tp_scale(h1, mu))) < floor_sign:
            raise Error("a fitted run-position bound fails certification (low side)")
        if self.positive(tp_add(h0, tp_scale(h1, p2_sub(mu, qx_const(1))))) >= floor_sign:
            raise Error("a fitted run-position bound fails certification (high side)")
        return mu^

    def expand(mut self, i: Int) raises:
        var v = self.vertices[i].copy()
        if v.top == v.bottom and v.is_zero_offset():
            return
        var mw = self.line.mw(v.w)
        var ell = self.line.ell.copy()
        var y = self.line.y
        for sa in range(3):
            if sa == 1 and not self.has_run(v.top):
                continue
            for sb in range(3):
                if sb == 1 and not self.has_run(v.bottom):
                    continue
                var base = w_sub(w_add(mw, self.prefix(v.bottom, sb)), self.prefix(v.top, sa))
                var a2 = self.letter(v.top, sa)
                var b2 = self.letter(v.bottom, sb)
                if sa != 1 and sb != 1:
                    if self.real(a2, b2, base):
                        var c = self.intern(SymVertex(a2, b2, base^))
                        self.adj[i].append(c)
                    continue
                # offset base + m e_y; real iff ell_b2 + t + m ell_y > 0 and ell_a2 - t - m ell_y > 0
                var t = self.line.t_of(base)
                var low_h = tp_add(ell[b2], t)  # real below: low_h + m ell_y > 0
                var high_h = tp_sub(t, ell[a2])  # real above: high_h + m ell_y < 0
                # run positions: m = k_b - k_a with k in [0, run - 1]
                var rlo = p2_neg(p2_sub(self.line.run[v.top], qx_const(1))) if sa == 1 else QX()
                var rhi = p2_sub(self.line.run[v.bottom], qx_const(1)) if sb == 1 else QX()
                var low: QX
                var high: QX
                if self.line.wedge:
                    # a run end that is itself real binds, and needs no fitted bound
                    if self.positive(tp_add(low_h, tp_scale(ell[y], rlo))) > 0:
                        low = rlo.copy()
                    else:
                        low = self.least_m(low_h, ell[y], True)
                    if self.positive(tp_add(high_h, tp_scale(ell[y], rhi))) < 0:
                        high = rhi.copy()
                    else:
                        high = p2_sub(self.least_m(high_h, ell[y], False), qx_const(1))
                else:
                    var lo = self.least_m(low_h, ell[y], True)
                    var hi = p2_sub(self.least_m(high_h, ell[y], False), qx_const(1))  # least m with t + m ell_y >= ell_a2, less one
                    low = lo.copy() if self.ev.sign(p2_sub(lo, rlo)) >= 0 else rlo.copy()
                    high = hi.copy() if self.ev.sign(p2_sub(rhi, hi)) >= 0 else rhi.copy()
                var gap = p2_sub(high, low)
                if not p2_is_const(gap):
                    if self.ev.sign(gap) < 0:
                        continue
                    raise Error("a run-position range grows with the parameters")
                var g0 = p2_const_value(gap)
                if g0.lt(Q.zero()):
                    continue
                var width = 0
                while q_int(width + 1).le(g0):
                    width += 1
                for d in range(width + 1):
                    var mval = p2_add(low, qx_const(d))
                    var child = w_add(base, w_unit(y, mval))
                    var c = self.intern(SymVertex(a2, b2, child^))
                    self.adj[i].append(c)

    def seeds(mut self) raises:
        for a in range(3):
            for b in range(a + 1, 3):
                var tops = List[Int]([a, b])
                var bots = List[Int]([b, a])
                var top_pos = List[List[QX]]()
                top_pos.append(w_zero())
                top_pos.append(w_unit(a, qx_const(1)))
                var bot_pos = List[List[QX]]()
                bot_pos.append(w_zero())
                bot_pos.append(w_unit(b, qx_const(1)))
                for i in range(2):
                    for j in range(2):
                        var w = w_sub(bot_pos[j], top_pos[i])
                        if self.real(tops[i], bots[j], w):
                            _ = self.intern(SymVertex(tops[i], bots[j], w^))


def _h_pos(m: Int, mut field: LineField, g0: TPoly, g1: TPoly, floor_sign: Int, mut ev: Eventual) raises -> Bool:
    return field.sign_at_beta(tp_add(g0, tp_scale(g1, qx_const(m))), ev) >= floor_sign


def _least_at(line: Line, sign: Int, h0: TPoly, h1: TPoly, q: Int, d: Int, strict: Bool) raises -> Int:
    """Exact least integer `m` with `h0 + m h1 > 0` (`>= 0` if not `strict`) at
    `beta(q, d)`, for one concrete parameter point."""
    var field = LineField(tp_at_q(line.field.chi, q, d))
    var g0 = tp_scale(tp_at_q(h0, q, d), qx_const(sign))
    var g1 = tp_scale(tp_at_q(h1, q, d), qx_const(sign))
    var ev = Eventual()
    if field.sign_at_beta(g1, ev) <= 0:
        raise Error("the run-position step is not positive")
    var m = 0
    var step = 1

    # find an interval [lo, hi] with h(lo) <= 0 < h(hi)
    var fs = 1 if strict else 0

    if _h_pos(m, field, g0, g1, fs, ev):
        var hi = m
        var lo = m - step
        while _h_pos(lo, field, g0, g1, fs, ev):
            hi = lo
            step *= 2
            lo = hi - step
        while hi - lo > 1:
            var mid = (lo + hi) // 2
            if _h_pos(mid, field, g0, g1, fs, ev):
                hi = mid
            else:
                lo = mid
        return hi
    var lo = m
    var hi = m + step
    while not _h_pos(hi, field, g0, g1, fs, ev):
        lo = hi
        step *= 2
        hi = lo + step
    while hi - lo > 1:
        var mid = (lo + hi) // 2
        if _h_pos(mid, field, g0, g1, fs, ev):
            hi = mid
        else:
            lo = mid
    return hi


def symbolic_line_graph(var line: Line) raises -> SymbolicLineGraph:
    """The swap-seed overlap graph of the line for all `q > threshold`; see the module docstring."""
    var ev = Eventual()
    var cert = certify_line(line, ev)
    var out = SymbolicLineGraph()
    if not cert.holds:
        out.pip = False
        out.threshold = ev.threshold.copy()
        out.d_threshold = ev.d_threshold.copy()
        return out^
    var cl = _Closure(line^, cert.ell_sign, ev^)
    cl.seeds()
    var done = 0
    while done < len(cl.queue):
        var i = cl.queue[done]
        done += 1
        cl.expand(i)
    out.pip = True
    out.threshold = cl.ev.threshold.copy()
    out.d_threshold = cl.ev.d_threshold.copy()
    out.queries = cl.ev.queries
    out.vertices = cl.vertices.copy()
    out.adj = cl.adj.copy()
    return out^


def offset_zero_reachable(g: SymbolicLineGraph) -> List[Bool]:
    """Whether each vertex has an offset-zero descendant (itself included)."""
    var n = g.size()
    var good = List[Bool](length=n, fill=False)
    var rev = List[List[Int]]()
    for _ in range(n):
        rev.append(List[Int]())
    for i in range(n):
        for j in range(len(g.adj[i])):
            rev[g.adj[i][j]].append(i)
    var stack = List[Int]()
    for i in range(n):
        if g.vertices[i].is_zero_offset():
            good[i] = True
            stack.append(i)
    while len(stack) > 0:
        var v = stack.pop()
        for k in range(len(rev[v])):
            var u = rev[v][k]
            if not good[u]:
                good[u] = True
                stack.append(u)
    return good^
