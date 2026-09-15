"""Contracting lower bound on the first boundary-coincidence depth (canonical).

Manuscript Proposition 5.42.  An overlap `(i, j, t)` with a level-`m`
descendant of offset zero has `t = -sum_{s<m} beta^{-(s+1)} c_s` with each
increment `c_s` in the finite digit set `F` of one inflation, so for every
contracting embedding `sigma_k` of Q(beta):
    |sigma_k(t)| <= C_k * sum_{s=1}^{m} |sigma_k(beta)|^{-s},  C_k = max_{F \\ {0}} |sigma_k(c)|.
`least_level(t)` is `0` for `t = 0` and otherwise the least `m >= 1` allowed
by every contracting embedding.

Complex contracting pair (`D > 0`): `|sigma(t)|^2 = N(t)/t`,
`|sigma(beta)|^{-2} = rho := beta/D`, `K := max_{F \\ {0}} N(c)/c = C^2`
(attained at `c*`), and with `r = rho^{1/2}`:
`(sum_{s=1}^m r^s)^2 = A_m + r B_m`, `A_m = sum_j n_{2j} rho^j`,
`B_m = sum_j n_{2j+1} rho^j`, `n_k = min(k-1, 2m+1-k)`.  The defining
inequality squared is `N(t)/t <= K (A_m + r B_m)`, which holds iff
`N(t)/t <= K A_m` or `(N(t)/t - K A_m)^2 <= K^2 rho B_m^2`: two exact sign
tests at the Perron root, no relaxation.  Two real contracting conjugates:
the defining comparison at each isolated conjugate root.

All field arithmetic is in `Q[x]/(chi)` over unbounded rationals and every
sign is a Sturm--Tarski query (`real_root_sign`) at an isolated real root of
`chi`, the Perron root included: the fixed-width oracle of `perron_field3`
fails closed on the coefficient growth of the level tests, this one does
not.  A capped automaton is never accepted."""

from finite_exact.rat_q import Q, q_abs
from psc.exact import q_int, q_poly, q_sign, require_q
from psc.overlap_seed_patch import SeedOverlapAutomaton, SeedOverlapTables
from psc.perron_field3 import CubicElt, PerronField3, _checked_add, _checked_mul, _checked_sub, cubic_sub_checked
from psc.real_root_sign import isolate_real_roots, sign_at_isolated_root


# ---- Q[x]/(chi): elements are `List[Q]`, low degree first, trimmed ----------


def lift(x: CubicElt) -> List[Q]:
    var v: List[Int] = [x.a0, x.a1, x.a2]
    return q_poly(v)


def _coef(x: List[Q], i: Int) -> Q:
    if i < len(x):
        return x[i].copy()
    return Q.zero()


def _fadd(x: List[Q], y: List[Q]) raises -> List[Q]:
    var n = len(x) if len(x) > len(y) else len(y)
    var out = List[Q]()
    for i in range(n):
        out.append(require_q(_coef(x, i).add(_coef(y, i)), "field add"))
    return out^


def _fneg(x: List[Q]) -> List[Q]:
    var out = List[Q]()
    for i in range(len(x)):
        out.append(x[i].neg())
    return out^


def _fsub(x: List[Q], y: List[Q]) raises -> List[Q]:
    return _fadd(x, _fneg(y))


def _fscale(x: List[Q], k: Q) raises -> List[Q]:
    var out = List[Q]()
    for i in range(len(x)):
        out.append(require_q(x[i].mul(k), "field scale"))
    return out^


def _fmul(chi: List[Q], x: List[Q], y: List[Q]) raises -> List[Q]:
    var prod = List[Q]()
    if len(x) == 0 or len(y) == 0:
        return prod^
    for _ in range(len(x) + len(y) - 1):
        prod.append(Q.zero())
    for i in range(len(x)):
        for j in range(len(y)):
            prod[i + j] = require_q(prod[i + j].add(x[i].mul(y[j])), "field mul")
    # reduce modulo the monic cubic chi
    var r = prod.copy()
    for d in range(len(r) - 1, 2, -1):
        var k = r[d].copy()
        if q_sign(k) == 0:
            continue
        for i in range(4):
            r[d - 3 + i] = require_q(r[d - 3 + i].sub(k.mul(chi[i])), "field reduce")
    var out = List[Q]()
    for i in range(3):
        out.append(_coef(r, i))
    return out^


def _fnorm(chi: List[Q], x: List[Q]) raises -> Q:
    """N(x) = det of multiplication by x on the basis 1, beta, beta^2."""
    var beta = q_poly([0, 1])
    var c0 = x.copy()
    var c1 = _fmul(chi, c0, beta)
    var c2 = _fmul(chi, c1, beta)
    var m00 = _coef(c0, 0)
    var m01 = _coef(c1, 0)
    var m02 = _coef(c2, 0)
    var m10 = _coef(c0, 1)
    var m11 = _coef(c1, 1)
    var m12 = _coef(c2, 1)
    var m20 = _coef(c0, 2)
    var m21 = _coef(c1, 2)
    var m22 = _coef(c2, 2)
    var t0 = m00.mul(m11.mul(m22).sub(m12.mul(m21)))
    var t1 = m01.mul(m10.mul(m22).sub(m12.mul(m20)))
    var t2 = m02.mul(m10.mul(m21).sub(m11.mul(m20)))
    return require_q(t0.sub(t1).add(t2), "field norm")


def field_norm(field: PerronField3, x: CubicElt) raises -> Q:
    return _fnorm(q_poly(field.charpoly()), lift(x))


def discriminant(field: PerronField3) raises -> Int:
    """Discriminant of x^3 + chi2 x^2 + chi1 x + chi0; negative iff a complex pair."""
    var a = field.chi2
    var b = field.chi1
    var c = field.chi0
    var t1 = _checked_mul(18, _checked_mul(a, _checked_mul(b, c)))
    var t2 = _checked_mul(4, _checked_mul(a, _checked_mul(a, _checked_mul(a, c))))
    var t3 = _checked_mul(_checked_mul(a, a), _checked_mul(b, b))
    var t4 = _checked_mul(4, _checked_mul(b, _checked_mul(b, b)))
    var t5 = _checked_mul(27, _checked_mul(c, c))
    return _checked_sub(_checked_sub(_checked_add(_checked_sub(t1, t2), t3), t4), t5)


def digit_set(tables: SeedOverlapTables) raises -> List[CubicElt]:
    """Nonzero single-inflation offset increments q - p over all letter pairs."""
    var out = List[CubicElt]()
    var seen = Dict[CubicElt, Bool]()
    for a in range(3):
        for b in range(3):
            for k in range(len(tables.sigma[a])):
                for m in range(len(tables.sigma[b])):
                    var c = cubic_sub_checked(tables.prefix(b, m), tables.prefix(a, k))
                    if c.is_zero() or c in seen:
                        continue
                    seen[c] = True
                    out.append(c)
    return out^


def _cauchy_bound(field: PerronField3) raises -> Int:
    var m = 0
    for v in [field.chi0, field.chi1, field.chi2]:
        var a = _checked_sub(0, v) if v < 0 else v
        if a > m:
            m = a
    return _checked_add(m, 1)


struct ContractingBound(Copyable, Movable):
    var chi: List[Q]
    var is_complex: Bool
    var max_level: Int
    # isolating brackets: index 0 is the Perron root; 1, 2 the real conjugates (real case)
    var root_lo: List[Q]
    var root_hi: List[Q]
    # complex pair: rho = beta/D, the level tables A_m, B_m (index m, entry 0 unused),
    # c* maximising |N(c)|/|c| on F \ {0}, and |N(c*)|
    var rho: List[Q]
    var A: List[List[Q]]
    var B: List[List[Q]]
    var cstar: List[Q]
    var cstar_norm: Q
    # two real conjugates (index r = 0, 1): C_r and the level table G_r[m] = sum_{s<m} |beta_r|^s
    var cmax: List[List[Q]]
    var G: List[List[List[Q]]]
    # beta^m (index m), used by the real branch
    var beta_pow: List[List[Q]]

    def __init__(out self, tables: SeedOverlapTables, max_level: Int = 64) raises:
        var field = tables.field
        self.chi = q_poly(field.charpoly())
        self.max_level = max_level
        self.is_complex = discriminant(field) < 0
        self.root_lo = List[Q]()
        self.root_hi = List[Q]()
        self.rho = List[Q]()
        self.A = List[List[Q]]()
        self.B = List[List[Q]]()
        self.cstar = List[Q]()
        self.cstar_norm = Q.zero()
        self.cmax = List[List[Q]]()
        self.G = List[List[List[Q]]]()
        self.beta_pow = List[List[Q]]()
        var digits = digit_set(tables)
        if len(digits) == 0:
            raise Error("empty increment set")
        var perron = isolate_real_roots(self.chi, q_int(1), q_int(_cauchy_bound(field)), 1)
        self.root_lo.append(perron[0][0].copy())
        self.root_hi.append(perron[0][1].copy())
        var beta = q_poly([0, 1])
        if self.is_complex:
            var D = q_int(-field.chi0)
            if q_sign(D) <= 0:
                raise Error("complex contracting pair requires D > 0")
            self.rho = _fscale(beta, require_q(Q.one().div(D), "1/D"))
            var rho_pow = List[List[Q]]()
            rho_pow.append(q_poly([1]))
            for _ in range(max_level):
                rho_pow.append(_fmul(self.chi, rho_pow[len(rho_pow) - 1], self.rho))
            # (sum_{s=1}^m r^s)^2 = A_m + r B_m with r^2 = rho, n_k = min(k-1, 2m+1-k)
            self.A.append(List[Q]())
            self.B.append(List[Q]())
            for m in range(1, max_level + 1):
                var Am = List[Q]()
                var Bm = List[Q]()
                for k in range(2, 2 * m + 1):
                    var n = k - 1 if k - 1 < 2 * m + 1 - k else 2 * m + 1 - k
                    var term = _fscale(rho_pow[k // 2], q_int(n))
                    if k % 2 == 0:
                        Am = _fadd(Am, term)
                    else:
                        Bm = _fadd(Bm, term)
                self.A.append(Am^)
                self.B.append(Bm^)
            var best = self._abs_at(0, lift(digits[0]))
            var best_norm = q_abs(self._norm(lift(digits[0])))
            for i in range(1, len(digits)):
                var ac = self._abs_at(0, lift(digits[i]))
                var nc = q_abs(self._norm(lift(digits[i])))
                # nc/|c| > best_norm/|best|  <=>  nc*|best| - best_norm*|c| > 0
                if self._sign_at(0, _fsub(_fscale(best, nc), _fscale(ac, best_norm))) > 0:
                    best = ac^
                    best_norm = nc^
            self.cstar = best^
            self.cstar_norm = best_norm^
        else:
            self.beta_pow.append(q_poly([1]))
            for _ in range(max_level):
                self.beta_pow.append(_fmul(self.chi, self.beta_pow[len(self.beta_pow) - 1], beta))
            var boxes = isolate_real_roots(self.chi, q_int(-1), q_int(1), 2)
            for r in range(2):
                self.root_lo.append(boxes[r][0].copy())
                self.root_hi.append(boxes[r][1].copy())
                var eb = self._abs_at(r + 1, beta)
                var cm = self._abs_at(r + 1, lift(digits[0]))
                for i in range(1, len(digits)):
                    var c = self._abs_at(r + 1, lift(digits[i]))
                    if self._sign_at(r + 1, _fsub(c, cm)) > 0:
                        cm = c^
                self.cmax.append(cm^)
                # G_r[m] = sum_{s<m} |beta_r|^s
                var Gr = List[List[Q]]()
                Gr.append(List[Q]())
                var pw = q_poly([1])
                for _ in range(max_level):
                    Gr.append(_fadd(Gr[len(Gr) - 1], pw))
                    pw = _fmul(self.chi, pw, eb)
                self.G.append(Gr^)

    def _sign_at(self, r: Int, x: List[Q]) raises -> Int:
        return sign_at_isolated_root(self.chi, x, self.root_lo[r], self.root_hi[r])

    def _abs_at(self, r: Int, x: List[Q]) raises -> List[Q]:
        if self._sign_at(r, x) < 0:
            return _fneg(x)
        return x.copy()

    def _norm(self, x: List[Q]) raises -> Q:
        return _fnorm(self.chi, x)

    def least_level(self, a: SeedOverlapAutomaton, t: CubicElt) raises -> Int:
        if a.capped:
            raise Error("contracting bound is undefined for a capped partial graph")
        if t.is_zero():
            return 0
        var x = lift(t)
        if self.is_complex:
            var at = self._abs_at(0, x)
            var lhs = _fscale(self.cstar, q_abs(self._norm(x)))          # |N(t)| |c*|
            var at2 = _fscale(_fmul(self.chi, at, at), require_q(self.cstar_norm.square(), "K^2"))  # |N(c*)|^2 |t|^2
            for m in range(1, self.max_level + 1):
                # X <= K (A_m + r B_m), X = |N(t)|/|t|, K = |N(c*)|/|c*|; times |t| |c*|:
                var E = _fsub(lhs, _fscale(_fmul(self.chi, self.A[m], at), self.cstar_norm))
                if self._sign_at(0, E) <= 0:
                    return m
                # E > 0: E <= |N(c*)| r B_m |t|  <=>  E^2 <= |N(c*)|^2 rho B_m^2 |t|^2
                var rhs = _fmul(self.chi, _fmul(self.chi, at2, self.rho), _fmul(self.chi, self.B[m], self.B[m]))
                if self._sign_at(0, _fsub(rhs, _fmul(self.chi, E, E))) >= 0:
                    return m
            raise Error("contracting bound exceeded the level cap")
        var worst = 0
        for r in range(1, 3):
            var found = False
            for m in range(1, self.max_level + 1):
                var tb = self._abs_at(r, _fmul(self.chi, x, self.beta_pow[m]))
                if self._sign_at(r, _fsub(_fmul(self.chi, self.cmax[r - 1], self.G[r - 1][m]), tb)) >= 0:
                    if m > worst:
                        worst = m
                    found = True
                    break
            if not found:
                raise Error("contracting bound exceeded the level cap")
        return worst
