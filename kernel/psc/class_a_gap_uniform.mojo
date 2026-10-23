"""Closure and descent of a class-A regime table for every gap d >= d0 (#139, gaps d >= 5).

The ray certificate (`psc.class_a_carrier_closure`, `psc.class_a_carrier_descent`)
proves one line `(n+d, n, n+eps)` with `d` fixed. This module proves a *regime*
(`psc.gap_form.Regime`): all `n = d l + r` with `l >= l0`, `d >= d0` and `r`
pinned by the regime (`r = j`, `r = d - j`, or `j0 <= r <= d - j1`), with one
`l`-affine table of rows, pieces and descent occurrences shared by every gap.
Design, lemmas and the module contract: docs/class-a-gap-uniform-certificate-design-2026-10-23.md.

The port is line for line the ray certificate with these substitutions:
  * run lengths, the child-index base and the prefix-count ranges are gap
    forms in Z[l, d, r]; their division by `d` is Lemma 2 (`Regime.div_*`),
    which refuses unless the rounding is one constant on the whole regime,
    and comparisons involving them are Lemma 1 after the regime's `r`
    substitution (`Regime.nonneg`);
  * every Perron sign is `sign_on_box` (Lemma 3) of the numerator of an
    `A + n B + (r h) C` form with `u = d h`, at each `r h` endpoint of the
    regime, and must agree across endpoints;
  * every other quantity is `l`-affine and uses the ray helpers unchanged.
Receipts: CLASS_A_REGIME_CLOSURE, CLASS_A_REGIME_DESCENT and
CLASS_A_REGIME_BOUNDARY_HITTING. Nothing here is uniform in `eps`, and a
regime proves nothing about `(d, r)` outside it.
"""
from std.collections import Dict
from psc.gap_form import GapForm, Regime, gap_const, gap_lin, KIND_LOW, KIND_HIGH, KIND_MIDDLE
from psc.poly_hu import PolyHU, AffHU, sign_on_box
from psc.class_a_carrier_closure import (
    ClosureStats, aff, a_add, a_sub, a_le, a_max, a_min, slice_key, slices,
)
from psc.class_a_carrier_descent import is_target_piece


# ---------------------------------------------------------------------------
# Perron side: L and T as A + n B + (r h) C over Z[h, u], u = d h.
# ---------------------------------------------------------------------------

def _p(coeffs: List[List[Int]]) -> PolyHU:
    """`coeffs[i][j]` is the coefficient of `h^i u^j`."""
    var out = PolyHU.zero()
    for i in range(len(coeffs)):
        for j in range(len(coeffs[i])):
            if coeffs[i][j] != 0:
                out = out.add(PolyHU.monomial(i, j, coeffs[i][j]))
    return out^


def length_hu(eps: Int, letter: Int) raises -> AffHU:
    """`L = (1 + (1-eps) h + u + u h, 1 + (1-eps) h, 1 + h)`."""
    if letter == 0:
        return AffHU(_p([[1, 1], [1 - eps, 1]]), PolyHU.zero(), PolyHU.zero())
    if letter == 1:
        return AffHU(_p([[1], [1 - eps]]), PolyHU.zero(), PolyHU.zero())
    if letter == 2:
        return AffHU(_p([[1], [1]]), PolyHU.zero(), PolyHU.zero())
    raise Error("tile letter outside 0..2")


def displacement_hu(eps: Int, s: Int, k: List[Int], y: Int) raises -> AffHU:
    """`T = s L_c + k d h(1+h) + eps y h` for `k = a l + b`, with
    `k d h(1+h) = a n h(1+h) + b u (1+h) - a (r h)(1+h)`."""
    var a = k[0]
    var b = k[1]
    var lc = length_hu(eps, 1).a.copy()
    var A = lc.scale(s).add(_p([[0, b], [0, b]])).add(_p([[0], [eps * y]]))
    var B = _p([[0], [a], [a]])
    var C = _p([[-a], [-a]])
    return AffHU(A^, B^, C^)


def perron_hu(eps: Int) -> AffHU:
    """`P(n,h) = (1 - eps h - (1-eps) h^2 - u h - u h^2) + n (-h - h^2)`."""
    return AffHU(_p([[1], [-eps, -1], [eps - 1, -1]]), _p([[0], [-1], [-1]]), PolyHU.zero())


def check_regime_identity(eps: Int) raises:
    """Lemma 4: `h (M^T L)_j - (1+h) L_j + P = 0` coefficient-wise in `(h, u, n)`,
    with `M^T L = (2L_x + (n+d) L_y, L_x + L_c + n L_y, L_x + L_c + (n+eps) L_y)`
    and `d L_y h = u (1+h)`; and `E = n h(1+h)` is the `n`-free part of `P`."""
    if eps != 1 and eps != -1:
        raise Error("class-A line requires eps = +-1")
    var lx = length_hu(eps, 0).a.copy()
    var lc = length_hu(eps, 1).a.copy()
    var ly = length_hu(eps, 2).a.copy()
    var h = PolyHU.monomial(1, 0, 1)
    var one_h = _p([[1], [1]])
    var u_one_h = _p([[0, 1], [0, 1]])
    var p = perron_hu(eps)
    var hmt = List[AffHU]()
    hmt.append(AffHU(lx.scale(2).mul(h).add(u_one_h), ly.mul(h), PolyHU.zero()))
    hmt.append(AffHU(lx.add(lc).mul(h), ly.mul(h), PolyHU.zero()))
    hmt.append(AffHU(lx.add(lc).mul(h).add(ly.mul(h).scale(eps)), ly.mul(h), PolyHU.zero()))
    var ls = List[PolyHU]([lx.copy(), lc.copy(), ly.copy()])
    for j in range(3):
        var lhs = hmt[j].sub(AffHU(ls[j].mul(one_h), PolyHU.zero(), PolyHU.zero())).add(p)
        if not (lhs.a.is_zero() and lhs.b.is_zero() and lhs.c.is_zero()):
            raise Error("scaled lengths are not the left Perron eigenvector of the gap family")
    if not p.b.add(_p([[0], [1], [1]])).is_zero():
        raise Error("elimination identity disagrees with the Perron polynomial")


def check_perron_bound(eps: Int) raises:
    """`n^3 P(n, 1/n) = -(1+eps) n^2 - (d+1-eps) n - d`: every coefficient of this
    polynomial in `(n, d)` is `<= 0` and one is negative, so `h_n < 1/n` for
    all `n, d >= 1` (`P(n, 0) = 1` and `P(n, .)` decreases on `h > 0`)."""
    # Expand n^3 P(n, 1/n) term by term: P = sum_e (alpha_e + beta_e n + gamma_e d) h^e.
    # Coefficients of n^(3-e) * (alpha_e + beta_e n + gamma_e d): monomials n^(3-e), n^(4-e), n^(3-e) d.
    var mono = Dict[Int, Int]()   # key 10*i + j for n^i d^j
    var alpha = List[Int]([1, -eps, eps - 1, 0])
    var beta = List[Int]([0, -1, -1, 0])
    var gamma = List[Int]([0, 0, -1, -1])
    for e in range(4):
        var i = 3 - e
        for term in range(3):
            var coef = alpha[e] if term == 0 else (beta[e] if term == 1 else gamma[e])
            if coef == 0:
                continue
            var key = (10 * (i + 1)) if term == 1 else (10 * i + (1 if term == 2 else 0))
            mono[key] = (mono[key] if key in mono else 0) + coef
    var negative = False
    for key in mono.keys():
        if mono[key] > 0:
            raise Error("n^3 P(n,1/n) has a positive coefficient: the bound h < 1/n fails")
        if mono[key] < 0:
            negative = True
    if not negative:
        raise Error("n^3 P(n,1/n) vanished: no Perron bound")


def rh_endpoints(reg: Regime) -> List[PolyHU]:
    """The values of `r h` on the regime: `j h` (low), `u - j h` (high), both
    `j0 h` and `u - j1 h` (middle)."""
    var out = List[PolyHU]()
    if reg.kind == KIND_LOW:
        out.append(PolyHU.monomial(1, 0, reg.j))
    elif reg.kind == KIND_HIGH:
        out.append(PolyHU.monomial(0, 1, 1).sub(PolyHU.monomial(1, 0, reg.j)))
    else:
        out.append(PolyHU.monomial(1, 0, reg.j))
        out.append(PolyHU.monomial(0, 1, 1).sub(PolyHU.monomial(1, 0, reg.j1)))
    return out^


def regime_sign(reg: Regime, m: AffHU, max_depth: Int = 12) raises -> Int:
    """Sign of `m` at every member of the regime: Lemma 3 at each `r h`
    endpoint; the endpoint signs must agree (the margin is affine in `r h`)."""
    var sign = 2
    for rh in rh_endpoints(reg):
        var s = sign_on_box(m.numerator(rh, reg.eps), reg.l0, reg.d0, max_depth)
        if sign == 2:
            sign = s
        elif s != sign:
            raise Error("UNDECIDED sign: margin changes sign across the regime's residues")
    return sign


def strict_inside(reg: Regime, top: Int, bottom: Int, t: AffHU) raises -> Bool:
    return (regime_sign(reg, length_hu(reg.eps, top).sub(t)) > 0
            and regime_sign(reg, t.add(length_hu(reg.eps, bottom))) > 0)


def _unreal_on(reg: Regime, top: Int, bottom: Int, s2: Int, k0: List[Int], y2: Int,
               j_lo: List[Int], j_hi: List[Int]) raises -> Bool:
    """Not a strict overlap for any `j` in `[j_lo, j_hi]` and any member: the
    displacement increases in `j`, so one margin is `<= 0` at the relevant end,
    for every residue of the regime (affine in `r h`, both endpoints)."""
    var t_hi = displacement_hu(reg.eps, s2, a_add(k0, j_hi), y2)
    if regime_sign(reg, t_hi.add(length_hu(reg.eps, bottom))) <= 0:
        return True
    var t_lo = displacement_hu(reg.eps, s2, a_add(k0, j_lo), y2)
    if regime_sign(reg, length_hu(reg.eps, top).sub(t_lo)) <= 0:
        return True
    return False


# ---------------------------------------------------------------------------
# Integer side: segments and the child index as gap forms.
# ---------------------------------------------------------------------------

def first_letter(letter: Int) -> Int:
    return 1 if letter == 1 else 0


def last_letter(letter: Int) -> Int:
    return 1 if letter == 2 else 0


struct GapSegment(Copyable, Movable):
    """FIRST (empty prefix), RUN (first letter then `m` copies of `y`,
    `0 <= m <= run - 1`) or LAST (first letter then the whole run), with the
    `y`-count range as gap forms."""
    var child: Int
    var px: Int
    var pc: Int
    var m_lo: GapForm
    var m_hi: GapForm

    def __init__(out self, reg: Regime, letter: Int, part: Int) raises:
        if letter < 0 or letter > 2 or part < 0 or part > 2:
            raise Error("invalid segment")
        self.px = 0
        self.pc = 0
        self.m_lo = gap_const(0)
        self.m_hi = gap_const(0)
        if part == 0:
            self.child = first_letter(letter)
            return
        self.px = 1 if first_letter(letter) == 0 else 0
        self.pc = 1 - self.px
        var run = reg.run(letter)
        if part == 1:
            self.child = 2
            self.m_hi = run.sub(gap_const(1))
        else:
            self.child = last_letter(letter)
            self.m_lo = run.copy()
            self.m_hi = run.copy()


def _to_aff(f: GapForm) raises -> List[Int]:
    """An `l`-affine gap form as the ray helpers' `[slope, constant]`."""
    if f.cd != 0 or f.cld != 0 or f.cr != 0:
        raise Error("gap form is not l-affine")
    return [f.cl, f.c1]


def _nonneg_l(u: List[Int], l0: Int) -> Bool:
    return u[0] >= 0 and u[0] * l0 + u[1] >= 0


# ---------------------------------------------------------------------------
# Closure.
# ---------------------------------------------------------------------------

def check_seeds(reg: Regime, rows: List[List[Int]], sl: Dict[Int, List[Int]], mut stats: ClosureStats) raises:
    """Twelve candidate seed overlaps `(a,b,0)`, `(a,a,e_b)`, `(b,b,-e_a)`,
    `(b,a,e_b-e_a)`: each is a strict overlap at every member (then a carrier
    label) or at none."""
    for a in range(3):
        for b in range(a + 1, 3):
            for which in range(4):
                var top = a if which < 2 else b
                var bottom = b if which % 2 == 0 else a
                var w = List[Int]([0, 0, 0])
                if which == 1 or which == 3:
                    w[b] += 1
                if which == 2 or which == 3:
                    w[a] -= 1
                var s = w[0] + w[1] + w[2]
                var t = displacement_hu(reg.eps, s, aff(0, w[0]), w[2])
                if strict_inside(reg, top, bottom, t):
                    stats.seeds_real += 1
                    var found = False
                    var key = slice_key(top, bottom, s, w[2])
                    if key in sl:
                        for i in sl[key]:
                            var row = rows[i].copy()
                            if a_le(aff(row[4], row[5]), aff(0, w[0]), reg.l0) == 1 and a_le(aff(0, w[0]), aff(row[6], row[7]), reg.l0) == 1:
                                found = True
                    if not found:
                        raise Error("real swap seed omitted from the regime carrier")
                else:
                    stats.seeds_unreal += 1


def check_row_members(reg: Regime, row: List[Int], mut stats: ClosureStats) raises:
    var lo = aff(row[4], row[5])
    var hi = aff(row[6], row[7])
    if a_le(lo, hi, reg.l0) != 1:
        raise Error("regime carrier row is empty for some l>=l0")
    for k in [lo.copy(), hi.copy()]:
        var t = displacement_hu(reg.eps, row[2], k, row[3])
        if not strict_inside(reg, row[0], row[1], t):
            raise Error("regime carrier row member is not a strict overlap")
        stats.member_checks += 1


def child_base(reg: Regime, row: List[Int]) -> GapForm:
    """`d k_lo + n s + eps y = (row[4] + s) l d + row[5] d + s r + eps y` for `k_lo = row[4] l + row[5]`."""
    return GapForm(reg.eps * row[3], 0, row[5], row[4] + row[2], row[2])


def check_row_closure(reg: Regime, rows: List[List[Int]], sl: Dict[Int, List[Int]], ri: Int,
                      window: Int, mut stats: ClosureStats) raises:
    var row = rows[ri].copy()
    var top = row[0]
    var bottom = row[1]
    var s = row[2]
    var y = row[3]
    var l0 = reg.l0
    var k_lo = aff(row[4], row[5])
    var j_max = a_sub(aff(row[6], row[7]), k_lo)
    var zero = aff(0, 0)
    var has_terminal = False
    var terminal = aff(0, 0)
    if top == bottom and s == 0 and y == 0 and a_le(k_lo, zero, l0) == 1 and a_le(zero, aff(row[6], row[7]), l0) == 1:
        has_terminal = True
        terminal = aff(-row[4], -row[5])
    var base = child_base(reg, row)
    for part_top in range(3):
        var seg_top = GapSegment(reg, top, part_top)
        for part_bottom in range(3):
            var seg_bottom = GapSegment(reg, bottom, part_bottom)
            stats.segments += 1
            var dx = seg_bottom.px - seg_top.px
            var dc = seg_bottom.pc - seg_top.pc
            var child_top = seg_top.child
            var child_bottom = seg_bottom.child
            var k0 = a_add(k_lo, aff(0, s + dx))
            var d_lo = seg_bottom.m_lo.sub(seg_top.m_hi)
            var d_hi = seg_bottom.m_hi.sub(seg_top.m_lo)
            for sign in range(2):
                var yw = window if sign == 0 else -window
                var s2 = 2 * s + dx + dc + yw
                var t0 = displacement_hu(reg.eps, s2, k0, yw)
                var tj = displacement_hu(reg.eps, s2, a_add(k0, j_max), yw)
                if yw > 0:
                    if (regime_sign(reg, length_hu(reg.eps, child_top).sub(t0)) > 0
                            or regime_sign(reg, length_hu(reg.eps, child_top).sub(tj)) > 0):
                        raise Error("child window edge is a strict overlap")
                else:
                    if (regime_sign(reg, t0.add(length_hu(reg.eps, child_bottom))) > 0
                            or regime_sign(reg, tj.add(length_hu(reg.eps, child_bottom))) > 0):
                        raise Error("child window edge is a strict overlap")
                stats.window_checks += 1
            for y2 in range(-window + 1, window):
                var s2 = 2 * s + dx + dc + y2
                stats.y_cases += 1
                # Realizable j: y2 - base - d j in [d_lo, d_hi]  (Lemma 2 divides by d).
                var r_lo = _to_aff(reg.div_ceil(gap_const(y2).sub(base).sub(d_hi)))
                var r_hi = _to_aff(reg.div_floor(gap_const(y2).sub(base).sub(d_lo)))
                var lo = zero.copy()
                var hi = j_max.copy()
                if a_le(r_lo, zero, l0) == 1:
                    lo = zero.copy()
                elif a_le(zero, r_lo, l0) == 1:
                    lo = r_lo.copy()
                else:
                    stats.clip_fallbacks += 1
                if a_le(j_max, r_hi, l0) == 1:
                    hi = j_max.copy()
                elif a_le(r_hi, j_max, l0) == 1:
                    hi = r_hi.copy()
                else:
                    stats.clip_fallbacks += 1
                if a_le(lo, hi, l0) == 0:
                    continue
                var ivs = List[List[Int]]()
                var key = slice_key(child_top, child_bottom, s2, y2)
                if key in sl:
                    for i in sl[key]:
                        var target = rows[i].copy()
                        var t_lo = a_sub(aff(target[4], target[5]), k0)
                        var t_hi = a_sub(aff(target[6], target[7]), k0)
                        ivs.append([t_lo[0], t_lo[1], t_hi[0], t_hi[1]])
                for i in range(1, len(ivs)):
                    var m = i
                    while m > 0 and ivs[m][0] * l0 + ivs[m][1] < ivs[m - 1][0] * l0 + ivs[m - 1][1]:
                        var tmp = ivs[m].copy()
                        ivs[m] = ivs[m - 1].copy()
                        ivs[m - 1] = tmp^
                        m -= 1
                for i in range(1, len(ivs)):
                    if a_le(aff(ivs[i - 1][2], ivs[i - 1][3] + 1), aff(ivs[i][0], ivs[i][1]), l0) != 1:
                        raise Error("UNDECIDED: target intervals are not uniformly ordered")
                var gaps = List[List[Int]]()
                var cursor = lo.copy()
                for iv in ivs:
                    gaps.append([cursor[0], cursor[1], iv[0], iv[1] - 1])
                    cursor = aff(iv[2], iv[3] + 1)
                gaps.append([cursor[0], cursor[1], hi[0], hi[1]])
                if has_terminal:
                    var split = List[List[Int]]()
                    for g in gaps:
                        var g_lo = aff(g[0], g[1])
                        var g_hi = aff(g[2], g[3])
                        var inside = a_le(g_lo, terminal, l0) == 1 and a_le(terminal, g_hi, l0) == 1
                        var outside = a_le(terminal, a_sub(g_lo, aff(0, 1)), l0) == 1 or a_le(a_add(g_hi, aff(0, 1)), terminal, l0) == 1
                        if inside:
                            split.append([g[0], g[1], terminal[0], terminal[1] - 1])
                            split.append([terminal[0], terminal[1] + 1, g[2], g[3]])
                            stats.terminal_splits += 1
                        elif outside:
                            split.append(g.copy())
                        else:
                            raise Error("UNDECIDED: terminal membership in a gap varies with l")
                    gaps = split^
                for g in gaps:
                    var g_lo = a_max(aff(g[0], g[1]), lo, l0)
                    var g_hi = a_min(aff(g[2], g[3]), hi, l0)
                    if a_le(g_lo, g_hi, l0) == 0:
                        continue
                    if _unreal_on(reg, child_top, child_bottom, s2, k0, y2, g_lo, g_hi):
                        stats.gap_geometry += 1
                    else:
                        raise Error("ESCAPE: a real ordered child leaves the regime carrier: row " + String(ri)
                                    + " parts " + String(part_top) + "," + String(part_bottom) + " y'=" + String(y2)
                                    + " child (" + String(child_top) + "," + String(child_bottom) + ",s=" + String(s2) + ") k0=" + String(k0[0]) + "l+" + String(k0[1])
                                    + " j in [" + String(g_lo[0]) + "l+" + String(g_lo[1]) + ", " + String(g_hi[0]) + "l+" + String(g_hi[1]) + "]"
                                    + " realizable [" + String(r_lo[0]) + "l+" + String(r_lo[1]) + ", " + String(r_hi[0]) + "l+" + String(r_hi[1]) + "]")
                stats.covered += 1


def certify_regime_closure(reg: Regime, rows: List[List[Int]], window: Int = 6) raises -> List[Int]:
    """Every carrier label is a strict overlap, every real swap seed is a
    label, and every real ordered child of a non-terminal label is a label,
    at every member of the regime. Raises on any undecided sign or
    comparison and on any escaping child."""
    reg.check()
    if window < 3 or window > 12:
        raise Error("child y-window outside the declared range")
    if len(rows) == 0:
        raise Error("empty regime carrier")
    check_regime_identity(reg.eps)
    check_perron_bound(reg.eps)
    var sl = slices(rows)
    var stats = ClosureStats()
    check_seeds(reg, rows, sl, stats)
    for ri in range(len(rows)):
        stats.rows += 1
        check_row_members(reg, rows[ri], stats)
        check_row_closure(reg, rows, sl, ri, window, stats)
    print("CLASS_A_REGIME_CLOSURE eps=" + String(reg.eps), "regime=" + reg.name(), "l>=" + String(reg.l0), "d>=" + String(reg.d0),
          "rows", stats.rows, "segments", stats.segments, "y_cases", stats.y_cases, "covered", stats.covered,
          "gap_geometry", stats.gap_geometry, "window_checks", stats.window_checks, "seeds_real", stats.seeds_real,
          "seeds_unreal", stats.seeds_unreal, "clip_fallbacks", stats.clip_fallbacks, "terminal_splits", stats.terminal_splits)
    return stats.as_list()


# ---------------------------------------------------------------------------
# Descent.
# ---------------------------------------------------------------------------

def _partition(parts: List[List[Int]], lo: List[Int], hi: List[Int], l0: Int, what: String) raises:
    """`parts` (`[lo_a, lo_b, hi_a, hi_b]`) tile `[lo, hi]` in order, for every `l >= l0`."""
    var sorted = parts.copy()
    for i in range(1, len(sorted)):
        var m = i
        while m > 0 and sorted[m][0] * l0 + sorted[m][1] < sorted[m - 1][0] * l0 + sorted[m - 1][1]:
            var tmp = sorted[m].copy()
            sorted[m] = sorted[m - 1].copy()
            sorted[m - 1] = tmp^
            m -= 1
    var cursor = lo.copy()
    for p in sorted:
        if cursor[0] != p[0] or cursor[1] != p[1]:
            raise Error(what + ": parts do not tile the range")
        if a_le(aff(p[0], p[1]), aff(p[2], p[3]), l0) != 1:
            raise Error(what + ": empty or reversed part")
        cursor = aff(p[2], p[3] + 1)
    var end = a_add(hi, aff(0, 1))
    if cursor[0] != end[0] or cursor[1] != end[1]:
        raise Error(what + ": parts stop short of the range end")


def _potential(piece: List[Int], j: List[Int]) -> List[Int]:
    """`X(l, j) = X_l l + X_j j + X_c` at the affine index `j`, as an affine form in `l`."""
    return aff(piece[5] + piece[6] * j[0], piece[6] * j[1] + piece[7])


def certify_regime_descent(reg: Regime, rows: List[List[Int]], pieces: List[List[Int]],
                           descents: List[List[Int]]) raises -> List[Int]:
    """Returns `[pieces, target pieces, descent rows, bound slope, bound constant]`:
    every carrier label reaches offset zero within `bound slope * l + bound
    constant` inflations at every member of the regime."""
    reg.check()
    var l0 = reg.l0
    var by_row = List[List[List[Int]]]()
    for _ in range(len(rows)):
        by_row.append(List[List[Int]]())
    for p in pieces:
        if len(p) != 8 or p[0] < 0 or p[0] >= len(rows):
            raise Error("malformed potential piece")
        by_row[p[0]].append([p[1], p[2], p[3], p[4]])
    for ri in range(len(rows)):
        var row = rows[ri].copy()
        _partition(by_row[ri], aff(0, 0), aff(row[6] - row[4], row[7] - row[5]), l0, "pieces of row " + String(ri))
    var bound_slope = 0
    var bound_at_l0 = 0
    var targets = 0
    for p in pieces:
        var lo = aff(p[1], p[2])
        var hi = aff(p[3], p[4])
        for j in [lo.copy(), hi.copy()]:
            var x = _potential(p, j)
            if not _nonneg_l(x, l0):
                raise Error("potential is negative on a piece")
            bound_slope = max(bound_slope, x[0])
            bound_at_l0 = max(bound_at_l0, x[0] * l0 + x[1])
        if is_target_piece(rows[p[0]], p):
            targets += 1
    var by_piece = List[List[List[Int]]]()
    for _ in range(len(pieces)):
        by_piece.append(List[List[Int]]())
    for d in descents:
        if len(d) != 9 or d[0] < 0 or d[0] >= len(pieces) or d[8] < 0 or d[8] >= len(pieces):
            raise Error("malformed descent row")
        by_piece[d[0]].append([d[1], d[2], d[3], d[4]])
    for pi in range(len(pieces)):
        var p = pieces[pi].copy()
        if is_target_piece(rows[p[0]], p):
            if len(by_piece[pi]) != 0:
                raise Error("target piece carries descent rows")
            continue
        _partition(by_piece[pi], aff(p[1], p[2]), aff(p[3], p[4]), l0, "descents of piece " + String(pi))
    for d in descents:
        var parent = pieces[d[0]].copy()
        var child = pieces[d[8]].copy()
        var row = rows[parent[0]].copy()
        var crow = rows[child[0]].copy()
        var s_lo = aff(d[1], d[2])
        var s_hi = aff(d[3], d[4])
        var seg_top = GapSegment(reg, row[0], d[5])
        var seg_bottom = GapSegment(reg, row[1], d[6])
        var yp = d[7]
        var dx = seg_bottom.px - seg_top.px
        var dc = seg_bottom.pc - seg_top.pc
        var s2 = 2 * row[2] + dx + dc + yp
        if seg_top.child != crow[0] or seg_bottom.child != crow[1] or s2 != crow[2] or yp != crow[3]:
            raise Error("descent child type disagrees with the named child piece")
        var k_lo = aff(row[4], row[5])
        var k0 = a_add(k_lo, aff(0, row[2] + dx))
        var shift = a_sub(k0, aff(crow[4], crow[5]))
        if not _nonneg_l(a_sub(a_add(s_lo, shift), aff(child[1], child[2])), l0):
            raise Error("descent child leaves its piece below")
        if not _nonneg_l(a_sub(aff(child[3], child[4]), a_add(s_hi, shift)), l0):
            raise Error("descent child leaves its piece above")
        # Realizable at every member: y' - base - d j in [d_lo, d_hi] for j in [s_lo, s_hi]
        # (Lemma 1 after the regime's r substitution).
        var base = child_base(reg, row)
        var d_lo = seg_bottom.m_lo.sub(seg_top.m_hi)
        var d_hi = seg_bottom.m_hi.sub(seg_top.m_lo)
        var d_s_hi = GapForm(0, 0, s_hi[1], s_hi[0], 0)
        var d_s_lo = GapForm(0, 0, s_lo[1], s_lo[0], 0)
        if not reg.nonneg(gap_const(yp).sub(base).sub(d_s_hi).sub(d_lo)):
            raise Error("descent occurrence is not realizable (lower run bound)")
        if not reg.nonneg(d_hi.sub(gap_const(yp).sub(base).sub(d_s_lo))):
            raise Error("descent occurrence is not realizable (upper run bound)")
        for j in [s_lo.copy(), s_hi.copy()]:
            var t_parent = displacement_hu(reg.eps, row[2], a_add(k_lo, j), row[3])
            if not strict_inside(reg, row[0], row[1], t_parent):
                raise Error("descent source is not a strict overlap")
            var t_child = displacement_hu(reg.eps, s2, a_add(k0, j), yp)
            if not strict_inside(reg, crow[0], crow[1], t_child):
                raise Error("descent child is not a strict overlap")
            var drop = a_sub(a_sub(_potential(parent, j), _potential(child, a_add(j, shift))), aff(0, 1))
            if not _nonneg_l(drop, l0):
                raise Error("descent does not lower the potential")
    var bound_const = bound_at_l0 - bound_slope * l0
    print("CLASS_A_REGIME_DESCENT eps=" + String(reg.eps), "regime=" + reg.name(), "l>=" + String(l0), "d>=" + String(reg.d0),
          "pieces", len(pieces), "targets", targets, "descent_rows", len(descents),
          "hit_depth_bound", String(bound_slope) + "l" + ("+" if bound_const >= 0 else "") + String(bound_const))
    return [len(pieces), targets, len(descents), bound_slope, bound_const]


def certify_regime(reg: Regime, rows: List[List[Int]], pieces: List[List[Int]],
                   descents: List[List[Int]]) raises -> List[List[Int]]:
    var closure = certify_regime_closure(reg, rows)
    var descent = certify_regime_descent(reg, rows, pieces, descents)
    print("CLASS_A_REGIME_BOUNDARY_HITTING eps=" + String(reg.eps), "regime=" + reg.name(), "l>=" + String(reg.l0),
          "d>=" + String(reg.d0), "closure=true descent=true universal_139=false")
    return [closure^, descent^]
