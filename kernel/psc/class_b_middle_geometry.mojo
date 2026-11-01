"""Gap-uniform Perron margins for the proposed class-B middle carrier.

h=1/beta, v=g*h, q=g*l+r. Uses the existing rational Bernstein checker
on h=v*t, 0<v<1/l0, 0<t<=1/g0, restricted to the necessary member hull.
No finite fit, containment or descent is inferred from strict row membership.
"""
from std.collections import Dict
from psc.poly_hu import PolyHU, AffHU, sign_within_hull
from psc.gap_form import Regime, KIND_MIDDLE, GapForm, gap_const
from psc.class_a_carrier_closure import aff, a_le, a_max, a_min, a_sub, a_add
from psc.class_b_ray_certificate import slices, slice_key, Stats, sign_regions, meet, _potential, potential_table
from psc.class_b_middle_potential_tables import middle_potentials
from psc.class_b_middle_tables import middle_rows


def bh(i: Int, j: Int, c: Int) -> PolyHU:
    return PolyHU.monomial(i, j, c)


def elimination(eps: Int) -> PolyHU:
    # q*h*(1+h) = (1-2h)(1-h)(1-eps*h) -(6+6eps)h^2 + v*h.
    return PolyHU.const(1).add(bh(1, 0, -3 - eps)).add(bh(2, 0, -4 - 3 * eps)).add(bh(3, 0, -2 * eps)).add(bh(1, 1, 1))


def b_length(eps: Int, letter: Int) raises -> AffHU:
    var p = PolyHU.zero()
    if letter == 0:
        p = PolyHU.const(3).add(bh(1, 0, 3 + 3 * eps)).add(bh(0, 1, -1)).add(bh(2, 0, 3 * eps))
    elif letter == 1:
        p = PolyHU.const(1).add(bh(1, 0, 1 - eps)).add(bh(2, 0, -eps))
    elif letter == 2:
        p = PolyHU.const(1).add(bh(1, 0, 1))
    else:
        raise Error("letter outside 0..2")
    return AffHU(p^, PolyHU.zero(), PolyHU.zero())


def check_b_identity(eps: Int) raises:
    if eps != -1 and eps != 1:
        raise Error("eps must be +-1")
    var h = bh(1, 0, 1)
    var v = bh(0, 1, 1)
    var lx = b_length(eps, 0).a.copy()
    var lc = b_length(eps, 1).a.copy()
    var ly = b_length(eps, 2).a.copy()
    var e = elimination(eps)
    var a0 = lx.mul(h).scale(2).add(ly.mul(h).scale(6 + 6 * eps)).sub(ly.mul(v)).sub(lx).add(e.scale(3))
    var a1 = lx.add(lc).mul(h).sub(lc).add(e)
    var a2 = lx.add(lc).add(ly.scale(eps)).mul(h).sub(ly).add(e)
    if not (a0.is_zero() and a1.is_zero() and a2.is_zero()):
        raise Error("normalized class-B lengths or elimination identity disagree")


def b_displacement(eps: Int, u: Int, d: Int, a: Int, b: Int) -> AffHU:
    # h^2 T = (u-eps*d*h)(1+h) - b*v - a*q*h + a*r*h.
    var p = PolyHU.const(u).add(bh(1, 0, u - eps * d)).add(bh(2, 0, -eps * d)).add(bh(0, 1, -b))
    return AffHU(p^, bh(1, 0, -a), PolyHU.const(a))


def b_sign(reg: Regime, expr: AffHU, depth: Int = 12) raises -> Int:
    var e = elimination(reg.eps)
    var denom = bh(1, 0, 1).add(bh(2, 0, 1))
    var side = e.sub(bh(0, 1, reg.l0)).sub(bh(1, 1, reg.l0)).sub(bh(1, 0, reg.j)).sub(bh(2, 0, reg.j))
    var endpoints = List[PolyHU]([bh(1, 0, reg.j), bh(0, 1, 1).sub(bh(1, 0, reg.j1))])
    var result = 2
    for rh in endpoints:
        var numerator = expr.a.add(expr.c.mul(rh)).mul(denom).add(expr.b.mul(e))
        var s = sign_within_hull(numerator, side, reg.l0, reg.d0, depth)
        if result == 2:
            result = s
        elif result != s:
            raise Error("middle residue endpoints have different certified signs")
    return result


def b_cached_sign(reg: Regime, expr: AffHU, mut cache: Dict[String, Int]) raises -> Int:
    var key = String(expr.a) + ";" + String(expr.b) + ";" + String(expr.c)
    if key not in cache:
        cache[key] = b_sign(reg, expr)
    return cache[key]


def certify_middle_members(eps: Int, l0: Int = 4) raises -> Int:
    var reg = Regime(eps, KIND_MIDDLE, 2 if eps == 1 else 6, 14 if eps == 1 else 6, l0, 16 if eps == 1 else 12)
    reg.check()
    check_b_identity(eps)
    var rows = middle_rows(eps)
    var cache = Dict[String, Int]()
    for i in range(len(rows)):
        var row = rows[i].copy()
        if a_le(aff(row[4], row[5]), aff(row[6], row[7]), l0) != 1:
            raise Error("empty middle carrier row ", i)
        for end in range(2):
            var t = b_displacement(eps, row[2], row[3], row[4 + 2 * end], row[5 + 2 * end])
            try:
                if b_cached_sign(reg, b_length(eps, row[0]).sub(t), cache) <= 0 or b_cached_sign(reg, t.add(b_length(eps, row[1])), cache) <= 0:
                    raise Error("not strict")
            except err:
                raise Error("MIDDLE_ROW_REFUSAL eps=" + String(eps) + " row=" + String(i) + " end=" + String(end) + " " + String(err))
    return len(rows)


def certify_middle_core(eps: Int, l0: Int = 4, omit: Bool = False) raises -> Int:
    """Every strict core label and every strict swap seed belongs to the
    proposed table, for all parameters of the middle regime. Not closure."""
    var reg = Regime(eps, KIND_MIDDLE, 2 if eps == 1 else 6, 14 if eps == 1 else 6, l0, 16 if eps == 1 else 12)
    reg.check()
    check_b_identity(eps)
    var rows = middle_rows(eps)
    if omit:
        var incomplete = List[List[Int]]()
        for i in range(1, len(rows)):
            incomplete.append(rows[i].copy())
        rows = incomplete^
    var cache = Dict[String, Int]()
    var count = 0
    for top in range(3):
        for bottom in range(3):
            for u in range(-3, 4):
                for d in range(-6, 7):
                    for k in range(-2, 3):
                        var t = b_displacement(eps, u, d, 0, k)
                        var right = b_cached_sign(reg, b_length(eps, top).sub(t), cache)
                        var left = b_cached_sign(reg, t.add(b_length(eps, bottom)), cache)
                        if right <= 0 or left <= 0:
                            continue
                        var found = False
                        for row in rows:
                            if row[0] == top and row[1] == bottom and row[2] == u and row[3] == d and a_le(aff(row[4], row[5]), aff(0, k), l0) == 1 and a_le(aff(0, k), aff(row[6], row[7]), l0) == 1:
                                found = True
                        if not found:
                            raise Error("strict core omitted: ", top, bottom, u, d, k)
                        count += 1
    # All canonical swap candidates have |u|<=3, |d|<=3 and |k|<=1:
    # this direct coordinate check ties seed containment to the core check.
    for a in range(3):
        for b in range(a + 1, 3):
            for which in range(4):
                var w = List[Int]([0, 0, 0])
                if which == 1 or which == 3:
                    w[b] += 1
                if which == 2 or which == 3:
                    w[a] -= 1
                if abs(3 * w[0] + w[1] + w[2]) > 3 or abs(w[1] - 3 * w[0]) > 6 or abs(w[0]) > 2:
                    raise Error("swap candidate outside the core")
    return count


def quotient_bounds(reg: Regime, f: GapForm, ceil: Bool) raises -> List[Int]:
    """Certified outer integer bounds for f/g. No single rounding value is
    assumed across the residue regime. Result [slope, lower, slope, upper]."""
    if f.cl != 0:
        raise Error("quotient has a pure l term")
    var v = GapForm(f.c1, 0, 0, 0, f.cr)
    var lower = -1000
    var upper = 1000
    for m in range(-32, 33):
        # ceil(v/g)>=m iff v>(m-1)g; floor(v/g)>=m iff v>=mg.
        var below = v.sub(GapForm(0, 0, m - 1 if ceil else m, 0, 0)).sub(gap_const(1 if ceil else 0))
        if reg.nonneg(below):
            lower = max(lower, m)
        # ceil(v/g)<=m iff v<=mg; floor(v/g)<=m iff v<(m+1)g.
        var above = GapForm(0, 0, m if ceil else m + 1, 0, 0).sub(v).sub(gap_const(0 if ceil else 1))
        if reg.nonneg(above):
            upper = min(upper, m)
    if lower == -1000 or upper == 1000:
        raise Error("quotient bound search exhausted: no verdict")
    return [f.cld, f.cd + lower, f.cld, f.cd + upper]


def b_run(eps: Int, t: Int) -> GapForm:
    if t == 0:
        return GapForm(6 + 6 * eps, 0, -1, 3, 3)
    return GapForm(eps if t == 2 else 0, 0, 0, 1, 1)


def b_segment(eps: Int, t: Int, part: Int) -> List[GapForm]:
    if part == 0:
        return [gap_const(0), gap_const(0)]
    var run = b_run(eps, t)
    if part == 1:
        return [gap_const(0), run.sub(gap_const(1))]
    return [run, run]


def middle_gap_outside(reg: Regime, ct: Int, cb: Int, u2: Int, d2: Int,
                       kc: List[Int], lo: List[Int], hi: List[Int], mut cache: Dict[String, Int]) raises -> Bool:
    var tlo = b_displacement(reg.eps, u2, d2, kc[0] - hi[0], kc[1] - hi[1])
    var thi = b_displacement(reg.eps, u2, d2, kc[0] - lo[0], kc[1] - lo[1])
    return b_cached_sign(reg, tlo.add(b_length(reg.eps, cb)), cache) <= 0 or b_cached_sign(reg, b_length(reg.eps, ct).sub(thi), cache) <= 0


def certify_middle_closure(eps: Int, l0: Int = 4) raises -> Int:
    """Attempt full closure with outer quotient bounds; a refusal is an exact
    remaining inequality for this checker, not an escaping actual child."""
    var reg = Regime(eps, KIND_MIDDLE, 2 if eps == 1 else 6, 14 if eps == 1 else 6, l0, 16 if eps == 1 else 12)
    reg.check()
    check_b_identity(eps)
    var rows = middle_rows(eps)
    var cache = Dict[String, Int]()
    var sl = slices(rows)
    var checks = 0
    for ri in range(len(rows)):
        if ri % 50 == 0:
            print("CLASS_B_MIDDLE_CLOSURE_PROGRESS eps", eps, "row", ri)
        var row = rows[ri].copy()
        var J = aff(row[6] - row[4], row[7] - row[5])
        var terminal = row[0] == row[1] and row[2] == 0 and row[3] == 0 and a_le(aff(row[4], row[5]), aff(0, 0), l0) == 1 and a_le(aff(0, 0), aff(row[6], row[7]), l0) == 1
        var term = aff(-row[4], -row[5])
        for pt in range(3):
            var ct = (0 if row[0] == 0 else 1) if pt == 0 else (2 if pt == 1 else 0)
            var apx = (1 if row[0] == 0 else 0) if pt > 0 else 0
            var apc = (0 if row[0] == 0 else 1) if pt > 0 else 0
            var a = b_segment(eps, row[0], pt)
            for pb in range(3):
                var cb = (0 if row[1] == 0 else 1) if pb == 0 else (2 if pb == 1 else 0)
                var dx = ((1 if row[1] == 0 else 0) if pb > 0 else 0) - apx
                var dc = ((0 if row[1] == 0 else 1) if pb > 0 else 0) - apc
                var b = b_segment(eps, row[1], pb)
                var d2 = -2 * row[2] + dc - 3 * dx
                var kc = aff(-row[4], row[2] - row[5] + dx)
                for uw in [-6, 6]:
                    for end in [aff(0, 0), J.copy()]:
                        var t = b_displacement(eps, uw, d2, kc[0] - end[0], kc[1] - end[1])
                        var sign = b_cached_sign(reg, t.add(b_length(eps, cb)), cache) if uw < 0 else b_cached_sign(reg, b_length(eps, ct).sub(t), cache)
                        if sign > 0:
                            raise Error("middle closure window is insufficient")
                for u2 in range(-5, 6):
                    var base = GapForm((4 + eps) * row[2] - eps * row[3] + 3 * dx + dc - u2, 0, -row[5], row[2] - row[4], row[2])
                    var low = quotient_bounds(reg, base.add(b[0]).sub(a[1]), True)
                    var high = quotient_bounds(reg, base.add(b[1]).sub(a[0]), False)
                    var lo = a_max(aff(0, 0), aff(low[0], low[1]), l0)
                    var hi = a_min(J, aff(high[2], high[3]), l0)
                    if a_le(lo, hi, l0) == 0:
                        continue
                    var ivs = List[List[Int]]()
                    var key = slice_key(ct, cb, u2, d2)
                    if key in sl:
                        for ci in sl[key]:
                            ivs.append([kc[0] - rows[ci][6], kc[1] - rows[ci][7], kc[0] - rows[ci][4], kc[1] - rows[ci][5]])
                    for i in range(1, len(ivs)):
                        var iv = ivs[i].copy()
                        var j = i
                        while j > 0 and iv[0] * l0 + iv[1] < ivs[j - 1][0] * l0 + ivs[j - 1][1]:
                            ivs[j] = ivs[j - 1].copy()
                            j -= 1
                        ivs[j] = iv^
                    for i in range(1, len(ivs)):
                        if a_le(aff(ivs[i - 1][2], ivs[i - 1][3] + 1), aff(ivs[i][0], ivs[i][1]), l0) != 1:
                            raise Error("middle child interval order is undecided")
                    var gaps = List[List[Int]]()
                    var cur = lo.copy()
                    for iv in ivs:
                        gaps.append([cur[0], cur[1], iv[0], iv[1] - 1])
                        cur = aff(iv[2], iv[3] + 1)
                    gaps.append([cur[0], cur[1], hi[0], hi[1]])
                    for gap in gaps:
                        var pieces = List[List[Int]]([gap.copy()])
                        if terminal and a_le(aff(gap[0], gap[1]), term, l0) == 1 and a_le(term, aff(gap[2], gap[3]), l0) == 1:
                            pieces = [List[Int]([gap[0], gap[1], term[0], term[1] - 1]), List[Int]([term[0], term[1] + 1, gap[2], gap[3]])]
                        elif terminal and a_le(term, aff(gap[0], gap[1] - 1), l0) != 1 and a_le(aff(gap[2], gap[3] + 1), term, l0) != 1:
                            raise Error("undecided terminal position")
                        for piece in pieces:
                            var glo = a_max(lo, aff(piece[0], piece[1]), l0)
                            var ghi = a_min(hi, aff(piece[2], piece[3]), l0)
                            if a_le(glo, ghi, l0) == 0:
                                continue
                            try:
                                if not middle_gap_outside(reg, ct, cb, u2, d2, kc, glo, ghi, cache):
                                    raise Error("strictness not excluded")
                            except err:
                                raise Error("MIDDLE_CLOSURE_REFUSAL eps=" + String(eps) + " row=" + String(ri) + " pt=" + String(pt) + " pb=" + String(pb) + " u2=" + String(u2) + " child_d=" + String(d2) + " jlo=" + String(glo) + " jhi=" + String(ghi) + " " + String(err))
                            checks += 1
    return checks


struct MiddleEdge(Copyable, Movable):
    var ct: Int
    var cb: Int
    var u2: Int
    var d2: Int
    var kc: List[Int]
    var r_lo: List[Int]
    var r_hi: List[Int]

    def __init__(out self, reg: Regime, row: List[Int], pt: Int, pb: Int, u2: Int) raises:
        var eps = reg.eps
        self.ct = (0 if row[0] == 0 else 1) if pt == 0 else (2 if pt == 1 else 0)
        self.cb = (0 if row[1] == 0 else 1) if pb == 0 else (2 if pb == 1 else 0)
        var dx = ((1 if row[1] == 0 else 0) if pb > 0 else 0) - ((1 if row[0] == 0 else 0) if pt > 0 else 0)
        var dc = ((0 if row[1] == 0 else 1) if pb > 0 else 0) - ((0 if row[0] == 0 else 1) if pt > 0 else 0)
        self.u2 = u2
        self.d2 = -2 * row[2] + dc - 3 * dx
        self.kc = aff(-row[4], row[2] - row[5] + dx)
        var a = b_segment(eps, row[0], pt)
        var b = b_segment(eps, row[1], pb)
        var base = GapForm((4 + eps) * row[2] - eps * row[3] + 3 * dx + dc - u2, 0, -row[5], row[2] - row[4], row[2])
        var low = quotient_bounds(reg, base.add(b[0]).sub(a[1]), True)
        var high = quotient_bounds(reg, base.add(b[1]).sub(a[0]), False)
        # Inner bounds: every j in this interval is realizable for every
        # parameter in the regime, even when the exact rounding varies.
        self.r_lo = aff(low[2], low[3])
        self.r_hi = aff(high[0], high[1])


def middle_child_intervals(rows: List[List[Int]], sl: Dict[Int, List[Int]], e: MiddleEdge, l0: Int) raises -> List[List[Int]]:
    var out = List[List[Int]]()
    var key = slice_key(e.ct, e.cb, e.u2, e.d2)
    if key in sl:
        for i in sl[key]:
            out.append([e.kc[0] - rows[i][6], e.kc[1] - rows[i][7], e.kc[0] - rows[i][4], e.kc[1] - rows[i][5]])
    for i in range(1, len(out)):
        var iv = out[i].copy()
        var j = i
        while j > 0 and iv[0] * l0 + iv[1] < out[j - 1][0] * l0 + out[j - 1][1]:
            out[j] = out[j - 1].copy()
            j -= 1
        out[j] = iv^
    for i in range(1, len(out)):
        if a_le(aff(out[i - 1][2], out[i - 1][3] + 1), aff(out[i][0], out[i][1]), l0) != 1:
            raise Error("middle descent child order undecided")
    return out^


def check_middle_row_descent(reg: Regime, rows: List[List[Int]], sl: Dict[Int, List[Int]], pot: Dict[Int, Int],
                      ri: Int, l0: Int, mut stats: Stats) raises:
    var row = rows[ri].copy()
    var k_lo = aff(row[4], row[5])
    var j_max = a_sub(aff(row[6], row[7]), k_lo)
    for region in sign_regions(k_lo, j_max, l0):
        var s = region[0]
        stats.pieces += 1
        if s == 0 and row[2] == 0 and row[3] == 0:
            stats.targets += 1
            continue
        var b_parent = _potential(pot, row[0], row[1], row[2], row[3], s)
        if b_parent < 0:
            raise Error("carrier piece without a potential")
        stats.max_potential_constant = max(stats.max_potential_constant, b_parent)
        var good = List[List[Int]]()
        for part_top in range(3):
            for part_bottom in range(3):
                for u2 in range(-5, 6):
                    var e = MiddleEdge(reg, row, part_top, part_bottom, u2)
                    for iv in middle_child_intervals(rows, sl, e, l0):
                        for t in range(-1, 2):
                            var b_child = _potential(pot, e.ct, e.cb, e.u2, e.d2, t)
                            if b_child < 0:
                                continue
                            # child sign region: k' = kc - j < 0, = 0, > 0
                            var parts = List[List[Int]]([List[Int]([region[1], region[2], region[3], region[4]]),
                                                         List[Int]([e.r_lo[0], e.r_lo[1], e.r_hi[0], e.r_hi[1]]),
                                                         List[Int]([iv[0], iv[1], iv[2], iv[3]])])
                            if t == -1:
                                parts.append([e.kc[0], e.kc[1] + 1, region[3], region[4]])
                            elif t == 0:
                                parts.append([e.kc[0], e.kc[1], e.kc[0], e.kc[1]])
                            else:
                                parts.append([region[1], region[2], e.kc[0], e.kc[1] - 1])
                            var m = meet(parts, l0)
                            if m[0] != 1:
                                continue
                            # D(j) = s (k_lo + j) + b_parent - t (kc - j) - b_child - 1 >= 0 at both ends.
                            var ok = True
                            for end in [aff(m[1], m[2]), aff(m[3], m[4])]:
                                var dj = a_sub(a_add(aff(s * (k_lo[0] + end[0]), s * (k_lo[1] + end[1])),
                                                     aff(0, b_parent - b_child - 1)),
                                               aff(t * (e.kc[0] - end[0]), t * (e.kc[1] - end[1])))
                                if a_le(aff(0, 0), dj, l0) != 1:
                                    ok = False
                            if ok:
                                good.append([m[1], m[2], m[3], m[4]])
                                stats.descent_candidates += 1
        # Greedy cover of the piece by descending child intervals.
        var cursor = aff(region[1], region[2])
        var top_end = aff(region[3], region[4] + 1)
        while a_le(top_end, cursor, l0) != 1:
            var best = -1
            for i in range(len(good)):
                if a_le(aff(good[i][0], good[i][1]), cursor, l0) == 1 and a_le(cursor, aff(good[i][2], good[i][3]), l0) == 1:
                    if best < 0 or a_le(aff(good[best][2], good[best][3]), aff(good[i][2], good[i][3]), l0) == 1:
                        best = i
            if best < 0:
                raise Error("MIDDLE_NO_DESCENT row=" + String(ri) + " sign=" + String(s) + " cursor=" + String(cursor) + " end=" + String(top_end))
            cursor = aff(good[best][2], good[best][3] + 1)
            stats.descent_intervals += 1



def certify_middle_descent(eps: Int, l0: Int = 4, zero: Bool = False, g0: Int = 0) raises -> List[Int]:
    var reg = Regime(eps, KIND_MIDDLE, 2 if eps == 1 else 6, 14 if eps == 1 else 6, l0, 16 if eps == 1 else 12)
    if g0 != 0:
        if g0 < reg.d0:
            raise Error("cannot lower the proposed middle gap floor")
        reg.d0 = g0
    reg.check()
    check_b_identity(eps)
    var rows = middle_rows(eps)
    var sl = slices(rows)
    var ps = middle_potentials(eps)
    if zero:
        for i in range(len(ps)):
            ps[i][5] = 0
    var pot = potential_table(ps)
    var stats = Stats()
    for ri in range(len(rows)):
        check_middle_row_descent(reg, rows, sl, pot, ri, l0, stats)
    return stats.as_list()
