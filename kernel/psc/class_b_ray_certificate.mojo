"""Uniform closure and descent of a typed class-B top-layer carrier on a residue ray.

Ray data are those of `psc.class_b_ray_line.BRay`; a carrier row
`(top, bottom, u, d, a, b, c, e)` holds the labels with `u = 3k+c+y`,
`d = c-3k` and `a l + b <= k <= c l + e` (the step-1 encoding of
docs/class-b-label-rays-2026-10-23.md). A potential row
`(top, bottom, u, d, s, b0)` gives every label of that slice with
`sign(k) = s` the potential `X = |k| + b0`.

**Children (Lemma 4).** Each image `sigma(t)` has FIRST (empty prefix, child
letter `x` for `t = x`, `c` otherwise), RUN (prefix = first letter then `m`
copies of `y`, `0 <= m < R(t)`, child `y`) and LAST (prefix = first letter then
the run, child `x`) segments, with run lengths `R = (p, q, r)`. For a segment
pair with first-letter differences `dx, dc` and run difference `m_b - m_t`,
`w' = M w + prefix_b - prefix_t` gives

  k' = u - k + dx,    d' = -2u + dc - 3dx,
  u' = (4 + r) u - g k - eps d + 3dx + dc + (m_b - m_t),

and `T(w') = beta T(w) + pos_b - pos_t`; the child is an occurrence iff it is
a strict overlap. For fixed `u'` the attainable `m_b - m_t` is the whole
integer interval of the two segments, so with `k = k_lo + j` the realizable
`j` are `[ceil(./g), floor(./g)]`, affine in `l` (slopes are multiples of `g`).

**Closure (Theorem A).** For every `q >= q0` on the ray: every carrier label is
a strict overlap; every real canonical swap seed is a carrier label; and every
real child of every non-terminal carrier label is a carrier label. The child
displacement increases in `u'` (slope `beta(beta+1)`) and in `j` (`k'`
decreases, slope `g beta`), so a window `|u'| < W` and one sign per gap end
decide every case. An escaping real child raises.

**Descent (Theorem B).** On each row and each sign region of `k`, the
non-target labels are covered by finitely many affine sub-intervals, each with
one realizable child carrier row and child sign region on which
`X_parent - X_child - 1 >= 0` at both ends for every `l >= l0`. Targets are the
offset-zero labels `w = 0`. Hence every carrier label reaches offset zero in at
most `X` inflations along actual children. A piece with no covering child
raises.

Every sign is decided for all `beta >= beta_low` (`BRay.sign`), every affine
comparison for every integer `l >= l0`; an undecided step refuses.
Source note: docs/class-b-ray-certificate-2026-10-27.md.
"""
from std.collections import Dict
from psc.class_a_carrier_closure import AffH, pmul, psub, aff, a_add, a_sub, a_le, a_div_ceil, a_div_floor, a_max, a_min
from psc.class_b_ray_line import BRay, check_line_identity, check_bound
from psc.overlap_seed_patch import build_seed_overlap_graph_from_tables, build_seed_overlap_tables_screened
from psc.vertex_coincidence import length_matrix, offset_vector


comptime WINDOW = 6


def slice_key(top: Int, bottom: Int, u: Int, d: Int) raises -> Int:
    if top < 0 or top > 2 or bottom < 0 or bottom > 2 or u < -16 or u > 16 or d < -32 or d > 32:
        raise Error("slice key outside the typed range")
    return ((top * 3 + bottom) * 33 + (u + 16)) * 65 + (d + 32)


def slices(rows: List[List[Int]]) raises -> Dict[Int, List[Int]]:
    var out = Dict[Int, List[Int]]()
    for i in range(len(rows)):
        if len(rows[i]) != 8:
            raise Error("malformed class-B carrier row")
        var key = slice_key(rows[i][0], rows[i][1], rows[i][2], rows[i][3])
        if key not in out:
            out[key] = List[Int]()
        out[key].append(i)
    return out^


def potential_table(rows: List[List[Int]]) raises -> Dict[Int, Int]:
    var out = Dict[Int, Int]()
    for row in rows:
        if len(row) != 6 or row[4] < -1 or row[4] > 1 or row[5] < 0:
            raise Error("malformed class-B potential row")
        var key = slice_key(row[0], row[1], row[2], row[3]) * 3 + row[4] + 1
        if key in out:
            raise Error("duplicate class-B potential row")
        out[key] = row[5]
    return out^


def displacement(ray: BRay, u: Int, d: Int, k: List[Int]) -> AffH:
    """`T = (beta+1)(u beta - eps d) - g beta k` with `k = k[0] l + k[1]`, as `a + l b`."""
    return AffH(psub(pmul([1, 1], [-ray.eps * d, u]), [0, ray.g * k[1]]), [0, -ray.g * k[0]])


def scaled_length(ray: BRay, letter: Int) raises -> AffH:
    return AffH(ray.length(letter), [])


def strict_inside(ray: BRay, top: Int, bottom: Int, t: AffH, q0: Int) raises -> Bool:
    return ray.sign(scaled_length(ray, top).sub(t), q0) > 0 and ray.sign(t.add(scaled_length(ray, bottom)), q0) > 0


struct Segment(Copyable, Movable):
    """FIRST (part 0), RUN (part 1) or LAST (part 2) of `sigma(letter)`."""
    var child: Int
    var px: Int
    var pc: Int
    var m_lo: List[Int]
    var m_hi: List[Int]

    def __init__(out self, ray: BRay, letter: Int, part: Int) raises:
        if letter < 0 or letter > 2 or part < 0 or part > 2:
            raise Error("invalid segment")
        if part == 0:
            self.child = 0 if letter == 0 else 1
            self.px = 0
            self.pc = 0
            self.m_lo = aff(0, 0)
            self.m_hi = aff(0, 0)
            return
        self.px = 1 if letter == 0 else 0
        self.pc = 1 - self.px
        var run = ray.run(letter)
        if part == 1:
            self.child = 2
            self.m_lo = aff(0, 0)
            self.m_hi = a_sub(run, aff(0, 1))
        else:
            self.child = 0
            self.m_lo = run.copy()
            self.m_hi = run.copy()


struct Edge(Copyable, Movable):
    """A symbolic child of a carrier row under one segment pair and child sum `u'`:
    `k' = kc - j`, child type `(ct, cb, u', d')`, realizable `j` in `[r_lo, r_hi]`."""
    var ct: Int
    var cb: Int
    var u2: Int
    var d2: Int
    var kc: List[Int]
    var r_lo: List[Int]
    var r_hi: List[Int]

    def __init__(out self, ray: BRay, row: List[Int], st: Segment, sb: Segment, u2: Int) raises:
        var u = row[2]
        var d = row[3]
        var dx = sb.px - st.px
        var dc = sb.pc - st.pc
        self.ct = st.child
        self.cb = sb.child
        self.u2 = u2
        self.d2 = -2 * u + dc - 3 * dx
        self.kc = aff(-row[4], u - row[5] + dx)
        # g j in [base + (m_b - m_t)_min - u', base + (m_b - m_t)_max - u']
        var base = aff(ray.g * (u - row[4]), (4 + ray.r + ray.eps) * u - ray.g * row[5] - ray.eps * d + 3 * dx + dc)
        self.r_lo = a_div_ceil(a_sub(a_add(base, a_sub(sb.m_lo, st.m_hi)), aff(0, u2)), ray.g)
        self.r_hi = a_div_floor(a_sub(a_add(base, a_sub(sb.m_hi, st.m_lo)), aff(0, u2)), ray.g)


struct Stats(Copyable, Movable):
    var rows: Int
    var member_checks: Int
    var seeds_real: Int
    var seeds_unreal: Int
    var y_cases: Int
    var covered: Int
    var gap_geometry: Int
    var window_checks: Int
    var clip_fallbacks: Int
    var terminal_splits: Int
    var pieces: Int
    var targets: Int
    var descent_intervals: Int
    var descent_candidates: Int
    var max_potential_constant: Int

    def __init__(out self):
        self.rows = 0
        self.member_checks = 0
        self.seeds_real = 0
        self.seeds_unreal = 0
        self.y_cases = 0
        self.covered = 0
        self.gap_geometry = 0
        self.window_checks = 0
        self.clip_fallbacks = 0
        self.terminal_splits = 0
        self.pieces = 0
        self.targets = 0
        self.descent_intervals = 0
        self.descent_candidates = 0
        self.max_potential_constant = 0

    def as_list(self) -> List[Int]:
        return [self.rows, self.member_checks, self.seeds_real, self.seeds_unreal, self.y_cases,
                self.covered, self.gap_geometry, self.window_checks, self.clip_fallbacks,
                self.terminal_splits, self.pieces, self.targets, self.descent_intervals,
                self.descent_candidates, self.max_potential_constant]


def meet(parts: List[List[Int]], l0: Int) -> List[Int]:
    """Intersection of affine intervals `[lo_a, lo_b, hi_a, hi_b]` on the ray:
    `(1, lo, hi)` when nonempty for every `l >= l0`, `(0, ...)` when empty for
    every such `l`, `(-1, ...)` when an order is undecided; flattened as
    `[status, lo_a, lo_b, hi_a, hi_b]`."""
    var lo = aff(parts[0][0], parts[0][1])
    var hi = aff(parts[0][2], parts[0][3])
    for i in range(1, len(parts)):
        var a = aff(parts[i][0], parts[i][1])
        var b = aff(parts[i][2], parts[i][3])
        if a_le(lo, a, l0) == 1:
            lo = a^
        elif a_le(a, lo, l0) != 1:
            return [-1, lo[0], lo[1], hi[0], hi[1]]
        if a_le(b, hi, l0) == 1:
            hi = b^
        elif a_le(hi, b, l0) != 1:
            return [-1, lo[0], lo[1], hi[0], hi[1]]
    var order = a_le(lo, hi, l0)
    return [1 if order == 1 else (0 if order == 0 else -1), lo[0], lo[1], hi[0], hi[1]]


def check_seeds(ray: BRay, rows: List[List[Int]], sl: Dict[Int, List[Int]], l0: Int, q0: Int,
                mut stats: Stats) raises:
    """The twelve candidates `(a,b,0)`, `(a,a,e_b)`, `(b,b,-e_a)`, `(b,a,e_b-e_a)`."""
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
                var u = 3 * w[0] + w[1] + w[2]
                var d = w[1] - 3 * w[0]
                if strict_inside(ray, top, bottom, displacement(ray, u, d, aff(0, w[0])), q0):
                    stats.seeds_real += 1
                    var found = False
                    var key = slice_key(top, bottom, u, d)
                    if key in sl:
                        for i in sl[key]:
                            if a_le(aff(rows[i][4], rows[i][5]), aff(0, w[0]), l0) == 1 and a_le(aff(0, w[0]), aff(rows[i][6], rows[i][7]), l0) == 1:
                                found = True
                    if not found:
                        raise Error("real swap seed omitted from the class-B carrier")
                else:
                    stats.seeds_unreal += 1


def check_row_members(ray: BRay, row: List[Int], l0: Int, q0: Int, mut stats: Stats) raises:
    var lo = aff(row[4], row[5])
    var hi = aff(row[6], row[7])
    if a_le(lo, hi, l0) != 1:
        raise Error("class-B carrier row is empty for some l>=l0")
    for k in [lo.copy(), hi.copy()]:
        if not strict_inside(ray, row[0], row[1], displacement(ray, row[2], row[3], k), q0):
            raise Error("class-B carrier row member is not a strict overlap")
        stats.member_checks += 1


def child_intervals(rows: List[List[Int]], sl: Dict[Int, List[Int]], e: Edge, l0: Int) raises -> List[List[Int]]:
    """Parent j-intervals `[lo_a, lo_b, hi_a, hi_b, row]` whose child is in a carrier
    row of the child slice: `K_lo <= kc - j <= K_hi`, sorted and uniformly ordered."""
    var ivs = List[List[Int]]()
    var key = slice_key(e.ct, e.cb, e.u2, e.d2)
    if key in sl:
        for i in sl[key]:
            var lo = a_sub(e.kc, aff(rows[i][6], rows[i][7]))
            var hi = a_sub(e.kc, aff(rows[i][4], rows[i][5]))
            ivs.append([lo[0], lo[1], hi[0], hi[1], i])
    for i in range(1, len(ivs)):
        var m = i
        while m > 0 and ivs[m][0] * l0 + ivs[m][1] < ivs[m - 1][0] * l0 + ivs[m - 1][1]:
            var tmp = ivs[m].copy()
            ivs[m] = ivs[m - 1].copy()
            ivs[m - 1] = tmp^
            m -= 1
    for i in range(1, len(ivs)):
        if a_le(aff(ivs[i - 1][2], ivs[i - 1][3] + 1), aff(ivs[i][0], ivs[i][1]), l0) != 1:
            raise Error("UNDECIDED: child carrier intervals are not uniformly ordered")
    return ivs^


def check_row_closure(ray: BRay, rows: List[List[Int]], sl: Dict[Int, List[Int]], ri: Int,
                      l0: Int, q0: Int, mut stats: Stats) raises:
    var row = rows[ri].copy()
    var k_lo = aff(row[4], row[5])
    var j_max = a_sub(aff(row[6], row[7]), k_lo)
    var zero = aff(0, 0)
    var has_terminal = row[0] == row[1] and row[2] == 0 and row[3] == 0 and a_le(k_lo, zero, l0) == 1 and a_le(zero, aff(row[6], row[7]), l0) == 1
    var terminal = a_sub(zero, k_lo)
    for part_top in range(3):
        var st = Segment(ray, row[0], part_top)
        for part_bottom in range(3):
            var sb = Segment(ray, row[1], part_bottom)
            # Window: at u' = +W the child is at or beyond its right boundary for
            # j = 0 and j = J, hence for every j and every u' >= W; likewise -W.
            for sgn in range(2):
                var e = Edge(ray, row, st, sb, WINDOW if sgn == 0 else -WINDOW)
                for kk in [e.kc.copy(), a_sub(e.kc, j_max)]:
                    var t = displacement(ray, e.u2, e.d2, kk)
                    if sgn == 0 and ray.sign(scaled_length(ray, e.ct).sub(t), q0) > 0:
                        raise Error("child window edge is a strict overlap")
                    if sgn == 1 and ray.sign(t.add(scaled_length(ray, e.cb)), q0) > 0:
                        raise Error("child window edge is a strict overlap")
                stats.window_checks += 1
            for u2 in range(-WINDOW + 1, WINDOW):
                var e = Edge(ray, row, st, sb, u2)
                stats.y_cases += 1
                var lo = zero.copy()
                var hi = j_max.copy()
                if a_le(zero, e.r_lo, l0) == 1:
                    lo = e.r_lo.copy()
                elif a_le(e.r_lo, zero, l0) != 1:
                    stats.clip_fallbacks += 1
                if a_le(e.r_hi, j_max, l0) == 1:
                    hi = e.r_hi.copy()
                elif a_le(j_max, e.r_hi, l0) != 1:
                    stats.clip_fallbacks += 1
                if a_le(lo, hi, l0) == 0:
                    continue
                var ivs = child_intervals(rows, sl, e, l0)
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
                        if a_le(g_lo, terminal, l0) == 1 and a_le(terminal, g_hi, l0) == 1:
                            split.append([g[0], g[1], terminal[0], terminal[1] - 1])
                            split.append([terminal[0], terminal[1] + 1, g[2], g[3]])
                            stats.terminal_splits += 1
                        elif a_le(terminal, a_sub(g_lo, aff(0, 1)), l0) == 1 or a_le(a_add(g_hi, aff(0, 1)), terminal, l0) == 1:
                            split.append(g.copy())
                        else:
                            raise Error("UNDECIDED: terminal membership in a gap varies with l")
                    gaps = split^
                for g in gaps:
                    var g_lo = a_max(aff(g[0], g[1]), lo, l0)
                    var g_hi = a_min(aff(g[2], g[3]), hi, l0)
                    if a_le(g_lo, g_hi, l0) == 0:
                        continue
                    # T' increases in j: unreal on the gap iff at or left of the
                    # left boundary at its upper end, or at or right of the right
                    # boundary at its lower end.
                    var t_hi = displacement(ray, u2, e.d2, a_sub(e.kc, g_hi))
                    var t_lo = displacement(ray, u2, e.d2, a_sub(e.kc, g_lo))
                    if ray.sign(t_hi.add(scaled_length(ray, e.cb)), q0) <= 0 or ray.sign(scaled_length(ray, e.ct).sub(t_lo), q0) <= 0:
                        stats.gap_geometry += 1
                    else:
                        raise Error("ESCAPE: a real ordered child leaves the class-B carrier")
                stats.covered += 1


def _potential(pot: Dict[Int, Int], top: Int, bottom: Int, u: Int, d: Int, s: Int) raises -> Int:
    var key = slice_key(top, bottom, u, d) * 3 + s + 1
    if key not in pot:
        return -1
    return pot[key]


def sign_regions(k_lo: List[Int], j_max: List[Int], l0: Int) raises -> List[List[Int]]:
    """`[s, lo_a, lo_b, hi_a, hi_b]` for the nonempty regions `sign(k_lo + j) = s`
    of `[0, j_max]`; an undecided region refuses."""
    var out = List[List[Int]]()
    var cut = a_sub(aff(0, 0), k_lo)
    var regions = List[List[Int]]([List[Int]([-1, 0, 0, cut[0], cut[1] - 1]),
                                   List[Int]([0, cut[0], cut[1], cut[0], cut[1]]),
                                   List[Int]([1, cut[0], cut[1] + 1, j_max[0], j_max[1]])])
    for b in regions:
        var m = meet(List[List[Int]]([List[Int]([0, 0, j_max[0], j_max[1]]), List[Int]([b[1], b[2], b[3], b[4]])]), l0)
        if m[0] == -1:
            raise Error("UNDECIDED: sign region of k varies with l")
        if m[0] == 1:
            out.append([b[0], m[1], m[2], m[3], m[4]])
    return out^


def check_row_descent(ray: BRay, rows: List[List[Int]], sl: Dict[Int, List[Int]], pot: Dict[Int, Int],
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
            var st = Segment(ray, row[0], part_top)
            for part_bottom in range(3):
                var sb = Segment(ray, row[1], part_bottom)
                for u2 in range(-WINDOW + 1, WINDOW):
                    var e = Edge(ray, row, st, sb, u2)
                    for iv in child_intervals(rows, sl, e, l0):
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
                raise Error("NO DESCENT: a carrier piece has no covering decreasing child")
            cursor = aff(good[best][2], good[best][3] + 1)
            stats.descent_intervals += 1


def certify_ray_rows(ray: BRay, q0: Int, rows: List[List[Int]], potentials: List[List[Int]]) raises -> List[Int]:
    """Closure and descent for every member `q >= q0` of the ray, i.e. boundary
    hitting there. Raises on any undecided step, escape or missing descent."""
    ray.check()
    if q0 < 1 or q0 > 160:
        raise Error("class-B ray floor must satisfy 1<=q0<=160")
    if len(rows) == 0:
        raise Error("empty class-B carrier")
    var l0 = ray.l_of(q0)
    ray.check_domain(q0)
    check_line_identity(ray)
    check_bound(ray, q0)
    var sl = slices(rows)
    var pot = potential_table(potentials)
    var stats = Stats()
    check_seeds(ray, rows, sl, l0, q0, stats)
    for ri in range(len(rows)):
        stats.rows += 1
        check_row_members(ray, rows[ri], l0, q0, stats)
        check_row_closure(ray, rows, sl, ri, l0, q0, stats)
        check_row_descent(ray, rows, sl, pot, ri, l0, stats)
    print("CLASS_B_RAY_CERTIFICATE " + ray.name() + " q>=" + String(q0), "rows", stats.rows,
          "seeds_real", stats.seeds_real, "seeds_unreal", stats.seeds_unreal, "u_cases", stats.y_cases,
          "covered", stats.covered, "gap_geometry", stats.gap_geometry, "window_checks", stats.window_checks,
          "clip_fallbacks", stats.clip_fallbacks, "terminal_splits", stats.terminal_splits,
          "pieces", stats.pieces, "targets", stats.targets, "descent_intervals", stats.descent_intervals,
          "max_b", stats.max_potential_constant)
    return stats.as_list()


def expand(rows: List[List[Int]], l: Int) -> Dict[Int, Bool]:
    """Labels `(top, bottom, k, c, y)` of the carrier at `l`, keyed injectively
    within the finite replay budget."""
    var out = Dict[Int, Bool]()
    for row in rows:
        for k in range(row[4] * l + row[5], row[6] * l + row[7] + 1):
            var c = row[3] + 3 * k
            var y = row[2] - 6 * k - row[3]
            out[_label_key(row[0], row[1], k, c, y)] = True
    return out^


def _label_key(top: Int, bottom: Int, k: Int, c: Int, y: Int) -> Int:
    return (((top * 3 + bottom) * 4001 + k + 2000) * 16001 + c + 8000) * 32001 + y + 16000


def replay_finite(ray: BRay, q: Int, rows: List[List[Int]], potentials: List[List[Int]]) raises -> Int:
    """Differential replay at one member: the complete native seed graph has
    exactly the carrier's labels, and every non-target vertex has a native child
    of strictly smaller potential. Returns the vertex count."""
    var l = ray.l_of(q)
    var tables = build_seed_overlap_tables_screened(ray.member(q))
    var graph = build_seed_overlap_graph_from_tables(tables, 20000)
    if graph.capped:
        raise Error("STATE_BUDGET_EXHAUSTED: no finite replay verdict")
    var carrier = expand(rows, l)
    var pot = potential_table(potentials)
    var lm = length_matrix(tables)
    var xs = List[Int]()
    for v in graph.states:
        var w = offset_vector(lm, v.shift)
        if abs(w[0]) > 1999 or abs(w[1]) > 7999 or abs(w[2]) > 15999:
            raise Error("offset coordinate budget exhausted")
        if _label_key(v.top, v.bottom, w[0], w[1], w[2]) not in carrier:
            raise Error("native graph vertex outside the class-B carrier")
        var s = 1 if w[0] > 0 else (-1 if w[0] < 0 else 0)
        var b = _potential(pot, v.top, v.bottom, 3 * w[0] + w[1] + w[2], w[1] - 3 * w[0], s)
        if b < 0:
            raise Error("native graph vertex without a potential")
        xs.append(abs(w[0]) + b)
    if len(carrier) != graph.size():
        raise Error("class-B carrier and native graph label sets differ")
    for i in range(graph.size()):
        var w = offset_vector(lm, graph.states[i].shift)
        if w[0] == 0 and w[1] == 0 and w[2] == 0:
            continue
        var found = False
        for c in graph.adj[i]:
            if xs[c] < xs[i]:
                found = True
                break
        if not found:
            raise Error("native vertex without a strictly decreasing child")
    return graph.size()
