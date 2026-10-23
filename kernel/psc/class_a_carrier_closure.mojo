"""Uniform forward closure of a typed class-A carrier for every integer n>=n0 (#139).

The line data (images, run lengths, scaled lengths, the elimination of `n`)
are those of `psc.class_a_line.ALine`, one of the two gap-one lines
`(n+1,n,n+eps)`. The text below describes the plus line, whose carrier is
the 89-row typed candidate of `psc.class_a_typed_carrier` on
`x->xy^(n+1)x, c->cy^nx, y->xy^(n+1)c`; the minus line is the 104-row carrier
of `psc.class_a_minus_carrier`, with `L = (1+3h+h^2, 1+2h, 1+h)`,
`T = s(1+2h) + k h(1+h) - y h` and `n h(1+h) = 1+h-3h^2-h^3`. With
`h = 1/(beta-1)` the Perron root satisfies `P(n,h) = h^3+(n+1)(h^2+h)-1 = 0`,
so `n h(1+h) = 1-h-h^2-h^3` and `0 < h < 1/(n+1)`. In units scaled by `1+h`
the tile lengths are `L = (1+h+h^2, 1, 1+h)` and the bottom-minus-top
displacement of an integral offset `w=(k,c,y)` with `s=k+c+y` is
`T(w) = s + k h(1+h) + y h`; a state is a strict overlap iff
`-L_bottom < T < L_top`.

Every question below is the sign of `A(h) + n B(h)` with integer polynomials
`A, B`, equivalently of the integer polynomial `A(h) h(1+h) + (1-h-h^2-h^3) B(h)`,
on the whole interval `(0, 1/(n0+1)]`, which contains `h_n` for every `n>=n0`.
A sign is accepted only when an exact Sturm count finds no root in that
interval; an undecided sign raises. Row indices, run positions and interval
endpoints are affine in `n`, and an affine comparison is accepted only when
it holds for every integer `n>=n0`.

What is proved (for the stated `n0`): every carrier label is a strict
overlap; every real canonical swap seed is a carrier label; and every real
ordered child occurrence of every non-terminal carrier label is a carrier
label. Hence the complete seed graph `G_n` is contained in the carrier for
every `n>=n0`. This is containment, not label-set equality, and it says
nothing about hitting; the descent is `psc.class_a_carrier_descent`.
Source note: docs/class-a-carrier-closure-2026-10-22.md.
"""
from std.collections import Dict
from finite_exact.rat_q import Q
from finite_linear_algebra.qpoly import evaluate
from psc.exact import q_poly, q_sign
from psc.pisot import count_roots_in
from psc.class_a_typed_carrier import template_rows
from psc.class_a_line import ALine, plus_line


# ---------------------------------------------------------------------------
# Integer polynomials in h, ascending coefficients.
# ---------------------------------------------------------------------------

def pnorm(a: List[Int]) -> List[Int]:
    var out = a.copy()
    while len(out) > 0 and out[len(out) - 1] == 0:
        _ = out.pop()
    return out^


def padd(a: List[Int], b: List[Int]) -> List[Int]:
    var out = List[Int]()
    for i in range(max(len(a), len(b))):
        out.append((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0))
    return pnorm(out)


def pscale(a: List[Int], c: Int) -> List[Int]:
    var out = List[Int]()
    for x in a:
        out.append(c * x)
    return pnorm(out)


def psub(a: List[Int], b: List[Int]) -> List[Int]:
    return padd(a, pscale(b, -1))


def pmul(a: List[Int], b: List[Int]) -> List[Int]:
    if len(a) == 0 or len(b) == 0:
        return List[Int]()
    var out = List[Int]()
    for _ in range(len(a) + len(b) - 1):
        out.append(0)
    for i in range(len(a)):
        for j in range(len(b)):
            out[i + j] += a[i] * b[j]
    return pnorm(out)


def sign_on_interval(p: List[Int], q: Q) raises -> Int:
    """Sign of the integer polynomial `p` on `(0, q]`: `0` for the zero
    polynomial, else `+-1` when an exact Sturm count finds no root there.
    Factors of `h` are stripped first (they are positive on the interval)."""
    var f = pnorm(p)
    if len(f) == 0:
        return 0
    var start = 0
    while f[start] == 0:
        start += 1
    var g = List[Int]()
    for i in range(start, len(f)):
        g.append(f[i])
    var qp = q_poly(g)
    var at_q = q_sign(evaluate(qp, q))
    if at_q == 0:
        raise Error("UNDECIDED sign: polynomial vanishes at the interval bound")
    if count_roots_in(qp, Q.zero(), q) != 0:
        raise Error("UNDECIDED sign: root inside (0, q]")
    return at_q


# ---------------------------------------------------------------------------
# A(h) + n B(h), with n h(1+h) = line.elimination().
# ---------------------------------------------------------------------------

struct AffH(Copyable, Movable):
    var a: List[Int]
    var b: List[Int]

    def __init__(out self, a: List[Int], b: List[Int]):
        self.a = pnorm(a)
        self.b = pnorm(b)

    def add(self, o: AffH) -> AffH:
        return AffH(padd(self.a, o.a), padd(self.b, o.b))

    def sub(self, o: AffH) -> AffH:
        return AffH(psub(self.a, o.a), psub(self.b, o.b))

    def numerator(self, line: ALine) -> List[Int]:
        """`A h(1+h) + E B` with `E = n h(1+h)`, whose sign is the sign of `A + nB`."""
        return padd(pmul(self.a, [0, 1, 1]), pmul(line.elimination(), self.b))

    def sign(self, q: Q, line: ALine) raises -> Int:
        return sign_on_interval(self.numerator(line), q)

    def is_zero(self) -> Bool:
        return len(self.a) == 0 and len(self.b) == 0


def aff_times(line: ALine, coefficient: List[Int], poly: List[Int]) -> AffH:
    """`d (a l + b) * poly(h)` for the affine pair `coefficient = [a, b]` in `l`,
    as `A + n B` (`line.to_n`); for `d = 1` this is `(a n + b) * poly`."""
    var c = line.to_n(coefficient)
    return AffH(pscale(poly, c[1]), pscale(poly, c[0]))


def scaled_length(line: ALine, letter: Int) raises -> AffH:
    """`d L_letter`: every displacement and length carries the same factor `d > 0`."""
    return AffH(pscale(line.length(letter), line.d), [])


def displacement(line: ALine, s: List[Int], k: List[Int], y: List[Int]) raises -> AffH:
    """`d T`, `T = k L_x + c L_c + y L_y = s L_c + k (L_x-L_c) + y (L_y-L_c)` for
    affine `s, k, y` in `l`; on the gap-one plus line `T = s + k h(1+h) + y h`."""
    var lc = line.length(1)
    return (aff_times(line, s, lc).add(aff_times(line, k, psub(line.length(0), lc)))
            .add(aff_times(line, y, psub(line.length(2), lc))))


def perron_polynomial(line: ALine) -> AffH:
    """`P(n,h) = 1 - (n+eps) h - (n+d+1-eps) h^2 - d h^3` as `A + n B`."""
    return AffH([1, -line.eps, line.eps - line.d - 1, -line.d], [0, -1, -1])


def check_line_identity(line: ALine) raises:
    """`h (M^T L)_j - (1+h) L_j = -P(n,h)` for each letter `j`, coefficient-wise
    in `n` and `h`, where `M^T L = (2L_x + (n+d)L_y, L_x+L_c+nL_y,
    L_x+L_c+(n+eps)L_y)` is read off the images and `P = perron_polynomial(line)`.
    Also checks that `line.elimination()` is `n h(1+h)` solved from `P = 0`."""
    line.check()
    var lx = line.length(0)
    var lc = line.length(1)
    var ly = line.length(2)
    var p = perron_polynomial(line)
    var mt = List[AffH]()
    mt.append(AffH(padd(pscale(lx, 2), pscale(ly, line.d)), ly))
    mt.append(AffH(padd(lx, lc), ly))
    mt.append(AffH(padd(padd(lx, lc), pscale(ly, line.eps)), ly))
    var ls = List[List[Int]]([lx.copy(), lc.copy(), ly.copy()])
    for j in range(3):
        var lhs = AffH(pmul(mt[j].a, [0, 1]), pmul(mt[j].b, [0, 1])).sub(AffH(pmul(ls[j], [1, 1]), []))
        if not lhs.add(p).is_zero():
            raise Error("scaled lengths are not the left Perron eigenvector of the line")
    if len(psub(line.elimination(), p.a)) != 0 or len(padd(p.b, [0, 1, 1])) != 0:
        raise Error("elimination identity disagrees with the Perron polynomial")


def check_bound(line: ALine, n0: Int, q: Q) raises:
    """`P(n0, q) < 0`; since `P(n, q)` decreases in `n`, `P(n, 0) = 1` and
    `P(n, .)` decreases on `h > 0`, the root `h_n` lies in `(0, q)` for all `n >= n0`."""
    var p = perron_polynomial(line)
    if q_sign(evaluate(q_poly(padd(p.a, pscale(p.b, n0))), q)) >= 0:
        raise Error("interval bound does not contain the Perron parameter h_n")


# ---------------------------------------------------------------------------
# Affine integers a l + b on the integer ray l >= l0 (the parameter `n0` of
# the comparisons below is that ray floor; `l = n` when `d = 1`).
# ---------------------------------------------------------------------------

def aff(a: Int, b: Int) -> List[Int]:
    return [a, b]


def a_add(u: List[Int], v: List[Int]) -> List[Int]:
    return [u[0] + v[0], u[1] + v[1]]


def a_sub(u: List[Int], v: List[Int]) -> List[Int]:
    return [u[0] - v[0], u[1] - v[1]]


def a_le(u: List[Int], v: List[Int], n0: Int) -> Int:
    """`1` if `u <= v` for every integer `n >= n0`, `0` if `u > v` for every
    such `n`, `-1` when the order changes on the ray."""
    if u[0] <= v[0] and u[0] * n0 + u[1] <= v[0] * n0 + v[1]:
        return 1
    if u[0] >= v[0] and u[0] * n0 + u[1] > v[0] * n0 + v[1]:
        return 0
    return -1


def a_div_ceil(u: List[Int], d: Int) raises -> List[Int]:
    """`ceil(u / d)` for an affine `u` whose slope is a multiple of `d`."""
    if u[0] % d != 0:
        raise Error("affine slope not divisible by the gap")
    var q = u[1] // d
    return [u[0] // d, q + (1 if q * d < u[1] else 0)]


def a_div_floor(u: List[Int], d: Int) raises -> List[Int]:
    """`floor(u / d)` for an affine `u` whose slope is a multiple of `d`."""
    if u[0] % d != 0:
        raise Error("affine slope not divisible by the gap")
    return [u[0] // d, u[1] // d]


def a_max(u: List[Int], v: List[Int], n0: Int) raises -> List[Int]:
    if a_le(u, v, n0) == 1:
        return v.copy()
    if a_le(v, u, n0) == 1:
        return u.copy()
    raise Error("UNDECIDED affine maximum on the ray")


def a_min(u: List[Int], v: List[Int], n0: Int) raises -> List[Int]:
    if a_le(u, v, n0) == 1:
        return u.copy()
    if a_le(v, u, n0) == 1:
        return v.copy()
    raise Error("UNDECIDED affine minimum on the ray")


# ---------------------------------------------------------------------------
# Substitution data: images x->x y^(n+1) x, c->c y^n x, y->x y^(n+eps) c.
# ---------------------------------------------------------------------------

def first_letter(letter: Int) -> Int:
    return 1 if letter == 1 else 0


def last_letter(letter: Int) -> Int:
    return 1 if letter == 2 else 0




struct Segment(Copyable, Movable):
    """One of the three proper-prefix segments FIRST (part 0, empty prefix),
    RUN (part 1, prefix = first letter then m copies of y, 0<=m<=run-1) and
    LAST (part 2, prefix = first letter then the whole run)."""
    var child: Int
    var px: Int
    var pc: Int
    var m_lo: List[Int]
    var m_hi: List[Int]

    def __init__(out self, line: ALine, letter: Int, part: Int) raises:
        if letter < 0 or letter > 2 or part < 0 or part > 2:
            raise Error("invalid segment")
        if part == 0:
            self.child = first_letter(letter)
            self.px = 0
            self.pc = 0
            self.m_lo = aff(0, 0)
            self.m_hi = aff(0, 0)
            return
        self.px = 1 if first_letter(letter) == 0 else 0
        self.pc = 1 - self.px
        var run = line.run(letter)
        if part == 1:
            self.child = 2
            self.m_lo = aff(0, 0)
            self.m_hi = a_sub(run, aff(0, 1))
        else:
            self.child = last_letter(letter)
            self.m_lo = run.copy()
            self.m_hi = run.copy()


def slice_key(top: Int, bottom: Int, s: Int, y: Int) raises -> Int:
    if top < 0 or top > 2 or bottom < 0 or bottom > 2 or s < -16 or s > 16 or y < -16 or y > 16:
        raise Error("slice key outside the typed range")
    return ((top * 3 + bottom) * 33 + (s + 16)) * 33 + (y + 16)


def slices(rows: List[List[Int]]) raises -> Dict[Int, List[Int]]:
    var out = Dict[Int, List[Int]]()
    for i in range(len(rows)):
        var row = rows[i].copy()
        if len(row) != 8:
            raise Error("malformed typed carrier row")
        var key = slice_key(row[0], row[1], row[2], row[3])
        if key not in out:
            out[key] = List[Int]()
        out[key].append(i)
    return out^


struct ClosureStats(Copyable, Movable):
    var rows: Int
    var member_checks: Int
    var segments: Int
    var y_cases: Int
    var covered: Int
    var gap_geometry: Int
    var window_checks: Int
    var seeds_real: Int
    var seeds_unreal: Int
    var clip_fallbacks: Int
    var terminal_splits: Int

    def __init__(out self):
        self.rows = 0
        self.member_checks = 0
        self.segments = 0
        self.y_cases = 0
        self.covered = 0
        self.gap_geometry = 0
        self.window_checks = 0
        self.seeds_real = 0
        self.seeds_unreal = 0
        self.clip_fallbacks = 0
        self.terminal_splits = 0

    def as_list(self) -> List[Int]:
        return [self.rows, self.member_checks, self.segments, self.y_cases, self.covered,
                self.gap_geometry, self.window_checks, self.seeds_real, self.seeds_unreal,
                self.clip_fallbacks, self.terminal_splits]


def strict_inside(line: ALine, top: Int, bottom: Int, t: AffH, q: Q) raises -> Bool:
    return scaled_length(line, top).sub(t).sign(q, line) > 0 and t.add(scaled_length(line, bottom)).sign(q, line) > 0


def _unreal_on(line: ALine, top: Int, bottom: Int, s2: Int, k0: List[Int], y2: Int,
               j_lo: List[Int], j_hi: List[Int], q: Q) raises -> Bool:
    """The child `(top,bottom)` with sum `s2`, `k' = k0 + j`, `y' = y2` is not
    a strict overlap for any `j` in `[j_lo, j_hi]`: its displacement is
    affine increasing in `j`, so it suffices that it is at or beyond the
    right boundary at `j_lo`, or at or before the left boundary at `j_hi`."""
    var t_hi = displacement(line, aff(0, s2), a_add(k0, j_hi), aff(0, y2))
    if t_hi.add(scaled_length(line, bottom)).sign(q, line) <= 0:
        return True
    var t_lo = displacement(line, aff(0, s2), a_add(k0, j_lo), aff(0, y2))
    if scaled_length(line, top).sub(t_lo).sign(q, line) <= 0:
        return True
    return False


def check_seeds(line: ALine, rows: List[List[Int]], sl: Dict[Int, List[Int]], n0: Int, q: Q,
                mut stats: ClosureStats) raises:
    """The twelve candidate seed overlaps of the three oriented swap pairs:
    `(a,b,0)`, `(a,a,e_b)`, `(b,b,-e_a)`, `(b,a,e_b-e_a)`. Each is either a
    strict overlap for every `n>=n0`, then it must be a carrier label, or
    not one for any such `n`."""
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
                var t = displacement(line, aff(0, s), aff(0, w[0]), aff(0, w[2]))
                if strict_inside(line, top, bottom, t, q):
                    stats.seeds_real += 1
                    var found = False
                    var key = slice_key(top, bottom, s, w[2])
                    if key in sl:
                        for i in sl[key]:
                            var row = rows[i].copy()
                            if a_le(aff(row[4], row[5]), aff(0, w[0]), n0) == 1 and a_le(aff(0, w[0]), aff(row[6], row[7]), n0) == 1:
                                found = True
                    if not found:
                        raise Error("real swap seed omitted from the typed carrier")
                else:
                    # Not strict for every n>=n0: both margins were decided, so
                    # one of them is <= 0 on the whole interval.
                    stats.seeds_unreal += 1


def check_row_members(line: ALine, row: List[Int], n0: Int, q: Q, mut stats: ClosureStats) raises:
    var lo = aff(row[4], row[5])
    var hi = aff(row[6], row[7])
    if a_le(lo, hi, n0) != 1:
        raise Error("typed carrier row is empty for some n>=n0")
    var ends = List[List[Int]]([lo.copy(), hi.copy()])
    for k in ends:
        var t = displacement(line, aff(0, row[2]), k, aff(0, row[3]))
        if not strict_inside(line, row[0], row[1], t, q):
            raise Error("typed carrier row member is not a strict overlap")
        stats.member_checks += 1


def check_row_closure(line: ALine, rows: List[List[Int]], sl: Dict[Int, List[Int]], ri: Int,
                      n0: Int, q: Q, window: Int, mut stats: ClosureStats) raises:
    var row = rows[ri].copy()
    var top = row[0]
    var bottom = row[1]
    var s = row[2]
    var y = row[3]
    var k_lo = aff(row[4], row[5])
    var j_max = a_sub(aff(row[6], row[7]), k_lo)   # j ranges over [0, j_max]
    var zero = aff(0, 0)
    # The equal-letter zero-offset coincidence is terminal and has no children.
    var has_terminal = False
    var terminal = aff(0, 0)
    if top == bottom and s == 0 and y == 0 and a_le(k_lo, zero, n0) == 1 and a_le(zero, aff(row[6], row[7]), n0) == 1:
        has_terminal = True
        terminal = aff(-row[4], -row[5])
    for part_top in range(3):
        var seg_top = Segment(line, top, part_top)
        for part_bottom in range(3):
            var seg_bottom = Segment(line, bottom, part_bottom)
            stats.segments += 1
            var dx = seg_bottom.px - seg_top.px
            var dc = seg_bottom.pc - seg_top.pc
            var child_top = seg_top.child
            var child_bottom = seg_bottom.child
            # k' = k + s + dx = k_lo + s + dx + j ;
            # y' = d k + n s + eps y + (m_b - m_t) = base + d j + (m_b - m_t), n = d l + r
            var k0 = a_add(k_lo, aff(0, s + dx))
            var base = aff(line.d * (row[4] + s), line.d * row[5] + line.r * s + line.eps * y)
            var d_lo = a_sub(seg_bottom.m_lo, seg_top.m_hi)
            var d_hi = a_sub(seg_bottom.m_hi, seg_top.m_lo)
            # Window edges: at y' = +window the child is at or beyond the right
            # boundary for every j, at y' = -window at or before the left one;
            # the displacement is increasing in y', so larger |y'| is unreal.
            for sign in range(2):
                var yw = window if sign == 0 else -window
                var s2 = 2 * s + dx + dc + yw
                var t0 = displacement(line, aff(0, s2), k0, aff(0, yw))
                var tj = displacement(line, aff(0, s2), a_add(k0, j_max), aff(0, yw))
                if yw > 0:
                    if scaled_length(line, child_top).sub(t0).sign(q, line) > 0 or scaled_length(line, child_top).sub(tj).sign(q, line) > 0:
                        raise Error("child window edge is a strict overlap")
                else:
                    if t0.add(scaled_length(line, child_bottom)).sign(q, line) > 0 or tj.add(scaled_length(line, child_bottom)).sign(q, line) > 0:
                        raise Error("child window edge is a strict overlap")
                stats.window_checks += 1
            for y2 in range(-window + 1, window):
                var s2 = 2 * s + dx + dc + y2
                stats.y_cases += 1
                # Realizable j: y2 - base - d j in [d_lo, d_hi].
                var r_lo = a_div_ceil(a_sub(a_sub(aff(0, y2), base), d_hi), line.d)
                var r_hi = a_div_floor(a_sub(a_sub(aff(0, y2), base), d_lo), line.d)
                var lo = zero.copy()
                var hi = j_max.copy()
                if a_le(r_lo, zero, n0) == 1:
                    lo = zero.copy()
                elif a_le(zero, r_lo, n0) == 1:
                    lo = r_lo.copy()
                else:
                    stats.clip_fallbacks += 1
                if a_le(j_max, r_hi, n0) == 1:
                    hi = j_max.copy()
                elif a_le(r_hi, j_max, n0) == 1:
                    hi = r_hi.copy()
                else:
                    stats.clip_fallbacks += 1
                if a_le(lo, hi, n0) == 0:
                    continue
                # Target rows of the child slice, as j-intervals.
                var ivs = List[List[Int]]()   # [lo_a, lo_b, hi_a, hi_b]
                var key = slice_key(child_top, child_bottom, s2, y2)
                if key in sl:
                    for i in sl[key]:
                        var target = rows[i].copy()
                        var t_lo = a_sub(aff(target[4], target[5]), k0)
                        var t_hi = a_sub(aff(target[6], target[7]), k0)
                        ivs.append([t_lo[0], t_lo[1], t_hi[0], t_hi[1]])
                # Insertion sort by the lower endpoint at n0; the order must be uniform.
                for i in range(1, len(ivs)):
                    var m = i
                    while m > 0 and ivs[m][0] * n0 + ivs[m][1] < ivs[m - 1][0] * n0 + ivs[m - 1][1]:
                        var tmp = ivs[m].copy()
                        ivs[m] = ivs[m - 1].copy()
                        ivs[m - 1] = tmp^
                        m -= 1
                for i in range(1, len(ivs)):
                    if a_le(aff(ivs[i - 1][2], ivs[i - 1][3] + 1), aff(ivs[i][0], ivs[i][1]), n0) != 1:
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
                        var inside = a_le(g_lo, terminal, n0) == 1 and a_le(terminal, g_hi, n0) == 1
                        var outside = a_le(terminal, a_sub(g_lo, aff(0, 1)), n0) == 1 or a_le(a_add(g_hi, aff(0, 1)), terminal, n0) == 1
                        if inside:
                            split.append([g[0], g[1], terminal[0], terminal[1] - 1])
                            split.append([terminal[0], terminal[1] + 1, g[2], g[3]])
                            stats.terminal_splits += 1
                        elif outside:
                            split.append(g.copy())
                        else:
                            raise Error("UNDECIDED: terminal membership in a gap varies with n")
                    gaps = split^
                for g in gaps:
                    var g_lo = a_max(aff(g[0], g[1]), lo, n0)
                    var g_hi = a_min(aff(g[2], g[3]), hi, n0)
                    if a_le(g_lo, g_hi, n0) == 0:
                        continue
                    if _unreal_on(line, child_top, child_bottom, s2, k0, y2, g_lo, g_hi, q):
                        stats.gap_geometry += 1
                    else:
                        raise Error("ESCAPE: a real ordered child leaves the typed carrier")
                stats.covered += 1


def certify_closure_line(line: ALine, n0: Int, rows: List[List[Int]], window: Int = 6) raises -> List[Int]:
    """Prove, for every integer n>=n0 on the residue ray of `line`, that the
    typed carrier (rows affine in `l`, `n = d l + r`) is a strict forward-closed
    superset of the complete seed graph. Raises on any undecided sign or
    comparison and on any escaping child."""
    if n0 < 4 or n0 > 160:
        raise Error("uniform closure floor must satisfy 4<=n0<=160")
    if window < 3 or window > 12:
        raise Error("child y-window outside the declared range")
    if len(rows) == 0:
        raise Error("empty typed carrier")
    check_line_identity(line)
    var l0 = ray_floor(line, n0)
    var n_min = line.n_of(l0)
    line.check_domain(n_min)
    var q = line.bound(n_min)
    check_bound(line, n_min, q)
    var sl = slices(rows)
    var stats = ClosureStats()
    check_seeds(line, rows, sl, l0, q, stats)
    for ri in range(len(rows)):
        stats.rows += 1
        check_row_members(line, rows[ri], l0, q, stats)
        check_row_closure(line, rows, sl, ri, l0, q, window, stats)
    var tag = "" if line.eps == 1 and line.d == 1 else " line=" + line.name()
    print("CLASS_A_CARRIER_CLOSURE n>=" + String(n_min) + tag, "rows", stats.rows, "segments", stats.segments,
          "y_cases", stats.y_cases, "covered", stats.covered, "gap_geometry", stats.gap_geometry,
          "window_checks", stats.window_checks, "seeds_real", stats.seeds_real,
          "seeds_unreal", stats.seeds_unreal, "clip_fallbacks", stats.clip_fallbacks,
          "terminal_splits", stats.terminal_splits)
    return stats.as_list()


def ray_floor(line: ALine, n0: Int) -> Int:
    """Least `l` with `d l + r >= n0`."""
    var l0 = 0
    while line.n_of(l0) < n0:
        l0 += 1
    return l0


def certify_closure_rows(n0: Int, rows: List[List[Int]], window: Int = 6) raises -> List[Int]:
    return certify_closure_line(plus_line(), n0, rows, window)


def certify_closure(n0: Int = 5, window: Int = 6) raises -> List[Int]:
    return certify_closure_rows(n0, template_rows(), window)
