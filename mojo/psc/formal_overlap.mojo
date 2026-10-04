"""Formal (potential) overlap graph, compared with the realized seed-patch graph.

A *potential overlap* is a state `(i, j, t)` of `psc.overlap_seed_patch` with
`t = sum_a w_a l_a`, `w in Z^3`, not required to be reachable from any seed.
The *formal overlap graph* `F_sigma` is the inflation closure of every
potential overlap in a box `|w_a| <= R_a`; the *realized graph* `R_sigma` is
the swap-seed closure. A *formal carrier* is a recurrent SCC of `F_sigma` with
its coincidence vertices deleted: the maximal set carrying coincidence-free
(producer-free) cycles. This is the sound object behind the ledger's
"formal producer-free cycles" (`docs/completion-ledger-2026-09-11.md` §V),
whose original instrument is not in the repository; a carrier, not a simple
cycle, is counted, because the number of simple cycles is not canonical.

Box completeness. Inflation sends `t` to `beta t + c` with `c` a difference
of two prefix positions. For a contracting conjugate `z` with
`D_z = max_c |c(z)|` and `T_z = D_z / (1 - |z|)`, a state with
`|t(z)| > T_z` has a child with `|t'(z)| < |t(z)|`, and a state with
`|t(z)| <= T_z` has every child with `|t'(z)| <= T_z`. Around a cycle the
value cannot strictly decrease and come back, so every cycle state has
`|t(z)| <= T_z` for every contracting `z`, and `|t(beta)| < l_max` by
interior overlap. The region `K+ = {|t(z)| <= T_z (1 + eps)}` is forward
closed (`|z| T_z (1 + eps) + D_z <= T_z (1 + eps)`), so seeding only from
`K+` loses no carrier and no path from a carrier to a coincidence. `K+` is
enumerated inside a `w`-box whose radii over-approximate it and are then
doubled. Floating point only chooses which exact states seed the closure:
`eps = 1e-6` exceeds the float error by orders of magnitude, so every state
of `K` is seeded. Every predicate (overlap, child,
coincidence, SCC, depth, realization) is exact. `carriers_inside_box`
records the a-posteriori receipt that every carrier vertex is a box seed.

A carrier is either wholly realized or wholly unrealized: the realized graph
is forward closed and a carrier is strongly connected. That is checked, and
the realized carriers are cross-checked against the realized graph's own
carriers. Capped graphs fail closed. Independent oracle:
src/psc_research/formal_overlap.py.
"""

from std.math import sqrt

from psc.overlap_obstruction import overlap_sccs
from psc.overlap_seed_patch import (
    OverlapState,
    SeedOverlapAutomaton,
    SeedOverlapTables,
    build_overlap_graph_from_seeds,
    build_seed_overlap_graph_from_tables,
    first_coincidence_depths,
    interior_overlap_cached,
)
from psc.perron_field3 import CubicElt, cubic_add_checked, cubic_sub_checked


comptime FORMAL_STATE_CAP = 400000
comptime BOX_SLACK = 2.0
comptime REGION_TOLERANCE = 1.0e-6


struct ContractionBox(Copyable, Movable):
    """The `w`-box radii and, per contracting conjugate `z = re + i im`, the
    threshold `T_z = D_z / (1 - |z|)` of the forward-closed region."""

    var radii: List[Int]
    var roots_re: List[Float64]
    var roots_im: List[Float64]
    var thresholds: List[Float64]

    def __init__(
        out self,
        var radii: List[Int],
        var roots_re: List[Float64],
        var roots_im: List[Float64],
        var thresholds: List[Float64],
    ):
        self.radii = radii^
        self.roots_re = roots_re^
        self.roots_im = roots_im^
        self.thresholds = thresholds^

    def in_region(self, t: CubicElt) -> Bool:
        """`|t(z)| <= T_z (1 + REGION_TOLERANCE)` for every contracting `z`."""
        for k in range(len(self.roots_re)):
            var v = _value(t, self.roots_re[k], self.roots_im[k])
            var bound = self.thresholds[k] * (1.0 + REGION_TOLERANCE)
            if v[0] * v[0] + v[1] * v[1] > bound * bound:
                return False
        return True


struct FormalCarrier(Copyable, Movable):
    """One recurrent coincidence-free SCC of the formal overlap graph."""

    var members: List[Int]
    var internal_edges: Int
    var realized: Bool
    var closed: Bool
    var aligned: Bool
    var direct_producer: Bool
    var death_depth: Int

    def __init__(
        out self,
        var members: List[Int],
        internal_edges: Int,
        realized: Bool,
        closed: Bool,
        aligned: Bool,
        direct_producer: Bool,
        death_depth: Int,
    ):
        self.members = members^
        self.internal_edges = internal_edges
        self.realized = realized
        self.closed = closed
        self.aligned = aligned
        self.direct_producer = direct_producer
        self.death_depth = death_depth

    def size(self) -> Int:
        return len(self.members)

    def cyclomatic(self) -> Int:
        """`|E| - |V| + 1`: the rank of the carrier's cycle space."""
        return self.internal_edges - len(self.members) + 1


struct FormalSurvey(Copyable, Movable):
    """The formal graph, the realized graph and the formal carriers."""

    var formal: SeedOverlapAutomaton
    var realized_states: Int
    var box: List[Int]
    var seeds: Int
    var nonproductive: Int
    var carriers: List[FormalCarrier]
    var carriers_inside_box: Bool

    def __init__(
        out self,
        var formal: SeedOverlapAutomaton,
        realized_states: Int,
        var box: List[Int],
        seeds: Int,
        nonproductive: Int,
        var carriers: List[FormalCarrier],
        carriers_inside_box: Bool,
    ):
        self.formal = formal^
        self.realized_states = realized_states
        self.box = box^
        self.seeds = seeds
        self.nonproductive = nonproductive
        self.carriers = carriers^
        self.carriers_inside_box = carriers_inside_box


# ---- floating-point box radii ------------------------------------------------


def _chi(field_coeffs: List[Int], x: Float64) -> Float64:
    return ((x + Float64(field_coeffs[2])) * x + Float64(field_coeffs[1])) * x + Float64(
        field_coeffs[0]
    )


def _perron_root(coeffs: List[Int]) -> Float64:
    """Largest real root of `x^3 + c2 x^2 + c1 x + c0` by bisection."""
    var hi = 2.0 + Float64(abs(coeffs[0]) + abs(coeffs[1]) + abs(coeffs[2]))
    var lo = 1.0
    for _ in range(200):
        var mid = (lo + hi) / 2.0
        if _chi(coeffs, mid) > 0.0:
            hi = mid
        else:
            lo = mid
    return (lo + hi) / 2.0


def _value(x: CubicElt, re: Float64, im: Float64) -> Tuple[Float64, Float64]:
    """`x(z)` for `z = re + i im`, as `(Re, Im)`."""
    var z2re = re * re - im * im
    var z2im = 2.0 * re * im
    return (
        Float64(x.a0) + Float64(x.a1) * re + Float64(x.a2) * z2re,
        Float64(x.a1) * im + Float64(x.a2) * z2im,
    )


def _det3(m: List[List[Float64]]) -> Float64:
    return (
        m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
        - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
        + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0])
    )


def _others(i: Int) -> Tuple[Int, Int]:
    if i == 0:
        return (1, 2)
    if i == 1:
        return (0, 2)
    return (0, 1)


def _inverse3(m: List[List[Float64]]) raises -> List[List[Float64]]:
    """Adjugate over determinant: `inv[r][c] = (-1)^(r+c) minor(c, r) / det`."""
    var d = _det3(m)
    if d == 0.0:
        raise Error("formal box: singular embedding matrix")
    var out = List[List[Float64]]()
    for r in range(3):
        var row = List[Float64]()
        for c in range(3):
            var rs = _others(c)
            var cs = _others(r)
            var minor = m[rs[0]][cs[0]] * m[rs[1]][cs[1]] - m[rs[0]][cs[1]] * m[rs[1]][cs[0]]
            var sign = 1.0 if (r + c) % 2 == 0 else -1.0
            row.append(sign * minor / d)
        out.append(row^)
    return out^


def formal_box(tables: SeedOverlapTables) raises -> ContractionBox:
    """The contraction region and a `w`-box containing it."""
    var coeffs = tables.field.charpoly()
    var beta = _perron_root(coeffs)
    # chi(x) = (x - beta)(x^2 + p x + q)
    var p = Float64(coeffs[2]) + beta
    var q = -Float64(coeffs[0]) / beta
    var disc = p * p - 4.0 * q
    var roots_re = List[Float64]()
    var roots_im = List[Float64]()
    if disc < 0.0:
        roots_re.append(-p / 2.0)
        roots_im.append(sqrt(-disc) / 2.0)
    else:
        roots_re.append((-p + sqrt(disc)) / 2.0)
        roots_re.append((-p - sqrt(disc)) / 2.0)
        roots_im.append(0.0)
        roots_im.append(0.0)

    var digits = List[CubicElt]()
    for i in range(3):
        for j in range(3):
            for a in range(len(tables.sigma[i])):
                for b in range(len(tables.sigma[j])):
                    digits.append(cubic_sub_checked(tables.prefix(j, b), tables.prefix(i, a)))

    var rows = List[List[Float64]]()
    var bounds = List[Float64]()
    var thresholds = List[Float64]()
    var perron_row = List[Float64]()
    var lmax = 0.0
    for a in range(3):
        var v = _value(tables.lengths.at(a), beta, 0.0)[0]
        perron_row.append(v)
        lmax = max(lmax, v)
    rows.append(perron_row^)
    bounds.append(lmax)
    for k in range(len(roots_re)):
        var re = roots_re[k]
        var im = roots_im[k]
        var modulus = sqrt(re * re + im * im)
        if modulus >= 1.0:
            raise Error("formal box: conjugate is not contracting")
        var dmax = 0.0
        for d in range(len(digits)):
            var v = _value(digits[d], re, im)
            dmax = max(dmax, sqrt(v[0] * v[0] + v[1] * v[1]))
        var threshold = dmax / (1.0 - modulus)
        thresholds.append(threshold)
        var re_row = List[Float64]()
        var im_row = List[Float64]()
        for a in range(3):
            var v = _value(tables.lengths.at(a), re, im)
            re_row.append(v[0])
            im_row.append(v[1])
        rows.append(re_row^)
        bounds.append(threshold)
        if im != 0.0:
            rows.append(im_row^)
            bounds.append(threshold)
    var inv = _inverse3(rows)
    var radii = List[Int]()
    for a in range(3):
        var r = 0.0
        for k in range(3):
            r += abs(inv[a][k]) * bounds[k]
        radii.append(Int(BOX_SLACK * r) + 1)
    return ContractionBox(radii^, roots_re^, roots_im^, thresholds^)


# ---- exact construction -------------------------------------------------------


def _scaled(x: CubicElt, n: Int) raises -> CubicElt:
    var out = CubicElt()
    var step = x if n >= 0 else -x
    for _ in range(abs(n)):
        out = cubic_add_checked(out, step)
    return out


def formal_seed_states(
    tables: SeedOverlapTables, region: ContractionBox, mut sign_cache: Dict[CubicElt, Int]
) raises -> List[OverlapState]:
    """Every potential overlap `(i, j, sum_a w_a l_a)` with `|w_a| <= R_a` and
    `t` in the contraction region."""
    ref box = region.radii
    var out = List[OverlapState]()
    for w0 in range(-box[0], box[0] + 1):
        var t0 = _scaled(tables.lengths.at(0), w0)
        for w1 in range(-box[1], box[1] + 1):
            var t1 = cubic_add_checked(t0, _scaled(tables.lengths.at(1), w1))
            for w2 in range(-box[2], box[2] + 1):
                var t = cubic_add_checked(t1, _scaled(tables.lengths.at(2), w2))
                if not region.in_region(t):
                    continue
                for top in range(3):
                    for bottom in range(3):
                        var s = OverlapState(top, bottom, t)
                        if interior_overlap_cached(tables, sign_cache, s):
                            out.append(s)
    return out^


def _coincidence_free(a: SeedOverlapAutomaton) -> SeedOverlapAutomaton:
    """The same vertices with every edge into or out of a coincidence removed."""
    var adj = List[List[Int]]()
    for v in range(a.size()):
        var row = List[Int]()
        if not a.states[v].is_coincidence():
            for k in range(len(a.adj[v])):
                var w = a.adj[v][k]
                if not a.states[w].is_coincidence():
                    row.append(w)
        adj.append(row^)
    return SeedOverlapAutomaton(a.states, adj, a.capped)


def recurrent_coincidence_free_sccs(a: SeedOverlapAutomaton) raises -> List[List[Int]]:
    """SCCs of the coincidence-free subgraph that carry a cycle."""
    var free = _coincidence_free(a)
    var all = overlap_sccs(free)
    var out = List[List[Int]]()
    for k in range(len(all)):
        ref comp = all[k]
        var cyclic = len(comp) > 1
        if len(comp) == 1:
            var v = comp[0]
            for j in range(len(free.adj[v])):
                cyclic = cyclic or free.adj[v][j] == v
        if cyclic:
            out.append(comp.copy())
    return out^


def survey_formal_overlaps(
    tables: SeedOverlapTables, max_states: Int = FORMAL_STATE_CAP
) raises -> FormalSurvey:
    var cache = Dict[CubicElt, Int]()
    var region = formal_box(tables)
    var box = region.radii.copy()
    var seeds = formal_seed_states(tables, region, cache)
    var formal = build_overlap_graph_from_seeds(tables, seeds, cache, max_states)
    if formal.capped:
        raise Error("formal overlap graph capped: no verdict")
    var realized = build_seed_overlap_graph_from_tables(tables)
    if realized.capped:
        raise Error("realized overlap graph capped: no verdict")

    var in_realized = Dict[OverlapState, Bool]()
    for v in range(realized.size()):
        in_realized[realized.states[v]] = True
    var in_seeds = Dict[OverlapState, Bool]()
    for s in range(len(seeds)):
        in_seeds[seeds[s]] = True

    var depth = first_coincidence_depths(formal)
    var nonproductive = 0
    for v in range(formal.size()):
        if depth[v] < 0:
            nonproductive += 1

    var comps = recurrent_coincidence_free_sccs(formal)
    var member = List[Int](length=formal.size(), fill=-1)
    for k in range(len(comps)):
        for i in range(len(comps[k])):
            member[comps[k][i]] = k

    var inside = True
    var carriers = List[FormalCarrier]()
    var realized_count = 0
    for k in range(len(comps)):
        ref comp = comps[k]
        var n_real = 0
        var internal = 0
        var closed = True
        var aligned = False
        var direct = False
        var death = -1
        for i in range(len(comp)):
            var v = comp[i]
            var s = formal.states[v]
            if s in in_realized:
                n_real += 1
            inside = inside and s in in_seeds
            aligned = aligned or s.shift.is_zero()
            if death < 0 or (depth[v] >= 0 and depth[v] < death):
                death = depth[v]
            for j in range(len(formal.adj[v])):
                var w = formal.adj[v][j]
                if member[w] == k:
                    internal += 1
                else:
                    closed = False
                    direct = direct or formal.states[w].is_coincidence()
        if n_real != 0 and n_real != len(comp):
            raise Error("formal carrier is partly realized: realized graph not forward closed")
        if n_real > 0:
            realized_count += 1
        carriers.append(
            FormalCarrier(comp.copy(), internal, n_real > 0, closed, aligned, direct, death)
        )

    var realized_comps = recurrent_coincidence_free_sccs(realized)
    if len(realized_comps) != realized_count:
        raise Error("realized carriers disagree with the realized formal carriers")

    return FormalSurvey(
        formal^, realized.size(), box^, len(seeds), nonproductive, carriers^, inside
    )
