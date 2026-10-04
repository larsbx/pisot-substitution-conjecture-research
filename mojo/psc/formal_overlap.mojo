"""Formal (potential) overlap graph, compared with the realized seed-patch graph.

A *potential overlap* is a state `(i, j, t)` of `psc.overlap_seed_patch` with
`t = sum_a w_a l_a`, `w in Z^3`, not required to be reachable from any seed.
The *formal overlap graph* `F_sigma` is the inflation closure of every
potential overlap in a contraction region; the *realized graph* `R_sigma` is
the swap-seed closure. A *formal carrier* is a recurrent SCC of `F_sigma` with
its coincidence vertices deleted: the maximal set carrying coincidence-free
(producer-free) cycles. This is the sound object behind the ledger's
"formal producer-free cycles" (`docs/completion-ledger-2026-09-11.md` §V),
whose original instrument is not in the repository; a carrier, not a simple
cycle, is counted, because the number of simple cycles is not canonical.

Contraction region. Write `q(t) = sum_k |sigma_k(t)|^2` over the two
contracting embeddings; it is exact in `Q(beta)`: `Tr(t^2) - t^2` for a real
pair, `2 N(t) / t` for a complex pair. Inflation sends `t` to `beta t + c`, `c`
a difference of two prefix positions, so on the contracting coordinates
`sqrt q(t') <= rho sqrt q(t) + sqrt q(c)`, `rho` the largest contracting
modulus. For any rational `T >= max_c sqrt q(c) / (1 - rho)` the region
`K_T = {q(t) <= T^2}` is therefore forward closed, and every state of a cycle
lies in it (outside `K_T` the value strictly decreases and cannot return).
Seeding the closure from the genuine overlaps of `K_T` loses no carrier and no
path from a carrier to a coincidence.

Everything is exact. `rho`, `max_c q(c)` and `T = A / 64` are rational upper
bounds from Sturm isolation and the cached Perron enclosure; membership in
`K_T` is one exact sign at the Perron root. The enumeration box comes from the
trace-dual basis: `w_a = Tr(t l*_a)`, so Cauchy--Schwarz over the contracting
embeddings gives `|w_a| <= l_max |l*_a(beta)| + T sqrt q(l*_a)`.
`carriers_inside_box` records the a-posteriori receipt that every carrier
vertex is a seed.

A carrier is either wholly realized or wholly unrealized: the realized graph
is forward closed and a carrier is strongly connected. That is checked, and
the realized carriers are cross-checked against the realized graph's own
carriers. Capped graphs and unrefinable bounds fail closed. Independent
oracle: src/psc_research/formal_overlap.py.
"""

from finite_exact.closed_interval import IQ
from finite_exact.rat_q import Q, q_abs, q_max, q_min

from psc.exact import contains_zero, q_poly, require_q
from psc.overlap_contracting import discriminant
from psc.overlap_obstruction import overlap_sccs
from psc.overlap_seed_patch import (
    OverlapState,
    SeedOverlapAutomaton,
    SeedOverlapTables,
    build_overlap_graph_from_seeds,
    build_seed_overlap_graph_from_tables,
    _first_depths,
    first_coincidence_depths,
    first_left_aligned_depths,
    interior_overlap_cached,
)
from psc.checked_int import checked_add as _checked_add, checked_mul as _checked_mul, checked_sub as _checked_sub
from psc.perron_field3 import (
    CubicElt,
    PerronField3,
    cubic_add_checked,
    cubic_mul,
    cubic_mul_beta,
    cubic_scale_checked,
    cubic_sub_checked,
    sign_at_perron,
)
from psc.perron_interval import PerronEnclosure
from psc.real_root_sign import count_real_roots, isolate_real_roots
from finite_linear_algebra.scalar import q_int


comptime FORMAL_STATE_CAP = 400000
comptime T_DENOMINATOR = 64  # T = A / 64
comptime RHO_SCALE = 1048576  # rho is rounded up to a multiple of 1 / 2^20
comptime ENCLOSURE_REFINEMENTS = 64
comptime MAX_REFINEMENT_ROUNDS = 8


struct FormalCarrier(Copyable, Movable):
    """One recurrent coincidence-free SCC of the formal overlap graph."""

    var members: List[Int]
    var internal_edges: Int
    var realized: Bool
    var closed: Bool
    var aligned: Bool
    var direct_producer: Bool
    var death_depth: Int
    var aligned_depth: Int
    var proper_aligned_depth: Int

    def __init__(
        out self,
        var members: List[Int],
        internal_edges: Int,
        realized: Bool,
        closed: Bool,
        aligned: Bool,
        direct_producer: Bool,
        death_depth: Int,
        aligned_depth: Int,
        proper_aligned_depth: Int,
    ):
        self.members = members^
        self.internal_edges = internal_edges
        self.realized = realized
        self.closed = closed
        self.aligned = aligned
        self.direct_producer = direct_producer
        self.death_depth = death_depth
        self.aligned_depth = aligned_depth
        self.proper_aligned_depth = proper_aligned_depth

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


# ---- exact field quantities ----------------------------------------------------


def _power_traces(field: PerronField3) raises -> Tuple[Int, Int]:
    """`Tr(beta)` and `Tr(beta^2)` from Newton's identities."""
    var p1 = -field.chi2
    return (p1, _checked_sub(_checked_mul(field.chi2, field.chi2), _checked_mul(2, field.chi1)))


def trace(field: PerronField3, x: CubicElt) raises -> Int:
    var p = _power_traces(field)
    return _checked_add(
        _checked_add(_checked_mul(3, x.a0), _checked_mul(x.a1, p[0])), _checked_mul(x.a2, p[1])
    )


def norm(field: PerronField3, x: CubicElt) raises -> Int:
    """`N(x)`: the determinant of multiplication by `x` on `1, beta, beta^2`."""
    var c0 = x
    var c1 = cubic_mul_beta(field, c0)
    var c2 = cubic_mul_beta(field, c1)
    var m: List[List[Int]] = [[c0.a0, c1.a0, c2.a0], [c0.a1, c1.a1, c2.a1], [c0.a2, c1.a2, c2.a2]]
    return _det3_int(m)


def _det3_int(m: List[List[Int]]) raises -> Int:
    var out = 0
    for c in range(3):
        var c1 = (c + 1) % 3
        var c2 = (c + 2) % 3
        var minor = _checked_sub(_checked_mul(m[1][c1], m[2][c2]), _checked_mul(m[1][c2], m[2][c1]))
        out = _checked_add(out, _checked_mul(m[0][c], minor))
    return out


def _least_int_at_least(x: Q) raises -> Int:
    """The least integer `n >= 0` with `n >= x`."""
    var hi = 1
    while q_int(hi).lt(x):
        hi = _checked_mul(hi, 2)
    var lo = 0
    while lo < hi:
        var mid = (lo + hi) // 2
        if q_int(mid).lt(x):
            lo = mid + 1
        else:
            hi = mid
    return lo


def _least_int_square_at_least(x: Q) raises -> Int:
    """The least integer `n >= 0` with `n^2 >= x`."""
    var hi = 1
    while q_int(_checked_mul(hi, hi)).lt(x):
        hi = _checked_mul(hi, 2)
    var lo = 0
    while lo < hi:
        var mid = (lo + hi) // 2
        if q_int(_checked_mul(mid, mid)).lt(x):
            lo = mid + 1
        else:
            hi = mid
    return lo


def _abs_upper(box: IQ) -> Q:
    """`max |x|` over a rational interval."""
    return q_max(q_abs(box.lo), q_abs(box.hi))


def _abs_lower(box: IQ) raises -> Q:
    """`min |x|` over a rational interval."""
    if contains_zero(box):
        return Q.zero()
    return q_min(q_abs(box.lo), q_abs(box.hi))


struct ContractionRegion(Copyable, Movable):
    """`K_T` with `T = A / 64`, and a `w`-box containing it."""

    var field: PerronField3
    var complex_pair: Bool
    var a: Int
    var radii: List[Int]

    def __init__(out self, field: PerronField3, complex_pair: Bool, a: Int, var radii: List[Int]):
        self.field = field
        self.complex_pair = complex_pair
        self.a = a
        self.radii = radii^

    def contains(self, t: CubicElt) raises -> Bool:
        """`4096 q(t) <= A^2`, decided by one exact sign at the Perron root."""
        var a2 = _checked_mul(self.a, self.a)
        var den2 = T_DENOMINATOR * T_DENOMINATOR
        if self.complex_pair:
            # q(t) = 2 N(t) / t(beta); multiply through by t(beta).
            var s = sign_at_perron(self.field, t)
            if s == 0:
                return True
            var y = cubic_sub_checked(
                cubic_scale_checked(t, a2), CubicElt(_checked_mul(2 * den2, norm(self.field, t)), 0, 0)
            )
            return s * sign_at_perron(self.field, y) >= 0
        var t2 = cubic_mul(self.field, t, t)
        var q = cubic_sub_checked(CubicElt(trace(self.field, t2), 0, 0), t2)
        return sign_at_perron(self.field, cubic_sub_checked(CubicElt(a2, 0, 0), cubic_scale_checked(q, den2))) >= 0


struct _QBounds(Copyable, Movable):
    """Rational enclosures shared by the bounds below, refined on demand."""

    var field: PerronField3
    var complex_pair: Bool
    var enclosure: PerronEnclosure

    def __init__(out self, field: PerronField3, complex_pair: Bool) raises:
        self.field = field
        self.complex_pair = complex_pair
        self.enclosure = PerronEnclosure(field, ENCLOSURE_REFINEMENTS)

    def value(self, x: CubicElt) raises -> IQ:
        return self.enclosure.interval(x)

    def q_upper(mut self, x: CubicElt) raises -> Q:
        """A rational upper bound for `q(x)`."""
        if x.is_zero():
            return Q.zero()
        if not self.complex_pair:
            var low = _abs_lower(self.value(x))
            var x2 = cubic_mul(self.field, x, x)
            return require_q(q_int(trace(self.field, x2)).sub(low.mul(low)), "q upper bound")
        var refinements = ENCLOSURE_REFINEMENTS
        for _ in range(MAX_REFINEMENT_ROUNDS):
            var low = _abs_lower(self.value(x))
            if not low.eq(Q.zero()):
                var n = q_abs(q_int(norm(self.field, x)))
                return require_q(n.mul(q_int(2)).div(low), "q upper bound")
            refinements *= 2
            self.enclosure = PerronEnclosure(self.field, refinements)
        raise Error("formal region: Perron enclosure does not separate x(beta) from zero")


def _rho_squared_upper(field: PerronField3, complex_pair: Bool, bounds: _QBounds) raises -> Q:
    """A rational upper bound `< 1` for the squared largest contracting modulus."""
    if complex_pair:
        # beta |z|^2 = |chi0|
        var beta_lo = bounds.enclosure.beta_box.lo.copy()
        return require_q(q_abs(q_int(field.chi0)).div(beta_lo), "rho^2 upper bound")
    var poly = q_poly(field.charpoly())
    var b = 1 + abs(field.chi0) + abs(field.chi1) + abs(field.chi2)
    var brackets = isolate_real_roots(poly, q_int(-b), q_int(b), 3)
    # The Perron root is the bracket with the largest lower end.
    var perron = 0
    for k in range(1, 3):
        if brackets[perron][0].lt(brackets[k][0]):
            perron = k
    var out = Q.zero()
    for k in range(3):
        if k == perron:
            continue
        var lo = brackets[k][0].copy()
        var hi = brackets[k][1].copy()
        for _ in range(200):
            var m = q_max(lo.mul(lo), hi.mul(hi))
            if m.lt(Q.one()):
                break
            var mid = require_q(lo.add(hi).div(q_int(2)), "bisection")
            if count_real_roots(poly, lo, mid) == 1:
                hi = mid^
            else:
                lo = mid^
        out = q_max(out, q_max(lo.mul(lo), hi.mul(hi)))
    return out^


def formal_region(tables: SeedOverlapTables) raises -> ContractionRegion:
    """The contraction region `K_T` and a `w`-box containing it."""
    var field = tables.field
    var complex_pair = discriminant(field) < 0
    var bounds = _QBounds(field, complex_pair)

    var rho2 = _rho_squared_upper(field, complex_pair, bounds)
    var k = _least_int_square_at_least(require_q(rho2.mul(q_int(RHO_SCALE * RHO_SCALE)), "rho scale"))
    if k >= RHO_SCALE:
        raise Error("formal region: contracting modulus bound is not below one")
    var gap = Q(Int64(RHO_SCALE - k), Int64(RHO_SCALE))  # 1 - rho upper bound > 0

    var d2 = Q.zero()
    for i in range(3):
        for j in range(3):
            for x in range(len(tables.sigma[i])):
                for y in range(len(tables.sigma[j])):
                    var c = cubic_sub_checked(tables.prefix(j, y), tables.prefix(i, x))
                    d2 = q_max(d2, bounds.q_upper(c))
    # least A with (A / 64)^2 (1 - rho)^2 >= d2
    var a = _least_int_square_at_least(
        require_q(d2.mul(q_int(T_DENOMINATOR * T_DENOMINATOR)).div(gap.mul(gap)), "T bound")
    )
    var t2 = Q(Int64(a * a), Int64(T_DENOMINATOR * T_DENOMINATOR))

    # Trace-dual basis: det(G) l*_b = sum_c adj(G)_bc l_c with G_ab = Tr(l_a l_b).
    var g = List[List[Int]]()
    for x in range(3):
        var row = List[Int]()
        for y in range(3):
            row.append(trace(field, cubic_mul(field, tables.lengths.at(x), tables.lengths.at(y))))
        g.append(row^)
    var det = _det3_int(g)
    if det == 0:
        raise Error("formal region: singular trace form on the tile lengths")
    var lmax = Q.zero()
    for x in range(3):
        lmax = q_max(lmax, bounds.value(tables.lengths.at(x)).hi.copy())
    var radii = List[Int]()
    for b in range(3):
        var dual = CubicElt()
        for c in range(3):
            var r0 = (b + 1) % 3
            var r1 = (b + 2) % 3
            var c0 = (c + 1) % 3
            var c1 = (c + 2) % 3
            # adj(G)_bc = cofactor(c, b)
            var cof = _checked_sub(_checked_mul(g[c0][r0], g[c1][r1]), _checked_mul(g[c0][r1], g[c1][r0]))
            dual = cubic_add_checked(dual, cubic_scale_checked(tables.lengths.at(c), cof))
        var scale = q_int(abs(det))
        var at_beta = require_q(_abs_upper(bounds.value(dual)).div(scale), "dual value")
        var q_dual = require_q(bounds.q_upper(dual).div(scale.mul(scale)), "dual q")
        var linear = _least_int_at_least(require_q(lmax.mul(at_beta), "box linear term"))
        var contracting = _least_int_square_at_least(require_q(t2.mul(q_dual), "box contracting term"))
        radii.append(linear + contracting + 1)
    return ContractionRegion(field, complex_pair, a, radii^)


# ---- exact construction -------------------------------------------------------


def formal_seed_states(
    tables: SeedOverlapTables, region: ContractionRegion, mut sign_cache: Dict[CubicElt, Int]
) raises -> List[OverlapState]:
    """Every genuine potential overlap `(i, j, sum_a w_a l_a)` of the box whose
    shift lies in the contraction region."""
    ref box = region.radii
    var out = List[OverlapState]()
    for w0 in range(-box[0], box[0] + 1):
        var t0 = cubic_scale_checked(tables.lengths.at(0), w0)
        for w1 in range(-box[1], box[1] + 1):
            var t1 = cubic_add_checked(t0, cubic_scale_checked(tables.lengths.at(1), w1))
            for w2 in range(-box[2], box[2] + 1):
                var t = cubic_add_checked(t1, cubic_scale_checked(tables.lengths.at(2), w2))
                var genuine = List[OverlapState]()
                for top in range(3):
                    for bottom in range(3):
                        var s = OverlapState(top, bottom, t)
                        if interior_overlap_cached(tables, sign_cache, s):
                            genuine.append(s)
                if len(genuine) > 0 and region.contains(t):
                    out += genuine^
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


def _least_depth(comp: List[Int], depths: List[Int]) -> Int:
    """The least nonnegative `depths[v]` over `comp`, `-1` if there is none."""
    var out = -1
    for i in range(len(comp)):
        var d = depths[comp[i]]
        if d >= 0 and (out < 0 or d < out):
            out = d
    return out


def survey_formal_overlaps(
    tables: SeedOverlapTables, max_states: Int = FORMAL_STATE_CAP
) raises -> FormalSurvey:
    var cache = Dict[CubicElt, Int]()
    var region = formal_region(tables)
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
    var aligned_depths = first_left_aligned_depths(formal)
    var proper_target = List[Bool]()
    for v in range(formal.size()):
        proper_target.append(formal.states[v].shift.is_zero() and not formal.states[v].is_coincidence())
    var proper_depths = _first_depths(formal, proper_target)
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
        for i in range(len(comp)):
            var v = comp[i]
            var s = formal.states[v]
            if s in in_realized:
                n_real += 1
            inside = inside and s in in_seeds
            aligned = aligned or s.shift.is_zero()
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
            FormalCarrier(
                comp.copy(), internal, n_real > 0, closed, aligned, direct,
                _least_depth(comp, depth), _least_depth(comp, aligned_depths),
                _least_depth(comp, proper_depths),
            )
        )

    var realized_comps = recurrent_coincidence_free_sccs(realized)
    if len(realized_comps) != realized_count:
        raise Error("realized carriers disagree with the realized formal carriers")

    return FormalSurvey(
        formal^, realized.size(), box^, len(seeds), nonproductive, carriers^, inside
    )


def aligned_pair_depth(s: FormalSurvey) raises -> Int:
    """`S(sigma)`: the largest first-coincidence depth of the six aligned pairs
    `(i, j, 0)`, `i != j`, or `-1` if one of them is nonproductive.

    They are the only offset-zero states that are not coincidences, and `t = 0`
    is genuine and in every contraction region, so all six are formal seeds;
    a missing one is an impossible state and raises. With `L` the first
    offset-zero depth of a state and `D` its coincidence depth, `D <= L + S`
    (docs/formal-productivity-reduction-2026-10-04.md)."""
    var depth = first_coincidence_depths(s.formal)
    var found = 0
    var out = 0
    for v in range(s.formal.size()):
        var x = s.formal.states[v]
        if x.shift.is_zero() and not x.is_coincidence():
            found += 1
            if depth[v] < 0:
                out = -1
            elif out >= 0 and depth[v] > out:
                out = depth[v]
    if found != 6:
        raise Error("formal graph does not hold exactly the six aligned pairs")
    return out
