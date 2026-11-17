"""All legal lifts of one nonzero periodic class in the unit PIP3 torus.

Enumerate the certified rational coset of centre-tile states and retain the
cycles of the literal first-return map. Compare every unordered pair in
the complete descendant graph, including pairs moved by the return.
See docs/c4-rank-two-periodic-compatibility-2026-11-17.md.
"""

from finite_exact.checked_int import checked_add, checked_mul, checked_sub
from finite_graph.scc import has_cycle, sccs
from psc.c4_geometric_f import PrototileMap, PrototileState, stable_radii
from psc.overlap_seed_patch import (
    OverlapState,
    build_overlap_graph_from_seeds,
    first_coincidence_depths,
    first_depths,
    first_left_aligned_depths,
)
from psc.perron_field3 import CubicElt, cubic_scale_checked, cubic_sub_checked


struct PeriodicFibreLift(Copyable, Movable):
    # The tile starts at minus centre.vector() / denominator.
    var centre: PrototileState
    var indices: List[Int]
    var next_lift: Int

    def __init__(out self, centre: PrototileState, var indices: List[Int], next_lift: Int):
        self.centre = centre
        self.indices = indices^
        self.next_lift = next_lift


struct PeriodicFibrePair(ImplicitlyCopyable, Copyable, Movable):
    var top: Int
    var bottom: Int
    var shared_vertex_depth: Int
    var coincidence_depth: Int
    var cut_free_depth: Int

    def __init__(out self, top: Int, bottom: Int, vertex: Int, coincidence: Int, cut_free: Int):
        self.top = top
        self.bottom = bottom
        self.shared_vertex_depth = vertex
        self.coincidence_depth = coincidence
        self.cut_free_depth = cut_free

    def bounded_gaps(self) -> Bool:
        return self.cut_free_depth < 0


struct PeriodicFibre(Copyable, Movable):
    var denominator: Int
    var return_power: Int
    var lifts: List[PeriodicFibreLift]
    var pairs: List[PeriodicFibrePair]
    var alignment_depth_bound: Int

    def __init__(
        out self, denominator: Int, return_power: Int, var lifts: List[PeriodicFibreLift]
    ):
        self.denominator = denominator
        self.return_power = return_power
        self.lifts = lifts^
        self.pairs = List[PeriodicFibrePair]()
        self.alignment_depth_bound = 0


def _candidate_states(
    mut m: PrototileMap, p: List[Int], d: Int, mut work_left: Int
) raises -> List[PrototileState]:
    # stable_radii floors upper bounds for integer states. The actual
    # rational coordinates satisfy |v_a / d| < radii[a] + 1.
    var radii = stable_radii(m.tables)
    var volume = 1
    for a in range(3):
        volume = checked_mul(volume, 2 * radii[a] + 2)
    if volume > work_left:
        raise Error("periodic fibre: work cap reached; inconclusive")
    work_left -= volume
    var lengths = List[CubicElt]()
    for a in range(3):
        lengths.append(cubic_scale_checked(m.tables.lengths.at(a), d))
    var states = List[PrototileState]()
    for x in range(-radii[0], radii[0] + 2):
        var v0 = checked_sub(checked_mul(d, x), p[0])
        for y in range(-radii[1], radii[1] + 2):
            var v1 = checked_sub(checked_mul(d, y), p[1])
            for z in range(-radii[2], radii[2] + 2):
                var v2 = checked_sub(checked_mul(d, z), p[2])
                var position = m.position(PrototileState(0, v0, v1, v2))
                if m.sign(position) <= 0:
                    continue
                for a in range(3):
                    if m.sign(cubic_sub_checked(position, lengths[a])) < 0:
                        states.append(PrototileState(a, v0, v1, v2))
    return states^


def _return_cycles(
    mut m: PrototileMap, states: List[PrototileState], d: Int, n: Int, work_left: Int
) raises -> List[PeriodicFibreLift]:
    if len(states) > work_left // n:
        raise Error("periodic fibre: work cap reached; inconclusive")
    var index = Dict[PrototileState, Int]()
    for i in range(len(states)):
        index[states[i]] = i
    var adj = List[List[Int]]()
    var paths = List[List[Int]]()
    for i in range(len(states)):
        var s = states[i]
        var path = List[Int]()
        for _ in range(n):
            var step = m.step(s, d)
            s = step.child
            path.append(step.index)
        var row = List[Int]()
        if s in index:
            row.append(index[s])
        adj.append(row^)
        paths.append(path^)

    var keep = List[Int](length=len(states), fill=-1)
    var components = sccs(adj)
    for comp in components:
        if has_cycle(adj, comp):
            for v in comp:
                keep[v] = 0
    var count = 0
    for i in range(len(states)):
        if keep[i] >= 0:
            keep[i] = count
            count += 1
    var lifts = List[PeriodicFibreLift]()
    for i in range(len(states)):
        if keep[i] >= 0:
            var target = keep[adj[i][0]]
            if target < 0:
                raise Error("periodic fibre: a cycle edge left the catalogue")
            lifts.append(PeriodicFibreLift(states[i], paths[i].copy(), target))
    return lifts^


def _compare_lifts(
    mut m: PrototileMap, mut fibre: PeriodicFibre, max_overlap_states: Int
) raises:
    var seeds = List[OverlapState]()
    var d = fibre.denominator
    for i in range(len(fibre.lifts)):
        var a = fibre.lifts[i].centre
        for j in range(i + 1, len(fibre.lifts)):
            var b = fibre.lifts[j].centre
            var x = checked_sub(a.v0, b.v0)
            var y = checked_sub(a.v1, b.v1)
            var z = checked_sub(a.v2, b.v2)
            if x % d != 0 or y % d != 0 or z % d != 0:
                raise Error("periodic fibre: centre-tile offset is outside the lattice")
            var shift = m.position(PrototileState(0, x // d, y // d, z // d))
            seeds.append(OverlapState(a.letter, b.letter, shift))
    if len(seeds) == 0:
        return
    var graph = build_overlap_graph_from_seeds(m.tables, seeds, m.signs, max_overlap_states)
    var vertex_depth = first_left_aligned_depths(graph)
    var coincidence_depth = first_coincidence_depths(graph)
    var bad = List[Bool]()
    var index = Dict[OverlapState, Int]()
    for i in range(graph.size()):
        index[graph.states[i]] = i
        bad.append(vertex_depth[i] < 0)
        fibre.alignment_depth_bound = max(fibre.alignment_depth_bound, vertex_depth[i])
    var bad_depth = first_depths(graph, bad)
    var k = 0
    for i in range(len(fibre.lifts)):
        for j in range(i + 1, len(fibre.lifts)):
            var root = index[seeds[k]]
            fibre.pairs.append(PeriodicFibrePair(i, j, vertex_depth[root], coincidence_depth[root], bad_depth[root]))
            k += 1


def catalogue_periodic_fibre(
    sigma: List[List[Int]], numerator: List[Int], denominator: Int, return_power: Int,
    max_work: Int = 2000000, max_overlap_states: Int = 20000,
) raises -> PeriodicFibre:
    """For a normalized nonzero class fixed by `M^return_power`, within the
    audited substitution input range of `PrototileMap`.

    Work counts box positions, the base-residue steps, and the steps of all
    candidate first returns. Invalid inputs and incomplete searches raise.
    Each retained path records the literal child index in each parent image.
    """
    if denominator <= 1 or len(numerator) != 3 or numerator == [0, 0, 0]:
        raise Error("periodic fibre: expected a nonzero normalized rational class")
    for x in numerator:
        if x < 0 or x >= denominator:
            raise Error("periodic fibre: expected a nonzero normalized rational class")
    if return_power <= 0 or max_work <= 0 or max_overlap_states <= 0:
        raise Error("periodic fibre: return power and caps must be positive")
    if return_power > max_work:
        raise Error("periodic fibre: work cap reached; inconclusive")
    var m = PrototileMap(sigma)
    var det = m.incidence.det()
    if det != 1 and det != -1:
        raise Error("periodic fibre: incidence matrix must be unimodular")
    var phase = numerator.copy()
    for _ in range(return_power):
        phase = m.apply_incidence(phase)
        for a in range(3):
            phase[a] %= denominator
    if phase != numerator:
        raise Error("periodic fibre: base class does not return at the specified power")

    var work_left = max_work - return_power
    var states = _candidate_states(m, numerator, denominator, work_left)
    var lifts = _return_cycles(m, states, denominator, return_power, work_left)
    if len(lifts) == 0:
        raise Error("periodic fibre: the certified box has no periodic lift")
    var fibre = PeriodicFibre(denominator, return_power, lifts^)
    _compare_lifts(m, fibre, max_overlap_states)
    return fibre^
