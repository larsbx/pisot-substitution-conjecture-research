"""Verified finite reversal-orbit quotient with literal indexed edge lifts.

This checker operates on an already completed native IndexedGraph. It verifies
state uniqueness, actual child words/Parikh transport, strict geometry,
ordered occurrence multiplicities, and reversal covariance. A separate bounded
literal Cartesian scan verifies outgoing completeness and exact S18 closure.
Distance certificates check all-edge lower bounds and lifted upper bounds.
All results are FINITE-INSTANCE, not universal BH or PSC.
"""

from std.collections import Dict
from finite_exact.checked_int import checked_add, checked_mul
from psc.class_a_boundary_children import BoundaryLabel, geometric_state, member_transport, _run, _letter
from psc.class_a_x_ladder import reversed_label
from psc.class_a_x_productivity import IndexedGraph, terminal, nine_sources, backwards
from psc.overlap_seed_patch import OverlapState, SeedOverlapTables, interior_overlap, interior_overlap_cached, selected_overlap_child
from psc.perron_field3 import CubicElt


struct VerifiedReversalQuotient(Copyable, Movable):
    var representatives: List[Int]
    var orbit_of: List[Int]
    var partner: List[Int]
    var adj: List[List[Int]]
    var ii: List[List[Int]]
    var jj: List[List[Int]]
    var original_edges: Int
    var occurrence_pairs: List[Int]

    def __init__(out self, representatives: List[Int], orbit_of: List[Int],
                 partner: List[Int], adj: List[List[Int]],
                 ii: List[List[Int]], jj: List[List[Int]], original_edges: Int, occurrence_pairs: List[Int]):
        self.representatives = representatives.copy()
        self.orbit_of = orbit_of.copy()
        self.partner = partner.copy()
        self.adj = adj.copy()
        self.ii = ii.copy()
        self.jj = jj.copy()
        self.original_edges = original_edges
        self.occurrence_pairs = occurrence_pairs.copy()


def verify_indexed_reversal_quotient(
    tables: SeedOverlapTables, g: IndexedGraph, k: Int, t: Int,
    pair_cap: Int = 20000000, state_cap: Int = 6000
) raises -> VerifiedReversalQuotient:
    """Construct the quotient *only after* checking all recorded original edges.

    The representative is the smaller original vertex ID of an R-orbit;
    this is deliberately not the Python oracle's lexicographic ordering.
    Orbit structure, indexed edge multiplicities and lifted paths must agree
    independently of this arbitrary enumeration convention.
    """
    if k < 0 or t < 0 or pair_cap < 1 or state_cap < 1:
        raise Error("outside minus class-A parameter chamber")
    var n = checked_add(checked_add(k, t), 3)
    var d = checked_add(checked_add(k, checked_mul(2, t)), 5)
    if len(tables.sigma) != 3:
        raise Error("wrong alphabet")
    for a in range(3):
        if len(tables.sigma[a]) != checked_add(_run(-1, n, d, a), 2):
            raise Error("wrong literal image length")
        for z in range(len(tables.sigma[a])):
            if tables.sigma[a][z] != _letter(-1, n, d, a, z):
                raise Error("wrong literal substitution word")

    var count = len(g.states)
    if count == 0 or len(g.adj) != count or len(g.ii) != count or len(g.jj) != count:
        raise Error("missing finite graph arrays")
    if count > state_cap:
        raise Error("state verification cap exhausted: no verdict")
    var ids = Dict[OverlapState, Int]()
    var cache = Dict[CubicElt, Int]()
    var pairs = List[Int]()
    var total_pairs = 0
    for v in range(count):
        var w = g.states[v]
        if w.top < 0 or w.top >= 3 or w.bottom < 0 or w.bottom >= 3:
            raise Error("invalid oriented tile types")
        var key = geometric_state(tables, w)
        if key in ids:
            raise Error("duplicate or noninjective full-Parikh state")
        ids[key] = v
        if not interior_overlap_cached(tables, cache, key):
            raise Error("non-strict listed state")
        if len(g.adj[v]) != len(g.ii[v]) or len(g.adj[v]) != len(g.jj[v]):
            raise Error("missing indexed occurrence arrays")
        if terminal(w) and len(g.adj[v]) != 0:
            raise Error("typed full-zero coincidence must be terminalized")
        var budget = 0 if terminal(w) else checked_mul(len(tables.sigma[w.top]), len(tables.sigma[w.bottom]))
        total_pairs = checked_add(total_pairs, budget)
        if total_pairs > pair_cap:
            raise Error("literal occurrence pair cap exhausted: no verdict")
        pairs.append(budget)

    # Independent of build_indexed's streaming interval sweep: examine EVERY
    # literal (i,j), including rejected/disjoint pairs, in top-major order.
    # Exact sign failures propagate; the budget was checked before this scan.
    for v in range(count):
        var w = g.states[v]
        if terminal(w):
            continue
        var source = geometric_state(tables, w)
        var cursor = 0
        for i in range(len(tables.sigma[w.top])):
            for j in range(len(tables.sigma[w.bottom])):
                var literal = selected_overlap_child(tables, source, i, j)
                if not interior_overlap_cached(tables, cache, literal):
                    continue
                if literal not in ids:
                    raise Error("strict literal child escaped listed carrier")
                var dest = ids[literal]
                if member_transport(-1, k, n, d, w, i, j) != g.states[dest]:
                    raise Error("literal child lost typed full-Parikh lift")
                if cursor >= len(g.adj[v]):
                    raise Error("missing required outgoing occurrence")
                if g.adj[v][cursor] != dest or g.ii[v][cursor] != i or g.jj[v][cursor] != j:
                    raise Error("outgoing row differs from complete literal enumeration")
                cursor += 1
        if cursor != len(g.adj[v]):
            raise Error("spurious outgoing occurrence")

    # Forward closure plus all S18 seeds is not enough to exclude unrelated
    # components: require every listed vertex to be reachable from S18 too.
    var seeds = List[Int]()
    for w in nine_sources():
        for flip in [False, True]:
            var seed = reversed_label(w) if flip else w
            var key = geometric_state(tables, seed)
            if key not in ids or g.states[ids[key]] != seed:
                raise Error("missing actual S18 seed")
            seeds.append(ids[key])
    var reverse_adj = List[List[Int]]()
    for _ in range(count):
        reverse_adj.append(List[Int]())
    for v in range(count):
        for dest in g.adj[v]:
            if dest < 0 or dest >= count:
                raise Error("child outside finite graph")
            reverse_adj[dest].append(v)
    var reached = backwards(reverse_adj, seeds)
    for v in range(count):
        if reached[v] < 0:
            raise Error("listed state is not S18 reachable")

    var partner = List[Int]()
    var fixed = 0
    for v in range(count):
        var rkey = geometric_state(tables, reversed_label(g.states[v]))
        if rkey not in ids:
            raise Error("missing actual reversed state")
        var rv = ids[rkey]
        if g.states[rv] != reversed_label(g.states[v]):
            raise Error("reversal lost full Parikh lift")
        if rv == v:
            if not terminal(g.states[v]):
                raise Error("nonterminal reversal-fixed state")
            fixed += 1
        partner.append(rv)
    for v in range(count):
        if partner[partner[v]] != v:
            raise Error("reversal is not an involution")

    var original_edges = 0
    for v in range(count):
        var w = g.states[v]
        var prev_i = -1
        var prev_j = -1
        for e in range(len(g.adj[v])):
            var dest = g.adj[v][e]
            var i = g.ii[v][e]
            var j = g.jj[v][e]
            if dest < 0 or dest >= count:
                raise Error("indexed child outside finite graph")
            if i < 0 or i >= len(tables.sigma[w.top]) or j < 0 or j >= len(tables.sigma[w.bottom]):
                raise Error("nonexistent literal occurrence index")
            if i < prev_i or (i == prev_i and j <= prev_j):
                raise Error("duplicated or unsorted occurrence pair")
            prev_i = i
            prev_j = j
            var child = member_transport(-1, k, n, d, w, i, j)
            var physical = geometric_state(tables, child)
            var literal = selected_overlap_child(tables, geometric_state(tables, w), i, j)
            if child != g.states[dest] or physical != literal or not interior_overlap_cached(tables, cache, physical):
                raise Error("indexed edge disagrees with independent literal-prefix transport or strictness")
            var rv = partner[v]
            var rdest = partner[dest]
            var found = False
            for z in range(len(g.adj[rv])):
                if g.adj[rv][z] == rdest and g.ii[rv][z] == j and g.jj[rv][z] == i:
                    found = True
                    break
            if not found:
                raise Error("missing occurrence-indexed reversed edge")
            original_edges += 1

    var reps = List[Int]()
    var orbit = List[Int](length=count, fill=-1)
    for v in range(count):
        if v <= partner[v]:
            var qid = len(reps)
            reps.append(v)
            orbit[v] = qid
            orbit[partner[v]] = qid
    for v in range(count):
        if orbit[v] < 0:
            raise Error("incomplete reversal orbit")
    if 2 * len(reps) != count + fixed:
        raise Error("incorrect quotient vertex count")

    var adj = List[List[Int]]()
    var ii = List[List[Int]]()
    var jj = List[List[Int]]()
    var quotient_edges = 0
    for v in reps:
        var targets = List[Int]()
        var top_indices = List[Int]()
        var bottom_indices = List[Int]()
        for e in range(len(g.adj[v])):
            targets.append(orbit[g.adj[v][e]])
            top_indices.append(g.ii[v][e])
            bottom_indices.append(g.jj[v][e])
            quotient_edges += 1
        adj.append(targets^)
        ii.append(top_indices^)
        jj.append(bottom_indices^)
    if original_edges != 2 * quotient_edges:
        raise Error("quotient edges lack genuine paired lifts")
    return VerifiedReversalQuotient(reps, orbit, partner, adj, ii, jj, original_edges, pairs)


def _lift_quotient_edge_cached(
    tables: SeedOverlapTables, g: IndexedGraph, q: VerifiedReversalQuotient,
    source: Int, selected: Int, k: Int, t: Int, mut cache: Dict[CubicElt, Int]
) raises -> Int:
    """Lift one stored quotient edge from EITHER real source orientation."""
    if source < 0 or source >= len(g.states) or len(q.orbit_of) != len(g.states):
        raise Error("source not in recorded quotient")
    var qid = q.orbit_of[source]
    if qid < 0 or qid >= len(q.representatives):
        raise Error("invalid source orbit")
    if selected < 0 or selected >= len(q.adj[qid]):
        raise Error("missing selected quotient occurrence")
    var rep = q.representatives[qid]
    if source != rep and source != q.partner[rep]:
        raise Error("source does not lift from representative orbit")
    var i = q.ii[qid][selected]
    var j = q.jj[qid][selected]
    if source != rep:
        var swap = i
        i = j
        j = swap
    var n = checked_add(checked_add(k, t), 3)
    var d = checked_add(checked_add(k, checked_mul(2, t)), 5)
    var actual = member_transport(-1, k, n, d, g.states[source], i, j)
    if not interior_overlap_cached(tables, cache, geometric_state(tables, actual)):
        raise Error("selected edge is not strictly geometric")
    for e in range(len(g.adj[source])):
        var dst = g.adj[source][e]
        if g.ii[source][e] == i and g.jj[source][e] == j:
            if actual != g.states[dst] or q.orbit_of[dst] != q.adj[qid][selected]:
                raise Error("selected lift has wrong typed target orbit")
            return dst
    raise Error("selected quotient edge has no actual occurrence lift")


def lift_quotient_edge(
    tables: SeedOverlapTables, g: IndexedGraph, q: VerifiedReversalQuotient,
    source: Int, selected: Int, k: Int, t: Int
) raises -> Int:
    var cache = Dict[CubicElt, Int]()
    return _lift_quotient_edge_cached(tables, g, q, source, selected, k, t, cache)


def verify_shortest_distance_bounds(adj: List[List[Int]], distance: List[Int]) raises:
    """All-edge inequalities: distance[v] <= 1 + distance[child]."""
    if len(distance) != len(adj):
        raise Error("incomplete distance domain")
    for rank in distance:
        if rank < 0 or rank >= len(adj):
            raise Error("invalid finite shortest distance")
    for v in range(len(adj)):
        for dst in adj[v]:
            if dst < 0 or dst >= len(adj) or distance[v] > checked_add(distance[dst], 1):
                raise Error("distance violates all-edge lower bound")


def verify_finite_distance_certificate(
    tables: SeedOverlapTables, g: IndexedGraph, k: Int, t: Int,
    original_distance: List[Int], quotient_distance: List[Int], selected: List[Int],
    pair_cap: Int = 20000000, state_cap: Int = 6000
) raises -> VerifiedReversalQuotient:
    """Check supplied distances without trusting the BFS which produced them.

    Full row inequalities give a lower bound; genuine descending lifted paths
    give the upper bound. This contract requires finite distances for EVERY
    listed S18 state. Unreachable or exhausted specimens receive no verdict.
    The quotient is rebuilt, never accepted as a caller-mutable trusted input.
    """
    var q = verify_indexed_reversal_quotient(tables, g, k, t, pair_cap, state_cap)
    var count = len(g.states)
    var orbits = len(q.representatives)
    if len(original_distance) != count or len(quotient_distance) != orbits or len(selected) != orbits:
        raise Error("incomplete distance certificate domain")
    verify_shortest_distance_bounds(g.adj, original_distance)
    verify_shortest_distance_bounds(q.adj, quotient_distance)
    var cache = Dict[CubicElt, Int]()
    for orb in range(orbits):
        var rank = quotient_distance[orb]
        if rank < 0 or rank >= orbits:
            raise Error("invalid finite quotient distance")
        var root = terminal(g.states[q.representatives[orb]])
        if (rank == 0) != root:
            raise Error("false typed terminal distance")
        if root:
            if selected[orb] != -1:
                raise Error("fabricated path from terminal")
        else:
            var e = selected[orb]
            if e < 0 or e >= len(q.adj[orb]):
                raise Error("fabricated selected quotient occurrence")
            if quotient_distance[q.adj[orb][e]] != rank - 1:
                raise Error("selected quotient edge does not descend")
    for v in range(count):
        var rank = original_distance[v]
        if rank < 0 or rank >= count or rank != quotient_distance[q.orbit_of[v]]:
            raise Error("original and quotient distances disagree")
        if (rank == 0) != terminal(g.states[v]):
            raise Error("false original terminal distance")
        # Every quotient edge lifts from every genuine source orientation.
        for e in range(len(q.adj[q.orbit_of[v]])):
            _ = _lift_quotient_edge_cached(tables, g, q, v, e, k, t, cache)
        var current = v
        for step in range(rank):
            var orb = q.orbit_of[current]
            current = _lift_quotient_edge_cached(tables, g, q, current, selected[orb], k, t, cache)
            if original_distance[current] != rank - step - 1:
                raise Error("lifted path has incorrect distance")
        if not terminal(g.states[current]):
            raise Error("fabricated terminal path")
    return q^
