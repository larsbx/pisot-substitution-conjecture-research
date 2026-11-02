"""Verified finite reversal-orbit quotient with literal indexed edge lifts.

This checker operates on an already completed native IndexedGraph. It verifies
state uniqueness, actual child words/Parikh transport, strict geometry,
ordered occurrence multiplicities, and reversal covariance. It does NOT
establish that a supplied graph is complete: that premise comes from the
fail-closed native builder and its independent complete-edge differential
oracle. All results are FINITE-INSTANCE, not universal BH or PSC.
"""

from std.collections import Dict
from finite_exact.checked_int import checked_add, checked_mul
from psc.class_a_boundary_children import BoundaryLabel, geometric_state, member_transport, _run, _letter
from psc.class_a_x_ladder import reversed_label
from psc.class_a_x_productivity import IndexedGraph, terminal
from psc.overlap_seed_patch import OverlapState, SeedOverlapTables, interior_overlap


struct VerifiedReversalQuotient(Copyable, Movable):
    var representatives: List[Int]
    var orbit_of: List[Int]
    var partner: List[Int]
    var adj: List[List[Int]]
    var ii: List[List[Int]]
    var jj: List[List[Int]]
    var original_edges: Int

    def __init__(out self, representatives: List[Int], orbit_of: List[Int],
                 partner: List[Int], adj: List[List[Int]],
                 ii: List[List[Int]], jj: List[List[Int]], original_edges: Int):
        self.representatives = representatives.copy()
        self.orbit_of = orbit_of.copy()
        self.partner = partner.copy()
        self.adj = adj.copy()
        self.ii = ii.copy()
        self.jj = jj.copy()
        self.original_edges = original_edges


def verify_indexed_reversal_quotient(
    tables: SeedOverlapTables, g: IndexedGraph, k: Int, t: Int
) raises -> VerifiedReversalQuotient:
    """Construct the quotient *only after* checking all recorded original edges.

    The representative is the smaller original vertex ID of an R-orbit;
    this is deliberately not the Python oracle's lexicographic ordering.
    Orbit structure, indexed edge multiplicities and lifted paths must agree
    independently of this arbitrary enumeration convention.
    """
    if k < 0 or t < 0:
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
    var ids = Dict[OverlapState, Int]()
    for v in range(count):
        var w = g.states[v]
        if w.top < 0 or w.top >= 3 or w.bottom < 0 or w.bottom >= 3:
            raise Error("invalid oriented tile types")
        var key = geometric_state(tables, w)
        if key in ids:
            raise Error("duplicate or noninjective full-Parikh state")
        ids[key] = v
        if not interior_overlap(tables, key):
            raise Error("non-strict listed state")
        if len(g.adj[v]) != len(g.ii[v]) or len(g.adj[v]) != len(g.jj[v]):
            raise Error("missing indexed occurrence arrays")
        if terminal(w) and len(g.adj[v]) != 0:
            raise Error("typed full-zero coincidence must be terminalized")

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
            if child != g.states[dest] or not interior_overlap(tables, geometric_state(tables, child)):
                raise Error("indexed edge has wrong typed Parikh child or strictness")
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
    return VerifiedReversalQuotient(reps, orbit, partner, adj, ii, jj, original_edges)


def lift_quotient_edge(
    tables: SeedOverlapTables, g: IndexedGraph, q: VerifiedReversalQuotient,
    source: Int, selected: Int, k: Int, t: Int
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
    if not interior_overlap(tables, geometric_state(tables, actual)):
        raise Error("selected edge is not strictly geometric")
    for e in range(len(g.adj[source])):
        var dst = g.adj[source][e]
        if g.ii[source][e] == i and g.jj[source][e] == j:
            if actual != g.states[dst] or q.orbit_of[dst] != q.adj[qid][selected]:
                raise Error("selected lift has wrong typed target orbit")
            return dst
    raise Error("selected quotient edge has no actual occurrence lift")
