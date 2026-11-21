"""Complete original S18 graphs for explicitly named small plus members.

The finite scope is the five seams n=1..5, d=n+4, and the 70 upper members
n=0..6, n+5<=d<=2n+11 below the n>=7 all-source entry theorem. Strict geometry is exact, every ordered
occurrence is retained, and typed full zero is the only terminal. Bounds
refuse rather than yielding a partial mathematical verdict.
"""
from std.collections import Dict
from finite_exact.checked_int import checked_add, checked_sub, checked_mul
from psc.class_a_boundary_children import (
    BoundaryLabel, _run, _prefix, _letter, geometric_state,
)
from psc.class_a_plus_sources import plus_swap_sources
from psc.class_a_x_productivity import IndexedGraph, _intern, backwards, terminal
from psc.overlap_seed_patch import (
    SeedOverlapTables, OverlapState, interior_overlap_cached, cached_sign,
    selected_overlap_child,
)
from psc.perron_field3 import (
    CubicElt, cubic_add_checked, cubic_sub_checked, cubic_mul_beta, sign_at_perron,
)


def seam_member(n: Int, d: Int) -> Bool:
    return n >= 1 and n <= 5 and d == n+4


def upper_small_member(n: Int, d: Int) -> Bool:
    """The 70 upper members below the n>=7 all-source entry theorem."""
    return n >= 0 and n <= 6 and d >= n+5 and d <= 2*n+11


def small_parameters(n: Int, d: Int) raises:
    if not (seam_member(n, d) or upper_small_member(n, d)):
        raise Error("plus small certificate requires one of (1,5)..(5,9) "
                    "or an upper member n<=6, n+5<=d<=2n+11")


def perron_floor(n: Int, d: Int) raises -> Int:
    """Exact floor of the largest real root of the literal plus cubic
    x^3-(n+4)x^2+(n+5-d)x-2, which has no integer root on this domain.
    n+3 on the five seams; the scan is bounded by the Cauchy bound."""
    small_parameters(n, d)
    var bound = 1 + max(n+4, max(abs(n+5-d), 2))
    var b = -1
    for x in range(bound+1):
        var chi = checked_sub(checked_add(checked_sub(checked_mul(checked_mul(x, x), x),
                  checked_mul(n+4, checked_mul(x, x))), checked_mul(n+5-d, x)), 2)
        if chi == 0:
            raise Error("integer root: reducible plus cubic")
        if chi < 0:
            b = x
    if b < 0 or (seam_member(n, d) and b != n+3):
        raise Error("plus Perron floor outside its exact interval")
    return b


def bind_small(tables: SeedOverlapTables, n: Int, d: Int) raises:
    """Separate literal small-member binding; the large binder is unchanged."""
    small_parameters(n, d)
    if len(tables.sigma) != 3:
        raise Error("plus small certificate requires three literal images")
    for a in range(3):
        var run = _run(1, n, d, a)
        if len(tables.sigma[a]) != run+2:
            raise Error("foreign small plus image length")
        for i in range(run+2):
            if tables.sigma[a][i] != _letter(1, n, d, a, i):
                raise Error("foreign small plus ordered image")
    if (tables.field.chi0 != -2 or tables.field.chi1 != n-d+5 or
        tables.field.chi2 != -(n+4)):
        raise Error("foreign small plus incidence cubic")
    var b = perron_floor(n, d)
    if (sign_at_perron(tables.field, CubicElt(-b, 1, 0)) <= 0 or
        sign_at_perron(tables.field, CubicElt(-(b+1), 1, 0)) >= 0):
        raise Error("foreign small plus Perron interval")
    var total = 0
    for a in range(3):
        total += len(tables.sigma[a])
    if len(tables.prefix_starts) != 4 or len(tables.prefix_positions) != total:
        raise Error("foreign small plus prefix-cache dimensions")
    var start = 0
    for a in range(3):
        if sign_at_perron(tables.field, tables.lengths.at(a)) <= 0:
            raise Error("nonpositive small plus tile length")
        if tables.prefix_starts[a] != start:
            raise Error("shifted small plus prefix cache")
        var cursor = CubicElt()
        for i in range(len(tables.sigma[a])):
            if tables.prefix_positions[start+i] != cursor:
                raise Error("small plus prefix cache differs from literal word")
            cursor = cubic_add_checked(cursor, tables.lengths.at(tables.sigma[a][i]))
        if cursor != cubic_mul_beta(tables.field, tables.lengths.at(a)):
            raise Error("small plus literal lengths fail exact scaling")
        start += len(tables.sigma[a])
    if tables.prefix_starts[3] != start:
        raise Error("wrong final small plus prefix endpoint")


def small_transport(n: Int, d: Int, w: BoundaryLabel, i: Int, j: Int) raises -> BoundaryLabel:
    """Full plus incidence and actual original-prefix Parikh transport."""
    small_parameters(n, d)
    var top = _prefix(1, n, d, w.top, i)
    var bottom = _prefix(1, n, d, w.bottom, j)
    var x = checked_add(checked_add(checked_mul(2, w.x), w.c), w.y)
    var c = checked_add(w.c, w.y)
    var y = checked_add(checked_add(checked_mul(n+d, w.x), checked_mul(n, w.c)),
                        checked_mul(n+1, w.y))
    return BoundaryLabel(_letter(1, n, d, w.top, i), _letter(1, n, d, w.bottom, j),
        checked_add(x, checked_sub(bottom[0], top[0])),
        checked_add(c, checked_sub(bottom[1], top[1])),
        checked_add(y, checked_sub(bottom[2], top[2])))


def build_small(tables: SeedOverlapTables, n: Int, d: Int,
                state_cap: Int=6000, pair_cap: Int=20000000) raises -> IndexedGraph:
    bind_small(tables, n, d)
    if state_cap < 18 or pair_cap < 1:
        raise Error("incomplete small plus graph: insufficient caps")
    var states = List[BoundaryLabel]()
    var ids = Dict[OverlapState, Int]()
    var cache = Dict[CubicElt, Int]()
    for w in plus_swap_sources(tables):
        _ = _intern(tables, states, ids, w, state_cap)
    var adj = List[List[Int]]()
    var ii = List[List[Int]]()
    var jj = List[List[Int]]()
    var pairs = 0
    var cursor = 0
    while cursor < len(states):
        var w = states[cursor]
        var targets = List[Int]()
        var top_indices = List[Int]()
        var bottom_indices = List[Int]()
        if not terminal(w):
            pairs = checked_add(pairs, checked_mul(len(tables.sigma[w.top]), len(tables.sigma[w.bottom])))
            if pairs > pair_cap:
                raise Error("incomplete small plus graph: occurrence-pair cap")
            var scaled = cubic_mul_beta(tables.field, geometric_state(tables, w).shift)
            var first_bottom = 0
            for i in range(len(tables.sigma[w.top])):
                var top_prefix = tables.prefix(w.top, i)
                var top_end = cubic_add_checked(top_prefix, tables.lengths.at(tables.sigma[w.top][i]))
                while first_bottom < len(tables.sigma[w.bottom]):
                    var start = cubic_add_checked(scaled, tables.prefix(w.bottom, first_bottom))
                    var finish = cubic_add_checked(start, tables.lengths.at(tables.sigma[w.bottom][first_bottom]))
                    if cached_sign(tables, cache, cubic_sub_checked(finish, top_prefix)) > 0:
                        break
                    first_bottom += 1
                var j = first_bottom
                while j < len(tables.sigma[w.bottom]):
                    var start = cubic_add_checked(scaled, tables.prefix(w.bottom, j))
                    if cached_sign(tables, cache, cubic_sub_checked(start, top_end)) >= 0:
                        break
                    var child = small_transport(n, d, w, i, j)
                    if interior_overlap_cached(tables, cache, geometric_state(tables, child)):
                        targets.append(_intern(tables, states, ids, child, state_cap))
                        top_indices.append(i)
                        bottom_indices.append(j)
                    j += 1
        adj.append(targets^)
        ii.append(top_indices^)
        jj.append(bottom_indices^)
        cursor += 1
    return IndexedGraph(states, adj, ii, jj)


def distances(g: IndexedGraph) raises -> List[Int]:
    var roots = List[Int]()
    for v in range(len(g.states)):
        if terminal(g.states[v]):
            roots.append(v)
    if len(roots) == 0:
        raise Error("small plus graph has no typed zero")
    return backwards(g.adj, roots)


def select_edges(g: IndexedGraph, distance: List[Int]) raises -> List[Int]:
    if len(distance) != len(g.states):
        raise Error("incomplete small plus distance vector")
    var selected = List[Int](length=len(g.states), fill=-1)
    for v in range(len(g.states)):
        if distance[v] < 0:
            raise Error("small plus state has no certified typed-zero path")
        if distance[v] == 0:
            if not terminal(g.states[v]):
                raise Error("nonterminal small plus distance zero")
            continue
        for z in range(len(g.adj[v])):
            var target = g.adj[v][z]
            if target < 0 or target >= len(g.states):
                raise Error("small plus edge target out of graph")
            if distance[target] == distance[v]-1:
                selected[v] = z
                break
        if selected[v] < 0:
            raise Error("no original decreasing small plus edge")
    return selected^


def verify_small(tables: SeedOverlapTables, n: Int, d: Int, g: IndexedGraph,
                 distance: List[Int], selected: List[Int],
                 state_cap: Int=6000, pair_cap: Int=20000000) raises -> List[Int]:
    """Exhaust all original Cartesian pairs, including absent intersections.

    Verify deterministic discovery order, complete rows, unique full states,
    actual strict geometry, exact shortest distances and selected edges.
    Return vertices, edges, Cartesian pairs, maximum distance and path edges.
    """
    bind_small(tables, n, d)
    var size = len(g.states)
    if size < 18 or size > state_cap or pair_cap < 1:
        raise Error("invalid or capped small plus certificate domain")
    if (len(g.adj) != size or len(g.ii) != size or len(g.jj) != size or
        len(distance) != size or len(selected) != size):
        raise Error("small plus certificate has missing rows")
    var sources = plus_swap_sources(tables)
    var ids = Dict[OverlapState, Int]()
    var cache = Dict[CubicElt, Int]()
    for v in range(size):
        var key = geometric_state(tables, g.states[v])
        if key in ids or not interior_overlap_cached(tables, cache, key):
            raise Error("duplicate, aliased or non-strict small plus state")
        ids[key] = v
        if v < 18 and g.states[v] != sources[v]:
            raise Error("missing or reordered actual plus swap source")
    var seen = List[Bool](length=size, fill=False)
    for v in range(18):
        seen[v] = True
    var discovered = 18
    var edges = 0
    var pairs = 0
    var maximum = 0
    var path_edges = 0
    for v in range(size):
        if not seen[v] or len(g.ii[v]) != len(g.adj[v]) or len(g.jj[v]) != len(g.adj[v]):
            raise Error("unreachable small plus state or malformed row")
        var w = g.states[v]
        var row = 0
        if not terminal(w):
            pairs = checked_add(pairs, checked_mul(len(tables.sigma[w.top]), len(tables.sigma[w.bottom])))
            if pairs > pair_cap:
                raise Error("small plus verification occurrence-pair cap")
            for i in range(len(tables.sigma[w.top])):
                for j in range(len(tables.sigma[w.bottom])):
                    var child = small_transport(n, d, w, i, j)
                    var key = geometric_state(tables, child)
                    if not interior_overlap_cached(tables, cache, key):
                        continue
                    if key not in ids:
                        raise Error("omitted small plus child state")
                    var target = ids[key]
                    if g.states[target] != child:
                        raise Error("small plus child lost a full integral coordinate")
                    if row >= len(g.adj[v]):
                        raise Error("omitted original small plus edge")
                    if g.adj[v][row] != target or g.ii[v][row] != i or g.jj[v][row] != j:
                        raise Error("small plus row differs from every ordered actual pair")
                    if selected_overlap_child(tables, geometric_state(tables, w), i, j) != key:
                        raise Error("small plus literal and geometric transport disagree")
                    if not seen[target]:
                        if target != discovered:
                            raise Error("small plus state discovery order changed")
                        seen[target] = True
                        discovered += 1
                    row += 1
        if row != len(g.adj[v]):
            raise Error("extra or terminalized small plus outgoing edge")
        edges = checked_add(edges, row)
        maximum = max(maximum, distance[v])
        path_edges = checked_add(path_edges, distance[v])
    if discovered != size:
        raise Error("small plus certificate includes unreachable states")
    var actual_distance = distances(g)
    var actual_selected = select_edges(g, actual_distance)
    for v in range(size):
        if distance[v] != actual_distance[v] or selected[v] != actual_selected[v]:
            raise Error("wrong small plus distance or original selected edge")
    return [size, edges, pairs, maximum, path_edges]
