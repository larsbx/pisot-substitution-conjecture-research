"""Exact prefix-aligned overlap decisions for the cyclic first-letter pairs.

The graph has terminal diagonals, and every nonterminal row retains all
positive-interior occurrence edges. The finite-system interpretation is in
docs/c4-periodic-ray-decision-2026-11-14.md.
"""

from psc.overlap_seed_patch import (
    OverlapState,
    SeedOverlapAutomaton,
    SeedOverlapTables,
    build_overlap_graph_from_seeds,
    build_seed_overlap_tables_screened,
    first_coincidence_depths,
    first_depths,
    interior_overlap_cached,
    selected_overlap_child,
)
from psc.perron_field3 import CubicElt, cubic_sub_checked


struct PeriodicRayDecision(Copyable, Movable):
    var top: Int
    var bottom: Int
    var state_count: Int
    var occurrence_count: Int
    var coincidence_depth: Int
    # A finite nonnegative depth for all states gives the uniform gap bound.
    # -1 is either a failed boundary test or a productive root, where the
    # boundary test is unnecessary and is skipped.
    var boundary_depth: Int
    var top_digits: List[Int]
    var bottom_digits: List[Int]

    def __init__(
        out self, top: Int, bottom: Int, state_count: Int, occurrence_count: Int,
        coincidence_depth: Int, boundary_depth: Int,
        var top_digits: List[Int], var bottom_digits: List[Int],
    ):
        self.top = top
        self.bottom = bottom
        self.state_count = state_count
        self.occurrence_count = occurrence_count
        self.coincidence_depth = coincidence_depth
        self.boundary_depth = boundary_depth
        self.top_digits = top_digits^
        self.bottom_digits = bottom_digits^

    def has_strict_system(self) -> Bool:
        return self.coincidence_depth == -1 and self.boundary_depth >= 0


def has_common_endpoint(
    tables: SeedOverlapTables, state: OverlapState
) raises -> Bool:
    return state.shift.is_zero() or state.shift == cubic_sub_checked(
        tables.lengths.at(state.top), tables.lengths.at(state.bottom)
    )


def common_endpoint_depth(
    tables: SeedOverlapTables, graph: SeedOverlapAutomaton,
) raises -> Int:
    """Maximum distance to a common endpoint, or -1 for an unreachable target."""
    var targets = List[Bool]()
    for k in range(graph.size()):
        targets.append(has_common_endpoint(tables, graph.states[k]))
    var depths = first_depths(graph, targets)
    var worst = 0
    for k in range(len(depths)):
        if depths[k] == -1:
            return -1
        worst = max(worst, depths[k])
    return worst


def _decide_pair(
    tables: SeedOverlapTables, top: Int, bottom: Int, max_states: Int
) raises -> PeriodicRayDecision:
    var seeds = List[OverlapState]()
    seeds.append(OverlapState(top, bottom, CubicElt()))
    var cache = Dict[CubicElt, Int]()
    var graph = build_overlap_graph_from_seeds(tables, seeds, cache, max_states)
    var coincidence = first_coincidence_depths(graph)
    var occurrence_count = 0
    for k in range(graph.size()):
        occurrence_count += len(graph.adj[k])

    # A productive graph uses terminal diagonals. The boundary test only
    # runs on the full graph in the absence of a diagonal.
    var boundary_depth = -1
    if coincidence[0] == -1:
        boundary_depth = common_endpoint_depth(tables, graph)

    # Replay a shortest coincidence path using the exact occurrence addresses.
    # A repeated target keeps its position in the complete child row.
    var top_digits = List[Int]()
    var bottom_digits = List[Int]()
    var vertex = 0
    while coincidence[vertex] > 0:
        var row_idx = 0
        var next_vertex = -1
        var state = graph.states[vertex]
        for i in range(len(tables.sigma[state.top])):
            for j in range(len(tables.sigma[state.bottom])):
                var child = selected_overlap_child(tables, state, i, j)
                if not interior_overlap_cached(tables, cache, child):
                    continue
                if row_idx >= len(graph.adj[vertex]):
                    raise Error("periodic-ray child row omitted a literal occurrence")
                var target = graph.adj[vertex][row_idx]
                if graph.states[target] != child:
                    raise Error("periodic-ray child row does not match literal order")
                row_idx += 1
                if next_vertex == -1 and coincidence[target] == coincidence[vertex] - 1:
                    top_digits.append(i)
                    bottom_digits.append(j)
                    next_vertex = target
        if row_idx != len(graph.adj[vertex]) or next_vertex == -1:
            raise Error("periodic-ray child row failed coincidence path replay")
        vertex = next_vertex

    return PeriodicRayDecision(
        top, bottom, graph.size(), occurrence_count, coincidence[0], boundary_depth,
        top_digits^, bottom_digits^
    )


def decide_periodic_rays(
    sigma: List[List[Int]], max_states: Int = 20000
) raises -> List[PeriodicRayDecision]:
    """Return a complete result per unordered pair of cyclic first letters."""
    if max_states <= 0:
        raise Error("periodic-ray graph state budget must be positive")
    var tables = build_seed_overlap_tables_screened(sigma)
    var cyclic = List[Bool]()
    for a in range(3):
        var first = a
        var returns = False
        for _ in range(3):
            first = sigma[first][0]
            returns = returns or first == a
        cyclic.append(returns)

    var result = List[PeriodicRayDecision]()
    for a in range(3):
        for b in range(a + 1, 3):
            if cyclic[a] and cyclic[b]:
                result.append(_decide_pair(tables, a, b, max_states))
    return result^
