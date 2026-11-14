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


def _occurrence_digits(
    tables: SeedOverlapTables, graph: SeedOverlapAutomaton,
    mut cache: Dict[CubicElt, Int], source: Int, target: Int,
) raises -> Tuple[Int, Int]:
    """Recover the first literal edge to target while checking the ordered row."""
    var state = graph.states[source]
    var row_idx = 0
    var top_digit = -1
    var bottom_digit = -1
    for i in range(len(tables.sigma[state.top])):
        for j in range(len(tables.sigma[state.bottom])):
            var child = selected_overlap_child(tables, state, i, j)
            if not interior_overlap_cached(tables, cache, child):
                continue
            if row_idx >= len(graph.adj[source]):
                raise Error("periodic-ray child row omitted a literal occurrence")
            var at_slot = graph.adj[source][row_idx]
            if graph.states[at_slot] != child:
                raise Error("periodic-ray child row does not match literal order")
            row_idx += 1
            if top_digit == -1 and at_slot == target:
                top_digit = i
                bottom_digit = j
    if row_idx != len(graph.adj[source]) or top_digit == -1:
        raise Error("periodic-ray child row failed occurrence replay")
    return Tuple(top_digit, bottom_digit)


def _cyclic_first_letter(sigma: List[List[Int]], letter: Int) -> Bool:
    var first = letter
    for _ in range(3):
        first = sigma[first][0]
        if first == letter:
            return True
    return False


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

    var top_digits = List[Int]()
    var bottom_digits = List[Int]()
    var vertex = 0
    while coincidence[vertex] > 0:
        var next_vertex = -1
        for k in range(len(graph.adj[vertex])):
            var target = graph.adj[vertex][k]
            if coincidence[target] == coincidence[vertex] - 1:
                next_vertex = target
                break
        if next_vertex == -1:
            raise Error("periodic-ray distance has no decreasing edge")
        var digits = _occurrence_digits(tables, graph, cache, vertex, next_vertex)
        top_digits.append(digits[0])
        bottom_digits.append(digits[1])
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
        cyclic.append(_cyclic_first_letter(sigma, a))

    var result = List[PeriodicRayDecision]()
    for a in range(3):
        for b in range(a + 1, 3):
            if cyclic[a] and cyclic[b]:
                result.append(_decide_pair(tables, a, b, max_states))
    return result^


struct ForbiddenHubStart(Copyable, Movable):
    """Shortest addressed distinct aligned start violating the expected hub side."""

    var depth: Int
    var top: Int
    var bottom: Int
    var top_digits: List[Int]
    var bottom_digits: List[Int]

    def __init__(
        out self, depth: Int, top: Int, bottom: Int,
        var top_digits: List[Int], var bottom_digits: List[Int],
    ):
        self.depth = depth
        self.top = top
        self.bottom = bottom
        self.top_digits = top_digits^
        self.bottom_digits = bottom_digits^


def first_forbidden_hub_start(
    sigma: List[List[Int]], hub: Int, top: Int, bottom: Int, phase: Int,
    max_states: Int = 20000,
) raises -> ForbiddenHubStart:
    """Check a phase candidate after verifying the complementary good edge.

    Depth -1 means no forbidden *distinct* aligned start in the complete graph.
    Diagonal productivity and common-vertex gaps are separate tests.
    """
    if hub < 0 or hub >= 3 or top < 0 or top >= 3 or bottom < 0 or bottom >= 3:
        raise Error("periodic-ray letters lie outside 0..2")
    if top == bottom or (top != hub and bottom != hub) or phase < 0 or phase > 1:
        raise Error("invalid cyclic hub pair or phase")
    var tables = build_seed_overlap_tables_screened(sigma)
    if not _cyclic_first_letter(sigma, top) or not _cyclic_first_letter(sigma, bottom):
        raise Error("periodic-ray root must have two cyclic first letters")

    var good = List[Int]()
    for a in range(3):
        if a != hub:
            good.append(a)
    if _decide_pair(tables, good[0], good[1], max_states).coincidence_depth < 0:
        raise Error("complementary good edge needs an actual coincidence witness")

    var seeds: List[OverlapState] = [OverlapState(top, bottom, CubicElt())]
    var cache = Dict[CubicElt, Int]()
    var graph = build_overlap_graph_from_seeds(tables, seeds, cache, max_states)
    if graph.capped:
        raise Error("hub-start reachability is undefined on a capped graph")

    # Pack (overlap index, expected hub side), with 0 for top and 1 for bottom.
    var initial = 0 if top == hub else 1
    var queue: List[Int] = [initial]
    var parent = List[Int]()
    for _ in range(graph.size()):
        parent.append(-1)
        parent.append(-1)
    parent[initial] = initial
    var head = 0
    while head < len(queue):
        var current = queue[head]
        head += 1
        var vertex = current // 2
        var side = current % 2
        var state = graph.states[vertex]
        var actual_hub = state.top if side == 0 else state.bottom
        if state.shift.is_zero() and state.top != state.bottom and actual_hub != hub:
            var top_digits = List[Int]()
            var bottom_digits = List[Int]()
            while current != initial:
                var previous = parent[current]
                var digits = _occurrence_digits(tables, graph, cache, previous // 2, current // 2)
                top_digits.append(digits[0])
                bottom_digits.append(digits[1])
                current = previous
            top_digits.reverse()
            bottom_digits.reverse()
            return ForbiddenHubStart(
                len(top_digits), state.top, state.bottom, top_digits^, bottom_digits^
            )
        var next_side = side ^ phase
        for k in range(len(graph.adj[vertex])):
            var target = 2 * graph.adj[vertex][k] + next_side
            if parent[target] == -1:
                parent[target] = current
                queue.append(target)

    return ForbiddenHubStart(-1, -1, -1, List[Int](), List[Int]())
