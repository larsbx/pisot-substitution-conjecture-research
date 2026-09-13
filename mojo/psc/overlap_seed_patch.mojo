"""Exact one-dimensional seed-patch overlap graph for G1b-2 diagnostics.

The graph starts from the same two-letter seed superpositions ``(ab, ba)`` used
by the repository balanced-pair automaton.  A state records two tile types and
the exact displacement of the bottom tile start from the top tile start as an
element of ``Z[beta]``.  Inflation is exact in the cubic Perron field.

This is intentionally called a *seed-patch overlap graph*.  It is not yet
identified with the complete realized-overlap graph appearing in the general
overlap-coincidence literature; that realization/dictionary statement remains
a theorem target.  Capped construction is inconclusive.
"""

from psc.bpa import substitution_incidence
from psc.mat3 import Mat3
from psc.perron_field3 import (
    CubicElt,
    PerronField3,
    TileLengths3,
    build_perron_field3,
    cubic_mul_beta,
    left_perron_tile_lengths,
    sign_at_perron,
)


struct OverlapState(ImplicitlyCopyable, Copyable, Movable, Equatable, Hashable, Writable):
    var top: Int
    var bottom: Int
    var shift: CubicElt

    def __init__(out self, top: Int, bottom: Int, shift: CubicElt):
        self.top = top
        self.bottom = bottom
        self.shift = shift

    def __eq__(self, other: OverlapState) -> Bool:
        return self.top == other.top and self.bottom == other.bottom and self.shift == other.shift

    def __ne__(self, other: OverlapState) -> Bool:
        return not (self == other)

    def is_coincidence(self) -> Bool:
        return self.top == self.bottom and self.shift.is_zero()

    def write_to[W: Writer](self, mut w: W):
        w.write("(", self.top, ",", self.bottom, ",", self.shift, ")")


struct SeedOverlapTables(Copyable, Movable):
    var sigma: List[List[Int]]
    var field: PerronField3
    var lengths: TileLengths3
    var prefix_starts: List[Int]
    var prefix_positions: List[CubicElt]

    def __init__(
        out self,
        sigma: List[List[Int]],
        field: PerronField3,
        lengths: TileLengths3,
        prefix_starts: List[Int],
        prefix_positions: List[CubicElt],
    ):
        self.sigma = sigma.copy()
        self.field = field
        self.lengths = lengths
        self.prefix_starts = prefix_starts.copy()
        self.prefix_positions = prefix_positions.copy()

    def prefix(self, parent: Int, child_index: Int) raises -> CubicElt:
        if parent < 0 or parent >= 3:
            raise Error("overlap parent letter lies outside 0..2")
        if child_index < 0 or child_index >= len(self.sigma[parent]):
            raise Error("overlap child index lies outside parent image")
        return self.prefix_positions[self.prefix_starts[parent] + child_index]


struct SeedOverlapAutomaton(Copyable, Movable):
    var states: List[OverlapState]
    var adj: List[List[Int]]
    var capped: Bool

    def __init__(
        out self,
        states: List[OverlapState],
        adj: List[List[Int]],
        capped: Bool,
    ):
        self.states = states.copy()
        self.adj = adj.copy()
        self.capped = capped

    def size(self) -> Int:
        return len(self.states)


def _validate_sigma(sigma: List[List[Int]]) raises:
    if len(sigma) != 3:
        raise Error("seed-patch overlap graph requires three substitution images")
    for a in range(3):
        if len(sigma[a]) == 0:
            raise Error("seed-patch overlap graph requires a non-erasing substitution")
        for j in range(len(sigma[a])):
            if sigma[a][j] < 0 or sigma[a][j] >= 3:
                raise Error("seed-patch overlap letter lies outside 0..2")


def build_seed_overlap_tables(sigma: List[List[Int]]) raises -> SeedOverlapTables:
    _validate_sigma(sigma)
    var m = Mat3(substitution_incidence(sigma))
    var field = build_perron_field3(m)
    var lengths = left_perron_tile_lengths(m)
    var starts: List[Int] = [0]
    var positions = List[CubicElt]()
    for parent in range(3):
        var cursor = CubicElt()
        for j in range(len(sigma[parent])):
            positions.append(cursor)
            cursor = cursor + lengths.at(sigma[parent][j])
        if cursor != cubic_mul_beta(field, lengths.at(parent)):
            raise Error("substitution image length disagrees with Perron scaling")
        starts.append(len(positions))
    return SeedOverlapTables(sigma, field, lengths, starts, positions)


def _cached_sign(
    tables: SeedOverlapTables,
    mut cache: Dict[CubicElt, Int],
    x: CubicElt,
) raises -> Int:
    if x in cache:
        return cache[x]
    var s = sign_at_perron(tables.field, x)
    cache[x] = s
    return s


def _interior_overlap_cached(
    tables: SeedOverlapTables,
    mut cache: Dict[CubicElt, Int],
    state: OverlapState,
) raises -> Bool:
    if state.top < 0 or state.top >= 3 or state.bottom < 0 or state.bottom >= 3:
        raise Error("overlap state tile type lies outside 0..2")
    # Top interval [0,l_top], bottom [shift, shift+l_bottom].
    var right_of_top_start = state.shift + tables.lengths.at(state.bottom)
    var left_of_top_end = state.shift - tables.lengths.at(state.top)
    return (
        _cached_sign(tables, cache, right_of_top_start) > 0
        and _cached_sign(tables, cache, left_of_top_end) < 0
    )


def interior_overlap(tables: SeedOverlapTables, state: OverlapState) raises -> Bool:
    var cache = Dict[CubicElt, Int]()
    return _interior_overlap_cached(tables, cache, state)


def _seed_states_with_cache(
    tables: SeedOverlapTables, mut cache: Dict[CubicElt, Int]
) raises -> List[OverlapState]:
    var out = List[OverlapState]()
    for a in range(3):
        for b in range(a + 1, 3):
            var top_types: List[Int] = [a, b]
            var bottom_types: List[Int] = [b, a]
            var top_starts: List[CubicElt] = [CubicElt(), tables.lengths.at(a)]
            var bottom_starts: List[CubicElt] = [CubicElt(), tables.lengths.at(b)]
            for i in range(2):
                for j in range(2):
                    var state = OverlapState(
                        top_types[i],
                        bottom_types[j],
                        bottom_starts[j] - top_starts[i],
                    )
                    if _interior_overlap_cached(tables, cache, state):
                        out.append(state)
    return out^


def seed_overlap_states(tables: SeedOverlapTables) raises -> List[OverlapState]:
    var cache = Dict[CubicElt, Int]()
    return _seed_states_with_cache(tables, cache)


def _children_with_cache(
    tables: SeedOverlapTables,
    mut cache: Dict[CubicElt, Int],
    state: OverlapState,
) raises -> List[OverlapState]:
    if not _interior_overlap_cached(tables, cache, state):
        raise Error("cannot inflate a non-overlap state")
    var out = List[OverlapState]()
    var scaled_shift = cubic_mul_beta(tables.field, state.shift)
    for i in range(len(tables.sigma[state.top])):
        var top_child = tables.sigma[state.top][i]
        var top_prefix = tables.prefix(state.top, i)
        for j in range(len(tables.sigma[state.bottom])):
            var bottom_child = tables.sigma[state.bottom][j]
            var bottom_prefix = tables.prefix(state.bottom, j)
            var child = OverlapState(
                top_child,
                bottom_child,
                scaled_shift + bottom_prefix - top_prefix,
            )
            if _interior_overlap_cached(tables, cache, child):
                out.append(child)
    return out^


def overlap_children(
    tables: SeedOverlapTables, state: OverlapState
) raises -> List[OverlapState]:
    var cache = Dict[CubicElt, Int]()
    return _children_with_cache(tables, cache, state)


def build_seed_overlap_graph(
    sigma: List[List[Int]], max_states: Int = 20000
) raises -> SeedOverlapAutomaton:
    if max_states <= 0:
        raise Error("seed-patch overlap state cap must be positive")
    var tables = build_seed_overlap_tables(sigma)
    var sign_cache = Dict[CubicElt, Int]()
    var seeds = _seed_states_with_cache(tables, sign_cache)
    var states = List[OverlapState]()
    var adj = List[List[Int]]()
    var index = Dict[OverlapState, Int](capacity=max_states)
    var queue = seeds.copy()
    var capped = False
    var head = 0

    while head < len(queue):
        var state = queue[head]
        head += 1
        if state in index:
            continue
        if len(states) >= max_states:
            capped = True
            break
        index[state] = len(states)
        states.append(state)
        adj.append(List[Int]())
        if state.is_coincidence():
            continue
        var cs = _children_with_cache(tables, sign_cache, state)
        for i in range(len(cs)):
            queue.append(cs[i])

    if capped:
        return SeedOverlapAutomaton(states, adj, True)

    for i in range(len(states)):
        if states[i].is_coincidence():
            continue
        var cs = _children_with_cache(tables, sign_cache, states[i])
        for j in range(len(cs)):
            if cs[j] not in index:
                raise Error("terminated overlap graph lost a reachable child")
            adj[i].append(index[cs[j]])
    return SeedOverlapAutomaton(states, adj, False)


def nonproductive_overlap_states(a: SeedOverlapAutomaton) -> List[Int]:
    """States from which no exact tile coincidence is reachable."""
    var good = List[Bool]()
    for i in range(a.size()):
        good.append(a.states[i].is_coincidence())
    var changed = True
    while changed:
        changed = False
        for i in range(a.size()):
            if good[i]:
                continue
            for j in range(len(a.adj[i])):
                if good[a.adj[i][j]]:
                    good[i] = True
                    changed = True
                    break
    var out = List[Int]()
    for i in range(a.size()):
        if not good[i]:
            out.append(i)
    return out^
