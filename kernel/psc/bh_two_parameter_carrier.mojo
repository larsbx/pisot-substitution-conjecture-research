"""Exact overlap carriers for particular higher-determinant family members.

Rows retain every ordered pair of image positions with positive common
interior, including rows out of coincidences.
"""
from finite_exact.checked_int import checked_sub
from finite_linear_algebra.mat3 import Mat3
from psc.bpa import substitution_incidence
from psc.occurrence_path import OccurrenceEdge
from psc.overlap_seed_patch import (
    OverlapState, SeedOverlapAutomaton, SeedOverlapTables, _tables_from,
    cached_sign, first_coincidence_depths, first_left_aligned_depths,
    interior_overlap_cached, seed_overlap_states_cached,
)
from psc.perron_field3 import (
    CubicElt, TileLengths3, cubic_add_checked, cubic_mul_beta,
    cubic_sub_checked, screened_perron_field3,
)


struct CarrierEdge(ImplicitlyCopyable, Copyable, Movable):
    var top_index: Int
    var bottom_index: Int
    var target: Int

    def __init__(out self, top_index: Int, bottom_index: Int, target: Int):
        self.top_index = top_index
        self.bottom_index = bottom_index
        self.target = target


struct Carrier(Movable):
    var states: List[OverlapState]
    var rows: List[List[CarrierEdge]]
    var zero_depths: List[Int]
    var coincidence_depths: List[Int]

    def __init__(out self, var states: List[OverlapState], var rows: List[List[CarrierEdge]],
                 var zero_depths: List[Int], var coincidence_depths: List[Int]):
        self.states = states^
        self.rows = rows^
        self.zero_depths = zero_depths^
        self.coincidence_depths = coincidence_depths^


def tables_for(r: Int, k: Int) raises -> SeedOverlapTables:
    if r < 4 or k < r or k > 4096:
        raise Error("expected 4 <= r <= k <= 4096")
    var second: List[Int] = [0]
    for _ in range(k):
        second.append(1)
    second.append(2)
    var third = List[Int]()
    for _ in range(r):
        third.append(0)
    third.append(1)
    var sigma: List[List[Int]] = [[1], second^, third^]
    var field = screened_perron_field3(Mat3(substitution_incidence(sigma)))
    # (beta, beta^2, beta+r) encodes all three integral coordinates injectively.
    return _tables_from(
        sigma, field, TileLengths3(CubicElt(0, 1), CubicElt(0, 0, 1), CubicElt(r, 1))
    )


def parikh_difference(r: Int, shift: CubicElt) raises -> CubicElt:
    """Decode native bottom-minus-top shift to Lean top-minus-bottom counts."""
    if r <= 0 or shift.a0 % r != 0:
        raise Error("packet shift lies outside the full integral prefix lattice")
    var bottom_minus_top_2 = shift.a0 // r
    return CubicElt(
        checked_sub(bottom_minus_top_2, shift.a1),
        checked_sub(0, shift.a2),
        checked_sub(0, bottom_minus_top_2),
    )


def _children(tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int],
              parent: OverlapState) raises -> List[OccurrenceEdge]:
    var out = List[OccurrenceEdge]()
    var shift = cubic_mul_beta(tables.field, parent.shift)
    var i = 0
    var j = 0
    # Advance the interval with the earlier end. An equal end advances both
    # since a tile beginning there can only touch the discarded tile.
    while i < len(tables.sigma[parent.top]) and j < len(tables.sigma[parent.bottom]):
        var a = tables.sigma[parent.top][i]
        var b = tables.sigma[parent.bottom][j]
        var child_shift = cubic_sub_checked(
            cubic_add_checked(shift, tables.prefix(parent.bottom, j)),
            tables.prefix(parent.top, i),
        )
        var child = OverlapState(a, b, child_shift)
        if interior_overlap_cached(tables, signs, child):
            out.append(OccurrenceEdge(parent, i, j, child))
        var end_difference = cubic_sub_checked(
            cubic_add_checked(child_shift, tables.lengths.at(b)), tables.lengths.at(a)
        )
        var order = cached_sign(tables, signs, end_difference)
        if order >= 0:
            i += 1
        if order <= 0:
            j += 1
    return out^


def build_carrier(r: Int, k: Int, max_states: Int, max_edges: Int) raises -> Carrier:
    """Close the union of all three ordered swaps ab/ba for a<b."""
    if max_states < 1 or max_edges < 0:
        raise Error("invalid overlap carrier budgets")
    var tables = tables_for(r, k)
    var signs = Dict[CubicElt, Int]()
    var states = List[OverlapState]()
    var ids = Dict[OverlapState, Int]()
    for seed in seed_overlap_states_cached(tables, signs):
        if seed not in ids:
            if len(states) == max_states:
                raise Error("BH state cap reached; no verdict")
            ids[seed] = len(states)
            states.append(seed)
    var rows = List[List[CarrierEdge]]()
    var adjacency = List[List[Int]]()
    var count = 0
    var head = 0
    while head < len(states):
        var row = List[CarrierEdge]()
        var adj = List[Int]()
        for edge in _children(tables, signs, states[head]):
            if count == max_edges:
                raise Error("BH occurrence cap reached; no verdict")
            count += 1
            if edge.target not in ids:
                if len(states) == max_states:
                    raise Error("BH state cap reached; no verdict")
                ids[edge.target] = len(states)
                states.append(edge.target)
            var dest = ids[edge.target]
            row.append(CarrierEdge(edge.top_index, edge.bottom_index, dest))
            adj.append(dest)
        rows.append(row^)
        adjacency.append(adj^)
        head += 1
    var graph = SeedOverlapAutomaton(states, adjacency, False)
    var zero = first_left_aligned_depths(graph)
    var diag = first_coincidence_depths(graph)
    return Carrier(states^, rows^, zero^, diag^)


def _verify_ranks(carrier: Carrier, ranks: List[Int], labelled: Bool) raises -> Int:
    if len(ranks) != len(carrier.states):
        raise Error("incomplete hit ranks")
    var depth = 0
    for i in range(len(carrier.states)):
        var state = carrier.states[i]
        var target = state.is_coincidence() if labelled else state.shift.is_zero()
        var rank = ranks[i]
        if rank < 0 or (rank == 0) != target:
            raise Error("rank is undefined or marks a false endpoint")
        if target:
            continue
        var descends = False
        for edge in carrier.rows[i]:
            var child_rank = ranks[edge.target]
            if child_rank < rank - 1:
                raise Error("claimed shortest depth has a shorter literal exit")
            if child_rank == rank - 1:
                descends = True
        if not descends:
            raise Error("rank has no literal descending child")
        depth = max(depth, rank)
    return depth


def verify_carrier(r: Int, k: Int, carrier: Carrier) raises -> Tuple[Int, Int, Int]:
    """Check complete occurrence rows and both shortest hit ranks."""
    var tables = tables_for(r, k)
    if len(carrier.rows) != len(carrier.states):
        raise Error("incomplete literal rows")
    var signs = Dict[CubicElt, Int]()
    var ids = Dict[OverlapState, Int]()
    for i in range(len(carrier.states)):
        var state = carrier.states[i]
        _ = parikh_difference(r, state.shift)
        if not interior_overlap_cached(tables, signs, state) or state in ids:
            raise Error("carrier has a non-strict or duplicate packet")
        ids[state] = i
    for root in seed_overlap_states_cached(tables, signs):
        if root not in ids:
            raise Error("carrier omits an actual seed overlap")
    var count = 0
    for i in range(len(carrier.states)):
        var literal = _children(tables, signs, carrier.states[i])
        if len(literal) != len(carrier.rows[i]):
            raise Error("row omits or adds literal occurrences")
        for j in range(len(literal)):
            var edge = carrier.rows[i][j]
            var expected = literal[j]
            if edge.target < 0 or edge.target >= len(carrier.states):
                raise Error("literal edge leaves its carrier")
            if edge.top_index != expected.top_index or edge.bottom_index != expected.bottom_index:
                raise Error("literal edge has the wrong ordered digits")
            if carrier.states[edge.target] != expected.target:
                raise Error("literal edge changes the target packet")
        count += len(literal)
    return (count, _verify_ranks(carrier, carrier.zero_depths, False),
            _verify_ranks(carrier, carrier.coincidence_depths, True))
