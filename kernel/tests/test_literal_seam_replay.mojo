"""Compare literal word returns with full canonical endpoint and seam identities."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.c4_geometric_f import PrototileState
from psc.literal_seam_replay import (
    LiteralEndpointReturn,
    LiteralSeamInventory,
    LiteralSeamReturn,
    literal_one_track_returns,
    replay_bigram,
    replay_endpoint_return,
    replay_interior_return,
    replay_seam_return,
)
from psc.one_track_seam_spectrum import (
    TOP,
    CellBoundaryMasks,
    SeamCycleProfile,
    one_track_seam_cycles,
    overlap_boundary_masks,
)
from psc.overlap_seed_patch import OverlapState
from psc.periodic_overlap_returns import PeriodicOverlapGraph
from psc.perron_field3 import CubicElt
from psc.zero_fibre import ZeroFibreComparison, compare_zero_fibre


struct OrderedCells(ImplicitlyCopyable, Copyable, Movable, Equatable, Hashable):
    var left: OverlapState
    var right: OverlapState

    def __init__(out self, left: OverlapState, right: OverlapState):
        self.left = left
        self.right = right

    def __eq__(self, other: OrderedCells) -> Bool:
        return self.left == other.left and self.right == other.right

    def __ne__(self, other: OrderedCells) -> Bool:
        return not (self == other)


def endpoint_fixed(
    graph: PeriodicOverlapGraph, masks: CellBoundaryMasks,
    root: Int, power: Int, right: Bool,
) -> Bool:
    var v = root
    for _ in range(power):
        var mask = masks.right[v] if right else masks.left[v]
        if mask != TOP:
            return False
        ref row = graph.graph.adj[v]
        if len(row) == 0:
            return False
        v = row[len(row) - 1 if right else 0]
    return v == root


def expected_endpoints(
    graph: PeriodicOverlapGraph, masks: CellBoundaryMasks,
    power: Int, right: Bool,
) raises -> Dict[OverlapState, Bool]:
    var expected = Dict[OverlapState, Bool]()
    for v in range(graph.graph.size()):
        if endpoint_fixed(graph, masks, v, power, right):
            var cell = graph.graph.states[v]
            assert_true(cell not in expected)
            expected[cell] = True
    return expected^


def expected_seams(
    graph: PeriodicOverlapGraph, masks: CellBoundaryMasks,
    profile: SeamCycleProfile, power: Int,
) raises -> Dict[OrderedCells, Bool]:
    var expected = Dict[OrderedCells, Bool]()
    for occurrence in profile.occurrences:
        if endpoint_fixed(graph, masks, occurrence.left, power, True) and (
            endpoint_fixed(graph, masks, occurrence.right, power, False)
        ):
            var pair = OrderedCells(
                graph.graph.states[occurrence.left], graph.graph.states[occurrence.right],
            )
            assert_true(pair not in expected)
            expected[pair] = True
    return expected^


def compare_endpoint_identities(
    records: List[LiteralEndpointReturn], expected: Dict[OverlapState, Bool],
) raises:
    if len(records) != len(expected):
        raise Error("literal seam test: endpoint population size differs")
    var seen = Dict[OverlapState, Bool]()
    for record in records:
        if record.cell in seen:
            raise Error("literal seam test: duplicate endpoint identity")
        if record.cell not in expected:
            raise Error("literal seam test: endpoint identity differs")
        seen[record.cell] = True


def compare_seam_identities(
    records: List[LiteralSeamReturn], expected: Dict[OrderedCells, Bool],
) raises:
    if len(records) != len(expected):
        raise Error("literal seam test: seam population size differs")
    var seen = Dict[OrderedCells, Bool]()
    for record in records:
        var pair = OrderedCells(record.left, record.right)
        if pair in seen:
            raise Error("literal seam test: duplicate ordered seam identity")
        if pair not in expected:
            raise Error("literal seam test: ordered seam identity differs")
        seen[pair] = True


def compare_interior_identities(
    inventory: LiteralSeamInventory, zero: ZeroFibreComparison,
) raises:
    var expected = Dict[PrototileState, Bool]()
    for patch in zero.patches:
        if patch.before < 0 and inventory.power % patch.period == 0:
            assert_true(patch.cut not in expected)
            expected[patch.cut] = True
    assert_equal(len(inventory.interiors), len(expected))
    var seen = Dict[PrototileState, Bool]()
    for record in inventory.interiors:
        assert_true(record.state not in seen)
        assert_true(record.state in expected)
        seen[record.state] = True


def replay_fixture(sigma: List[List[Int]]) raises -> Int:
    var graph = PeriodicOverlapGraph(sigma)
    assert_equal(graph.aligned_sinks, 0)
    var masks = overlap_boundary_masks(graph.tables, graph.graph.states)
    var profile = one_track_seam_cycles(graph.graph.adj, masks)
    var zero = compare_zero_fibre(sigma)
    assert_true(zero.all_meet_reference())
    var nonempty = 0
    for power in range(1, 13):
        var inventory = literal_one_track_returns(sigma, power)
        assert_equal(inventory.power, power)
        for record in inventory.interiors:
            replay_interior_return(inventory.images, record)
        for record in inventory.bigrams:
            replay_bigram(sigma, record)
        for record in inventory.first:
            replay_endpoint_return(
                graph.tables, inventory.images, inventory.interiors[record.interior], record, False,
            )
        for record in inventory.last:
            replay_endpoint_return(
                graph.tables, inventory.images, inventory.interiors[record.interior], record, True,
            )
        for record in inventory.seams:
            replay_seam_return(
                graph.tables, inventory.images, inventory.interiors, inventory.bigrams, record,
            )
        var first = expected_endpoints(graph, masks, power, False)
        var last = expected_endpoints(graph, masks, power, True)
        var seams = expected_seams(graph, masks, profile, power)
        compare_endpoint_identities(inventory.first, first)
        compare_endpoint_identities(inventory.last, last)
        compare_seam_identities(inventory.seams, seams)
        compare_interior_identities(inventory, zero)
        assert_equal(inventory.fixed_counts(), [len(first), len(last), len(seams)])
        assert_equal(inventory.fixed_counts(), profile.fixed_counts(power))
        nonempty += Int(len(seams) > 0)
    print(sigma, "literal identity comparisons", 12, "nonempty seam powers", nonempty)
    return nonempty


def test_identity_mutations() raises:
    var sigma: List[List[Int]] = [[0, 1], [1, 2], [0, 2, 1]]
    var graph = PeriodicOverlapGraph(sigma)
    var masks = overlap_boundary_masks(graph.tables, graph.graph.states)
    var profile = one_track_seam_cycles(graph.graph.adj, masks)
    var inventory = literal_one_track_returns(sigma, 2)
    var first = expected_endpoints(graph, masks, 2, False)
    var seams = expected_seams(graph, masks, profile, 2)
    compare_endpoint_identities(inventory.first, first)
    compare_seam_identities(inventory.seams, seams)
    assert_true(len(inventory.first) >= 2)
    assert_true(len(inventory.seams) >= 2)

    # Same population length; change one exact labelled offset to an
    # independently valid box state absent from the expected first ends.
    var wrong = inventory.first.copy()
    var changed = False
    for cell in graph.graph.states:
        if cell not in first:
            wrong[0].cell = cell
            changed = True
            break
    assert_true(changed)
    assert_equal(len(wrong), len(inventory.first))
    var refused = False
    try:
        compare_endpoint_identities(wrong, first)
    except e:
        refused = "endpoint identity differs" in String(e)
    assert_true(refused)

    wrong = inventory.first.copy()
    wrong[1].cell = wrong[0].cell
    refused = False
    try:
        compare_endpoint_identities(wrong, first)
    except e:
        refused = "duplicate endpoint identity" in String(e)
    assert_true(refused)

    var reversed = inventory.seams.copy()
    var saved_left = reversed[0].left
    reversed[0].left = reversed[0].right
    reversed[0].right = saved_left
    assert_equal(len(reversed), len(inventory.seams))
    refused = False
    try:
        compare_seam_identities(reversed, seams)
    except e:
        refused = "ordered seam identity differs" in String(e)
    assert_true(refused)
    refused = False
    try:
        replay_seam_return(
            graph.tables, inventory.images, inventory.interiors, inventory.bigrams, reversed[0],
        )
    except e:
        refused = True
    assert_true(refused)

    var duplicate = inventory.seams.copy()
    duplicate[1] = duplicate[0]
    refused = False
    try:
        compare_seam_identities(duplicate, seams)
    except e:
        refused = "duplicate ordered seam identity" in String(e)
    assert_true(refused)


def test_occurrence_mutations() raises:
    var sigma: List[List[Int]] = [[0, 1], [1, 2], [0, 2, 1]]
    var graph = PeriodicOverlapGraph(sigma)
    var inventory = literal_one_track_returns(sigma, 4)
    assert_true(len(inventory.interiors) > 0)
    var original = inventory.interiors[0].copy()
    replay_interior_return(inventory.images, original)

    var wrong_prefix = original.copy()
    wrong_prefix.prefix[0] += 1
    var refused = False
    try:
        replay_interior_return(inventory.images, wrong_prefix)
    except e:
        refused = True
    assert_true(refused)

    # Keep the selected letter and its original prefix vector. Another
    # occurrence of that same letter must not stand for this occurrence.
    var wrong_ordinal = original.copy()
    ref word = inventory.images[original.state.letter]
    var replaced = False
    for ordinal in range(1, len(word) - 1):
        if ordinal != original.ordinal and word[ordinal] == original.state.letter:
            wrong_ordinal.ordinal = ordinal
            replaced = True
            break
    assert_true(replaced)
    assert_equal(word[wrong_ordinal.ordinal], word[original.ordinal])
    refused = False
    try:
        replay_interior_return(inventory.images, wrong_ordinal)
    except e:
        refused = True
    assert_true(refused)

    assert_true(len(inventory.first) > 0)
    var shared = inventory.first[0]
    shared.cell = OverlapState(shared.cell.top, shared.cell.bottom, CubicElt())
    refused = False
    try:
        replay_endpoint_return(
            graph.tables, inventory.images, inventory.interiors[shared.interior], shared, False,
        )
    except e:
        refused = True
    assert_true(refused)

    var wrong_endpoint = inventory.first[0]
    wrong_endpoint.top_ordinal += 1
    refused = False
    try:
        replay_endpoint_return(
            graph.tables, inventory.images, inventory.interiors[wrong_endpoint.interior], wrong_endpoint, False,
        )
    except e:
        refused = True
    assert_true(refused)

    assert_true(len(inventory.bigrams) > 0)
    var illegal = inventory.bigrams[0]
    illegal.left = 2
    illegal.right = 2
    # No original image starts in 2, and 22 is internal to none of them.
    # Its purported witness is therefore not a legal adjacency.
    refused = False
    try:
        replay_bigram(sigma, illegal)
    except e:
        refused = True
    assert_true(refused)


def test_budgets() raises:
    var sigma: List[List[Int]] = [[0, 1], [1, 2], [0, 2, 1]]
    var refused = False
    # This upper guard makes the determinant/adjugate bound valid, including
    # nonintegral misses. A larger budget must never silently weaken it.
    try:
        _ = literal_one_track_returns(sigma, 2, word_cap=100001)
    except e:
        refused = "arithmetic scope refused" in String(e)
    assert_true(refused)
    refused = False
    try:
        _ = literal_one_track_returns(sigma, 2, word_cap=1)
    except e:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = literal_one_track_returns(sigma, 2, max_records=1)
    except e:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = literal_one_track_returns(sigma, 0)
    except e:
        refused = True
    assert_true(refused)


def main() raises:
    var nonempty = replay_fixture([[0, 1], [1, 2], [0, 2, 1]])
    nonempty += replay_fixture([[1], [0, 2], [2, 0, 2]])
    nonempty += replay_fixture([[1], [2], [0, 2, 1]])
    nonempty += replay_fixture([[0, 1], [0, 2], [0]])
    assert_true(nonempty > 0)
    test_identity_mutations()
    test_occurrence_mutations()
    test_budgets()
    require_contract("For four declared unit PIP3 productive full boxes and powers one through twelve, literal word self-occurrences recover the same exact integral interior states, first endpoint cells, last endpoint cells and ordered top-only seam pairs as the independent canonical maps. Each population is duplicate-free and every literal occurrence and legal bigram witness replays. Equal-size identity replacement, duplicate identities, reversed seams, changed prefixes, same-letter ordinal substitution, shared boundaries, altered endpoint ordinals, illegal bigrams and exhausted budgets refuse. This finite comparison supplies neither a strict sink nor a uniform neutral-spectrum exclusion.")
