"""Literal seam saturation, independent zero-fibre controls, and signed factors."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.fixed_point_count import iterated_map
from psc.one_track_seam_spectrum import (
    BOTH,
    BOTTOM,
    TOP,
    CellBoundaryMasks,
    NeutralSinkSpectrum,
    SeamCycleProfile,
    neutral_spectrum_for_sink,
    odd_unit_multiplicities,
    one_track_seam_cycles,
    overlap_boundary_masks,
)
from psc.periodic_overlap_returns import PeriodicOverlapGraph
from psc.zero_fibre import compare_zero_fibre


def replay_occurrences(graph: PeriodicOverlapGraph, profile: SeamCycleProfile) raises:
    var born = 0
    var inherited = 0
    for i in range(len(profile.occurrences)):
        var pair = profile.occurrences[i]
        if pair.previous < 0:
            ref row = graph.graph.adj[pair.source]
            assert_equal(pair.left, row[pair.ordinal])
            assert_equal(pair.right, row[pair.ordinal + 1])
            var first = graph.occurrence_indices(pair.source, pair.ordinal)
            var second = graph.occurrence_indices(pair.source, pair.ordinal + 1)
            assert_true(first != second)
            born += 1
        else:
            assert_true(pair.previous < i)
            var previous = profile.occurrences[pair.previous]
            ref left_row = graph.graph.adj[previous.left]
            assert_equal(pair.left, left_row[len(left_row) - 1])
            assert_equal(pair.right, graph.graph.adj[previous.right][0])
            inherited += 1
    assert_true(born > 0 and inherited > 0)


def fixed_letters(endpoint: List[Int], power: Int) -> Int:
    var image = iterated_map(endpoint, power)
    var fixed = 0
    for a in range(len(image)):
        fixed += Int(image[a] == a)
    return fixed


def replay_zero_fibre_control(
    sigma: List[List[Int]], expected_first: List[Int], expected_last: List[Int],
    expected_seam: List[Int], plus: Int, minus: Int,
) raises:
    var graph = PeriodicOverlapGraph(sigma)
    assert_equal(graph.aligned_sinks, 0)
    var masks = overlap_boundary_masks(graph.tables, graph.graph.states)
    var profile = one_track_seam_cycles(graph.graph.adj, masks)
    replay_occurrences(graph, profile)
    assert_equal(profile.first, expected_first)
    assert_equal(profile.last, expected_last)
    assert_equal(profile.seam, expected_seam)
    assert_equal(profile.cyclotomic_correction(1), plus)
    assert_equal(profile.cyclotomic_correction(2), minus)
    assert_equal(profile.cyclotomic_correction(3), 0)

    # Independent product check for the productive controls. The source
    # zero-fibre catalogue uses integer centre states and legal bigrams.
    var zero = compare_zero_fibre(sigma)
    assert_true(zero.all_meet_reference())
    var first: List[Int] = [sigma[0][0], sigma[1][0], sigma[2][0]]
    var last = List[Int]()
    for word in sigma:
        last.append(word[len(word) - 1])
    for n in range(1, 13):
        var interior = 0
        var seams = 0
        for patch in zero.patches:
            if n % patch.period == 0:
                interior += Int(patch.before < 0)
                seams += Int(patch.before >= 0)
        var direct: List[Int] = [interior * fixed_letters(first, n), interior * fixed_letters(last, n), interior * seams]
        assert_equal(profile.fixed_counts(n), direct)

    print(sigma, "top-only cycles", profile.first, profile.last, profile.seam,
          "corrections", plus, minus)


def test_refinement() raises:
    # Each letter has two half cells. The middle child of each three-letter
    # word retains its parent's orientation, so the middle cut persists.
    var bigons: List[List[Int]] = [[1, 0, 1], [0, 1, 0]]
    var fine = List[List[Int]]()
    for word in bigons:
        var left = List[Int]()
        var right = List[Int]()
        for i in range(len(word)):
            for half in range(2):
                var cell = 2 * word[i] + half
                if 2 * i + half < len(word):
                    left.append(cell)
                else:
                    right.append(cell)
        fine.append(left^)
        fine.append(right^)
    var masks = CellBoundaryMasks([BOTH, TOP, BOTH, BOTTOM], [TOP, BOTH, BOTTOM, BOTH])
    var overlap = odd_unit_multiplicities(fine, [2, 3, 0, 1])
    var result = NeutralSinkSpectrum(overlap, one_track_seam_cycles(fine, masks))
    var direct = odd_unit_multiplicities(bigons, [1, 0])
    assert_equal([result.overlap.plus, result.overlap.minus], [1, 1])
    assert_equal(result.seams.fixed_counts(1), [1, 1, 1])
    assert_equal([result.correction.plus, result.correction.minus], [-1, 0])
    assert_equal([direct.plus, direct.minus], [0, 1])
    assert_equal([result.bigon.plus, result.bigon.minus], [direct.plus, direct.minus])


def test_algebraic_multiplicity() raises:
    var positive: List[List[Int]] = [[0], [1], [0, 2], [1, 3]]
    var negative: List[List[Int]] = [[1], [0], [0, 3], [1, 2]]
    var swap: List[Int] = [1, 0, 3, 2]
    var p = odd_unit_multiplicities(positive, swap)
    var m = odd_unit_multiplicities(negative, swap)
    assert_equal([p.plus, p.minus], [2, 0])
    assert_equal([m.plus, m.minus], [0, 2])


def test_refusals() raises:
    var graph = PeriodicOverlapGraph([[0, 1], [1, 2], [0, 2, 1]])
    var masks = overlap_boundary_masks(graph.tables, graph.graph.states)
    var refused = False
    try:
        _ = one_track_seam_cycles(graph.graph.adj, masks, 1)
    except e:
        refused = "adjacency cap reached" in String(e)
    assert_true(refused)

    refused = False
    try:
        _ = neutral_spectrum_for_sink(graph, 0)
    except e:
        refused = "expected an aligned nonproductive sink" in String(e)
    assert_true(refused)

    refused = False
    try:
        _ = odd_unit_multiplicities([[0], [1], [2], [3]], [1, 0, 3, 2], 1)
    except e:
        refused = "odd matrix dimension cap reached" in String(e)
    assert_true(refused)

    refused = False
    try:
        _ = one_track_seam_cycles([[1], [1]], CellBoundaryMasks([TOP, BOTTOM], [BOTH, BOTH]))
    except e:
        refused = "inflation lost an existing track boundary" in String(e)
    assert_true(refused)

    refused = False
    try:
        _ = one_track_seam_cycles([[0, 1], [1]], CellBoundaryMasks([BOTH, BOTH], [TOP, TOP]))
    except e:
        refused = "adjacent cells disagree" in String(e)
    assert_true(refused)


def main() raises:
    replay_zero_fibre_control([[0, 1], [1, 2], [0, 2, 1]], [1, 1], [2], [2, 2], -1, 1)
    replay_zero_fibre_control([[1], [0, 2], [2, 0, 2]], [2, 2, 2], [2], [2, 2, 2], -1, -1)
    replay_zero_fibre_control([[1], [2], [0, 2, 1]], [], [], [], 0, 0)
    replay_zero_fibre_control([[0, 1], [0, 2], [0]], [], [], [], 0, 0)
    test_refinement()
    test_algebraic_multiplicity()
    test_refusals()
    require_contract("Literal one-track seams have indexed births or last/first ancestry. Their cycle lists and signed corrections agree with independent periodic zero-fibre controls at powers one through twelve. A productive PIP fixture has positive minus-one correction. A literal subdivision checks the corrected odd algebraic multiplicities against its uncut words, including a surviving minus-one root. Jordan controls distinguish algebraic multiplicity, and caps, bad boundary labels and an ineligible sink refuse.")
