"""Finite actual marks and Perron-scaled interior successors: literal controls.

The four ordered states below are a genuine strict non-PIP carrier. These
small integer-length assertions reuse canonical reduction, prefix residual,
derived-system and occurrence-packet implementations. Test-local interval
arithmetic is not a second packet constructor or a PIP length-field builder.
"""

from std.testing import assert_equal, assert_true, assert_false
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution, build, coincidence_boundaries, decompose
from psc.derived_system import build_derived_system
from psc.hierarchy_offset import prefix_difference3
from psc.target_packets import build_packets, make_root, descendant, verify_packet
from psc.words import Pair


def _weighted_prefix(word: List[Int], end: Int, lengths: List[Int]) -> Int:
    var total = 0
    for k in range(end):
        total += lengths[word[k]]
    return total


def _geometric_interior(
    top: List[Int], bottom: List[Int], i: Int, j: Int, lengths: List[Int],
) -> Bool:
    return (
        _weighted_prefix(top, i, lengths) < _weighted_prefix(bottom, j + 1, lengths)
        and _weighted_prefix(bottom, j, lengths) < _weighted_prefix(top, i + 1, lengths)
    )


def _image_start(sigma: List[List[Int]], word: List[Int], i: Int) -> Int:
    var start = 0
    for k in range(i):
        start += len(sigma[word[k]])
    return start


def _factor_ordinal(cuts: List[Int], position: Int) raises -> Int:
    for k in range(len(cuts) - 1):
        if cuts[k] <= position and position < cuts[k + 1]:
            return k
    raise Error("test position lies outside complete factorization")


def _packet_label(top: List[Int], bottom: List[Int], i: Int, j: Int) raises -> List[Int]:
    var residual = prefix_difference3(top, bottom, i, j)
    return [top[i], bottom[j], residual.x, residual.y, residual.z]


def _append_distinct(mut labels: List[List[Int]], label: List[Int]):
    for k in range(len(labels)):
        if labels[k] == label:
            return
    labels.append(label.copy())


def test_all_actual_strict_marks_have_scaled_interior_successors() raises:
    var sigma: List[List[Int]] = [[1], [0, 1, 2], [1]]
    var lengths: List[Int] = [1, 2, 1]
    var normalized: List[Pair] = [Pair([0, 1], [1, 0]), Pair([1, 2], [2, 1])]
    var system = build_derived_system(sigma, normalized)
    assert_equal(system.size(), 2)
    assert_equal(system.images[0], [0, 1])
    assert_equal(system.images[1], [0, 1])
    assert_equal(system.child_signs[0], [-1, 1])
    assert_equal(system.child_signs[1], [1, -1])
    for a in range(3):
        assert_true(lengths[a] > 0)
        assert_equal(_weighted_prefix(sigma[a], len(sigma[a]), lengths), 2 * lengths[a])

    var carrier: List[Pair] = [
        Pair([0, 1], [1, 0]), Pair([1, 0], [0, 1]),
        Pair([1, 2], [2, 1]), Pair([2, 1], [1, 2]),
    ]
    var packets = List[List[Int]]()
    var interior_packets = List[List[Int]]()
    var indexed_marks = 0
    var interior_marks = 0
    for c in range(len(carrier)):
        var source = carrier[c].copy()
        assert_equal(coincidence_boundaries(source.u, source.v), [0, 2])
        var top = apply_substitution(sigma, source.u)
        var bottom = apply_substitution(sigma, source.v)
        var cuts = coincidence_boundaries(top, bottom)
        var children = decompose(top, bottom)
        assert_equal(len(children), 2)
        for k in range(len(children)):
            var contained = False
            for t in range(len(carrier)):
                if children[k] == carrier[t]:
                    contained = True
            assert_true(contained)
            assert_false(children[k].is_coincidence())
        for i in range(len(source.u)):
            for j in range(len(source.v)):
                indexed_marks += 1
                var label = _packet_label(source.u, source.v, i, j)
                _append_distinct(packets, label)
                if not _geometric_interior(source.u, source.v, i, j, lengths):
                    continue
                interior_marks += 1
                _append_distinct(interior_packets, label)
                assert_false(label[0] == label[1] and label[2] == 0 and label[3] == 0 and label[4] == 0)
                var successors = 0
                for p in range(len(sigma[source.u[i]])):
                    for q in range(len(sigma[source.v[j]])):
                        var ti = _image_start(sigma, source.u, i) + p
                        var bi = _image_start(sigma, source.v, j) + q
                        if not _geometric_interior(top, bottom, ti, bi, lengths):
                            continue
                        successors += 1
                        var ordinal = _factor_ordinal(cuts, ti)
                        assert_equal(ordinal, _factor_ordinal(cuts, bi))
                        var li = ti - cuts[ordinal]
                        var lj = bi - cuts[ordinal]
                        var child = children[ordinal].copy()
                        assert_true(_geometric_interior(child.u, child.v, li, lj, lengths))
                        assert_equal(_packet_label(top, bottom, ti, bi), _packet_label(child.u, child.v, li, lj))
                assert_true(successors > 0)
    assert_equal(indexed_marks, 16)
    assert_equal(len(packets), 16)
    assert_equal(interior_marks, 12)
    assert_equal(len(interior_packets), 12)


def test_packet_support_does_not_count_occurrences() raises:
    # This reducible diagonal pair is a separate finite-support control, not
    # a strict carrier member. Two different marks have the same zero packet.
    var word: List[Int] = [0, 0]
    var labels = List[List[Int]]()
    var interior_labels = List[List[Int]]()
    var marks = 0
    for i in range(2):
        for j in range(2):
            marks += 1
            var label = _packet_label(word, word, i, j)
            _append_distinct(labels, label)
            if _geometric_interior(word, word, i, j, [1, 2, 1]):
                _append_distinct(interior_labels, label)
    assert_equal(marks, 4)
    assert_equal(len(labels), 3)
    assert_equal(len(interior_labels), 1)
    assert_equal(_packet_label(word, word, 0, 0), _packet_label(word, word, 1, 1))


def test_positive_wrong_row_can_have_no_interior_successor() raises:
    var sigma: List[List[Int]] = [[1], [0, 1, 2], [1]]
    var lengths: List[Int] = [2, 1, 1]
    var source = Pair([0, 1], [1, 0])
    for a in range(3):
        assert_true(lengths[a] > 0)
    assert_true(_geometric_interior(source.u, source.v, 0, 1, lengths))
    assert_equal(_weighted_prefix(source.u, 0, lengths), 0)
    assert_equal(_weighted_prefix(source.u, 1, lengths), 2)
    assert_equal(_weighted_prefix(source.v, 1, lengths), 1)
    assert_equal(_weighted_prefix(source.v, 2, lengths), 3)
    assert_true(_weighted_prefix(sigma[0], len(sigma[0]), lengths) != 2 * lengths[0])
    # The only valid digit pair is (0,0), so this is an actual dead end.
    assert_equal(len(sigma[source.u[0]]), 1)
    assert_equal(len(sigma[source.v[1]]), 1)
    var top = apply_substitution(sigma, source.u)
    var bottom = apply_substitution(sigma, source.v)
    assert_equal(top, [1, 0, 1, 2])
    assert_equal(bottom, [0, 1, 2, 1])
    assert_equal(_image_start(sigma, source.u, 0), 0)
    assert_equal(_image_start(sigma, source.v, 1), 3)
    assert_equal(_weighted_prefix(top, 0, lengths), 0)
    assert_equal(_weighted_prefix(top, 1, lengths), 1)
    assert_equal(_weighted_prefix(bottom, 3, lengths), 4)
    assert_equal(_weighted_prefix(bottom, 4, lengths), 5)
    assert_false(_geometric_interior(top, bottom, 0, 3, lengths))
    var cuts = coincidence_boundaries(top, bottom)
    assert_equal(cuts, [0, 2, 4])
    assert_true(_factor_ordinal(cuts, 0) != _factor_ordinal(cuts, 3))

    # The production constructor independently rejects these actual split
    # descendants. It receives the complete swap-seeded BPA, not an invented
    # automaton containing just the supplied strict subcomponent.
    var graph = build_packets(sigma, build(sigma))
    var state = -1
    for s in range(graph.bpa.size()):
        if graph.bpa.states[s] == source:
            state = s
    assert_true(state >= 0)
    var marked = make_root(graph, state, 0, 1)
    assert_equal(marked.residual.x, 0)
    assert_equal(marked.residual.y, -1)
    assert_equal(marked.residual.z, 0)
    var rejected = False
    try:
        _ = descendant(graph, marked, 0, 0)
    except:
        rejected = True
    assert_true(rejected)


def test_actual_cycle_and_boundary_predicates_stay_distinct() raises:
    var sigma: List[List[Int]] = [[1], [0, 1, 2], [1]]
    var graph = build_packets(sigma, build(sigma))
    var source = Pair([0, 1], [1, 0])
    var state = -1
    for s in range(graph.bpa.size()):
        if graph.bpa.states[s] == source:
            state = s
    assert_true(state >= 0)
    var root = make_root(graph, state, 0, 0)
    var first = descendant(graph, root, 0, 0)
    var second = descendant(graph, first, 0, 0)
    assert_true(verify_packet(graph, first))
    assert_true(verify_packet(graph, second))
    assert_equal(first.key.state_id, state)
    assert_equal(first.key.sign, -1)
    assert_equal(first.top_letter, 1)
    assert_equal(first.bottom_letter, 0)
    assert_equal(second.key.state_id, state)
    assert_equal(second.key.sign, 1)
    assert_equal(second.top_letter, 0)
    assert_equal(second.bottom_letter, 1)
    assert_equal(graph.factors[first.key.factor_edge].ordinal, 0)
    assert_equal(graph.factors[second.key.factor_edge].ordinal, 0)
    assert_true(root.residual.is_zero())
    assert_true(first.residual.is_zero())
    assert_true(second.residual.is_zero())
    assert_true(_geometric_interior(source.u, source.v, 0, 0, [1, 2, 1]))
    assert_true(_geometric_interior(source.v, source.u, 0, 0, [1, 2, 1]))
    # Native `interior` means an interior LEFT FACTOR BOUNDARY. Both selected
    # child occurrences are at the exterior start but geometrically overlap.
    assert_false(root.interior)
    assert_false(first.interior)
    assert_false(second.interior)
    assert_false(first.success)
    assert_false(second.success)

    var word: List[Int] = [0, 1]
    var lengths: List[Int] = [1, 2, 1]
    assert_equal(_weighted_prefix(word, 1, lengths), 1)
    assert_false(_geometric_interior(word, word, 0, 1, lengths))
    var cuts = coincidence_boundaries(word, word)
    assert_equal(cuts, [0, 1, 2])
    assert_true(_factor_ordinal(cuts, 0) != _factor_ordinal(cuts, 1))


def main() raises:
    test_all_actual_strict_marks_have_scaled_interior_successors()
    test_packet_support_does_not_count_occurrences()
    test_positive_wrong_row_can_have_no_interior_successor()
    test_actual_cycle_and_boundary_predicates_stay_distinct()
    print("C4 finite actual mark and Perron-scaled interior successor controls passed.")
    require_contract("four actual ordered strict non-PIP states have sixteen indexed packets and twelve geometric interior marks with Perron-scaled successors; wrong positive row, packet multiplicity, boundary touch and literal nonproductive cycle preserve the hypothesis and realization boundaries")
