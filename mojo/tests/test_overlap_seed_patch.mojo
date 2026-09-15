"""Exact regressions for the seed-patch overlap diagnostic."""

from std.testing import assert_equal, assert_false, assert_true
from psc.bpa import build, nonproductive_states, substitution_incidence
from psc.mat3 import Mat3
from psc.overlap_obstruction import common_child_start_count, nonproductive_sink_sccs
from psc.overlap_seed_patch import (
    OverlapState,
    SeedOverlapAutomaton,
    build_seed_overlap_graph,
    build_seed_overlap_graph_from_tables,
    first_coincidence_depths,
    first_left_aligned_depths,
    build_seed_overlap_tables,
    nonproductive_overlap_states,
    overlap_children,
    seed_overlap_states,
    strong_coincidence_depth,
    strong_coincidence_depth_from,
)
from psc.perron_field3 import CubicElt, build_perron_field3, sign_at_perron


def determinant_two_sigma() -> List[List[Int]]:
    var a0: List[Int] = [1]
    var a1: List[Int] = [0, 2, 1]
    var a2: List[Int] = [0, 0, 1]
    var sigma = List[List[Int]]()
    sigma.append(a0^)
    sigma.append(a1^)
    sigma.append(a2^)
    return sigma^


def identity_sigma() -> List[List[Int]]:
    var a0: List[Int] = [0]
    var a1: List[Int] = [1]
    var a2: List[Int] = [2]
    var sigma = List[List[Int]]()
    sigma.append(a0^)
    sigma.append(a1^)
    sigma.append(a2^)
    return sigma^


def _contains_int(xs: List[Int], x: Int) -> Bool:
    for i in range(len(xs)):
        if xs[i] == x:
            return True
    return False


def test_perron_order_is_exact_on_basic_elements() raises:
    var sigma = determinant_two_sigma()
    var m = Mat3(substitution_incidence(sigma))
    var field = build_perron_field3(m)
    assert_equal(sign_at_perron(field, CubicElt()), 0)
    assert_equal(sign_at_perron(field, CubicElt(1, 0, 0)), 1)
    assert_equal(sign_at_perron(field, CubicElt(-1, 0, 0)), -1)
    assert_equal(sign_at_perron(field, CubicElt(-1, 1, 0)), 1)  # beta - 1

    # Codex review found that rational midpoint isolation could overflow before
    # resolving this near-Perron linear form. The Sturm--Tarski implementation
    # must classify it exactly without denominator growth.
    assert_equal(sign_at_perron(field, CubicElt(-152138, 67035, 0)), -1)


def test_canonical_seed_overlap_graph_is_productive() raises:
    var sigma = determinant_two_sigma()
    var tables = build_seed_overlap_tables(sigma)
    var seeds = seed_overlap_states(tables)
    assert_equal(len(seeds), 9)

    var graph = build_seed_overlap_graph(sigma, 20000)
    assert_false(graph.capped)
    assert_equal(graph.size(), 628)
    assert_equal(len(nonproductive_overlap_states(graph)), 0)
    assert_equal(len(nonproductive_sink_sccs(graph)), 0)

    # Compare only the finite productivity verdict. Equality of the two graph
    # constructions is not yet a theorem or asserted by this test.
    var bpa = build(sigma, 20000)
    assert_false(bpa.capped)
    assert_equal(len(nonproductive_states(bpa)), 0)

    print("canonical seed-overlap initial states:", len(seeds))
    print("canonical seed-overlap graph states:", graph.size())


def test_capped_productivity_query_fails_closed() raises:
    var graph = build_seed_overlap_graph(determinant_two_sigma(), 1)
    assert_true(graph.capped)
    var caught = False
    try:
        _ = nonproductive_overlap_states(graph)
    except:
        caught = True
    assert_true(caught)


def test_non_pip_substitution_is_rejected() raises:
    var caught = False
    try:
        _ = build_seed_overlap_tables(identity_sigma())
    except:
        caught = True
    assert_true(caught)


def test_large_incidence_is_rejected_before_unchecked_pip_arithmetic() raises:
    # This primitive PIP family has characteristic polynomial x^3-n*x^2-1.
    # A large n would overflow the legacy fixed-width primitivity/charpoly
    # predicates.  The overlap kernel must reject it before calling them.
    var large = Mat3([0, 0, 1, 1, 0, 0, 0, 1, Int.MAX])
    var caught = False
    try:
        _ = build_perron_field3(large)
    except:
        caught = True
    assert_true(caught)


def test_first_coincidence_depths_pin_exact_values() raises:
    var graph = build_seed_overlap_graph(determinant_two_sigma(), 20000)
    var depths = first_coincidence_depths(graph)
    assert_equal(len(depths), 628)
    var worst = 0
    var zeros = 0
    for i in range(len(depths)):
        assert_true(depths[i] >= 0)
        if depths[i] > worst:
            worst = depths[i]
        if depths[i] == 0:
            zeros += 1
    assert_equal(worst, 16)
    assert_equal(zeros, 2)


def test_left_aligned_and_strong_coincidence_depths_pin_exact_values() raises:
    var sigma = determinant_two_sigma()
    var graph = build_seed_overlap_graph(sigma, 20000)
    var tables = build_seed_overlap_tables(sigma)
    var left = first_left_aligned_depths(graph)
    var coinc = first_coincidence_depths(graph)
    assert_equal(len(left), 628)
    var worst = 0
    var zeros = 0
    for i in range(len(left)):
        assert_true(left[i] >= 0)
        assert_true(left[i] <= coinc[i])
        if left[i] > worst:
            worst = left[i]
        if left[i] == 0:
            zeros += 1
    assert_equal(worst, 15)
    assert_equal(zeros, 7)
    var prefix = strong_coincidence_depth(graph, tables, False)
    var suffix = strong_coincidence_depth(graph, tables, True)
    assert_equal(prefix, 6)
    assert_equal(suffix, 1)
    assert_equal(strong_coincidence_depth_from(coinc, graph, tables, False), 6)
    assert_equal(strong_coincidence_depth_from(coinc, graph, tables, True), 1)
    var from_tables = build_seed_overlap_graph_from_tables(tables, 20000)
    assert_equal(from_tables.size(), graph.size())
    var capped = build_seed_overlap_graph_from_tables(tables, 1)
    assert_true(capped.capped)
    var fake: List[Int] = [0]
    var caught = False
    try:
        _ = strong_coincidence_depth_from(fake, capped, tables, False)
    except:
        caught = True
    assert_true(caught)
    for i in range(len(coinc)):
        assert_true(coinc[i] <= left[i] + prefix)


def test_common_child_starts_are_exactly_zero_shift_children() raises:
    var sigma = determinant_two_sigma()
    var tables = build_seed_overlap_tables(sigma)
    var graph = build_seed_overlap_graph_from_tables(tables, 20000)
    assert_false(graph.capped)

    for i in range(graph.size()):
        if graph.states[i].is_coincidence():
            continue
        var cs = overlap_children(tables, graph.states[i])
        var zero_shift_children = 0
        for j in range(len(cs)):
            if cs[j].shift.is_zero():
                zero_shift_children += 1
        assert_equal(
            common_child_start_count(tables, graph.states[i]), zero_shift_children
        )


def test_nonproductive_sink_obstruction_is_extracted_exactly() raises:
    # Synthetic complete graph: 0 is a coincidence, 1 reaches it, 2 feeds the
    # closed bad SCC {3,4}.  The obstruction extractor must discard the
    # transient bad vertex 2 and return the recurrent child-closed core.
    var states = List[OverlapState]()
    states.append(OverlapState(0, 0, CubicElt()))
    states.append(OverlapState(0, 1, CubicElt(1, 0, 0)))
    states.append(OverlapState(1, 2, CubicElt(2, 0, 0)))
    states.append(OverlapState(1, 2, CubicElt(3, 0, 0)))
    states.append(OverlapState(2, 0, CubicElt(4, 0, 0)))

    var adj = List[List[Int]]()
    var a0 = List[Int]()
    var a1: List[Int] = [0]
    var a2: List[Int] = [3]
    var a3: List[Int] = [4]
    var a4: List[Int] = [3]
    adj.append(a0^)
    adj.append(a1^)
    adj.append(a2^)
    adj.append(a3^)
    adj.append(a4^)

    var graph = SeedOverlapAutomaton(states, adj, False)
    var bad = nonproductive_overlap_states(graph)
    assert_equal(len(bad), 3)
    assert_true(_contains_int(bad, 2))
    assert_true(_contains_int(bad, 3))
    assert_true(_contains_int(bad, 4))

    var sinks = nonproductive_sink_sccs(graph)
    assert_equal(len(sinks), 1)
    assert_equal(len(sinks[0]), 2)
    assert_true(_contains_int(sinks[0], 3))
    assert_true(_contains_int(sinks[0], 4))
    assert_false(_contains_int(sinks[0], 2))

    var capped = SeedOverlapAutomaton(states, adj, True)
    var caught = False
    try:
        _ = nonproductive_sink_sccs(capped)
    except:
        caught = True
    assert_true(caught)


def main() raises:
    test_perron_order_is_exact_on_basic_elements()
    print("[PASS] test_perron_order_is_exact_on_basic_elements")
    test_canonical_seed_overlap_graph_is_productive()
    print("[PASS] test_canonical_seed_overlap_graph_is_productive")
    test_capped_productivity_query_fails_closed()
    print("[PASS] test_capped_productivity_query_fails_closed")
    test_non_pip_substitution_is_rejected()
    print("[PASS] test_non_pip_substitution_is_rejected")
    test_large_incidence_is_rejected_before_unchecked_pip_arithmetic()
    print("[PASS] test_large_incidence_is_rejected_before_unchecked_pip_arithmetic")
    test_first_coincidence_depths_pin_exact_values()
    print("[PASS] test_first_coincidence_depths_pin_exact_values")
    test_left_aligned_and_strong_coincidence_depths_pin_exact_values()
    print("[PASS] test_left_aligned_and_strong_coincidence_depths_pin_exact_values")
    test_common_child_starts_are_exactly_zero_shift_children()
    print("[PASS] test_common_child_starts_are_exactly_zero_shift_children")
    test_nonproductive_sink_obstruction_is_extracted_exactly()
    print("[PASS] test_nonproductive_sink_obstruction_is_extracted_exactly")
    print("9 seed-patch-overlap Mojo tests passed.")