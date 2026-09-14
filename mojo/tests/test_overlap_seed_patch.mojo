"""Exact regressions for the seed-patch overlap diagnostic."""

from std.testing import assert_equal, assert_false, assert_true
from psc.bpa import build, nonproductive_states, substitution_incidence
from psc.mat3 import Mat3
from psc.overlap_seed_patch import (
    build_seed_overlap_graph,
    first_coincidence_depths,
    first_left_aligned_depths,
    build_seed_overlap_tables,
    nonproductive_overlap_states,
    seed_overlap_states,
    strong_coincidence_depth,
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
    for i in range(len(coinc)):
        assert_true(coinc[i] <= left[i] + prefix)


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
    print("7 seed-patch-overlap Mojo tests passed.")
