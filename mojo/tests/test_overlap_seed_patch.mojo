"""Exact regressions for the seed-patch overlap diagnostic."""

from std.testing import assert_equal, assert_false, assert_true
from psc.bpa import build, nonproductive_states, substitution_incidence
from psc.mat3 import Mat3
from psc.overlap_seed_patch import (
    build_seed_overlap_graph,
    build_seed_overlap_tables,
    nonproductive_overlap_states,
    seed_overlap_states,
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


def test_canonical_seed_overlap_graph_is_productive() raises:
    var sigma = determinant_two_sigma()
    var tables = build_seed_overlap_tables(sigma)
    var seeds = seed_overlap_states(tables)
    assert_true(len(seeds) > 0)

    var graph = build_seed_overlap_graph(sigma, 20000)
    assert_false(graph.capped)
    assert_true(graph.size() > 0)
    assert_equal(len(nonproductive_overlap_states(graph)), 0)

    # Compare only the finite productivity verdict.  Equality of the two graph
    # constructions is not yet a theorem or asserted by this test.
    var bpa = build(sigma, 20000)
    assert_false(bpa.capped)
    assert_equal(len(nonproductive_states(bpa)), 0)

    print("canonical seed-overlap initial states:", len(seeds))
    print("canonical seed-overlap graph states:", graph.size())


def test_non_pip_substitution_is_rejected() raises:
    var caught = False
    try:
        _ = build_seed_overlap_tables(identity_sigma())
    except:
        caught = True
    assert_true(caught)


def main() raises:
    test_perron_order_is_exact_on_basic_elements()
    print("[PASS] test_perron_order_is_exact_on_basic_elements")
    test_canonical_seed_overlap_graph_is_productive()
    print("[PASS] test_canonical_seed_overlap_graph_is_productive")
    test_non_pip_substitution_is_rejected()
    print("[PASS] test_non_pip_substitution_is_rejected")
    print("3 seed-patch-overlap Mojo tests passed.")
