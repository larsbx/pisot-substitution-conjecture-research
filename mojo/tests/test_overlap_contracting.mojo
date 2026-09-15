"""Exact regressions for the contracting lower bound (manuscript Proposition 5.42)."""

from std.testing import assert_equal, assert_true
from finite_exact.rat_q import Q
from psc.exact import q_int, q_poly
from psc.overlap_contracting import ContractingBound, digit_set, discriminant, field_norm
from psc.overlap_seed_patch import (
    build_seed_overlap_graph_from_tables,
    build_seed_overlap_tables,
    first_left_aligned_depths,
)
from psc.perron_field3 import CubicElt
from psc.real_root_sign import count_real_roots, isolate_real_roots, sign_at_isolated_root, tarski_query


def make_sigma(w0: List[Int], w1: List[Int], w2: List[Int]) -> List[List[Int]]:
    var sigma = List[List[Int]]()
    sigma.append(w0.copy())
    sigma.append(w1.copy())
    sigma.append(w2.copy())
    return sigma^


def tau_sigma() -> List[List[Int]]:
    var a0: List[Int] = [1]
    var a1: List[Int] = [0, 2, 1]
    var a2: List[Int] = [0, 0, 1]
    return make_sigma(a0, a1, a2)


def tribonacci_sigma() -> List[List[Int]]:
    var a0: List[Int] = [0, 1]
    var a1: List[Int] = [0, 2]
    var a2: List[Int] = [0]
    return make_sigma(a0, a1, a2)


def totally_real_sigma() -> List[List[Int]]:
    var a0: List[Int] = [1]
    var a1: List[Int] = [0, 2]
    var a2: List[Int] = [0, 2, 2]
    return make_sigma(a0, a1, a2)


def test_sturm_tarski_counts_and_signs() raises:
    # x^2 - 2: roots +-sqrt2; count in (-2, 2) is 2, in (0, 2) is 1; sign of x at the positive root is +1
    var p: List[Int] = [-2, 0, 1]
    var P = q_poly(p)
    assert_equal(count_real_roots(P, q_int(-2), q_int(2)), 2)
    assert_equal(count_real_roots(P, q_int(0), q_int(2)), 1)
    var x: List[Int] = [0, 1]
    assert_equal(sign_at_isolated_root(P, q_poly(x), q_int(0), q_int(2)), 1)
    assert_equal(sign_at_isolated_root(P, q_poly(x), q_int(-2), q_int(0)), -1)
    var boxes = isolate_real_roots(P, q_int(-2), q_int(2), 2)
    assert_equal(len(boxes), 2)
    # x^2 - 3 at the positive root of x^2 - 2 is negative
    var y: List[Int] = [-3, 0, 1]
    assert_equal(sign_at_isolated_root(P, q_poly(y), q_int(0), q_int(2)), -1)


def check_bound(sigma: List[List[Int]], expect_complex: Bool, expect_max_m0: Int) raises:
    var tables = build_seed_overlap_tables(sigma)
    var graph = build_seed_overlap_graph_from_tables(tables, 20000)
    var cb = ContractingBound(tables)
    assert_equal(cb.is_complex, expect_complex)
    assert_equal(discriminant(tables.field) < 0, expect_complex)
    assert_true(field_norm(tables.field, CubicElt(0, 1, 0)).eq(q_int(-tables.field.chi0)))
    var left = first_left_aligned_depths(graph)
    var worst = 0
    for i in range(graph.size()):
        var m0 = cb.least_level(graph, graph.states[i].shift)
        assert_true(m0 >= 0)
        assert_true(m0 <= left[i])
        assert_equal(m0 == 0, graph.states[i].shift.is_zero())
        if m0 > worst:
            worst = m0
    assert_equal(worst, expect_max_m0)


def test_bound_pins_exact_values() raises:
    check_bound(tribonacci_sigma(), True, 2)
    check_bound(tau_sigma(), True, 4)
    check_bound(totally_real_sigma(), False, 2)


def test_capped_graph_is_rejected() raises:
    var tables = build_seed_overlap_tables(tau_sigma())
    var capped = build_seed_overlap_graph_from_tables(tables, 1)
    var cb = ContractingBound(tables)
    var caught = False
    try:
        _ = cb.least_level(capped, CubicElt(1, 0, 0))
    except:
        caught = True
    assert_true(caught)


def main() raises:
    test_sturm_tarski_counts_and_signs()
    print("[PASS] test_sturm_tarski_counts_and_signs")
    test_bound_pins_exact_values()
    print("[PASS] test_bound_pins_exact_values")
    test_capped_graph_is_rejected()
    print("[PASS] test_capped_graph_is_rejected")
    print("3 contracting-bound Mojo tests passed.")
