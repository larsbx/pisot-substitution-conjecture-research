"""Canonical Mojo regressions for the strict first-child hub phase."""

from std.testing import assert_equal, assert_true
from psc.claim_tests import require_claim, require_contract
from psc.endpoint_core import endpoint_type
from psc.hub_selector import (
    alternating_e_template,
    cdef_phase_is_uniform,
    first_child_hub_residual,
    strict_star_eventual_cycle_period,
    strict_star_pair_viable,
    strict_star_recurrent_cycle_kind,
    strict_star_selector_phase,
)


def test_named_representatives_pin_selector_phases() raises:
    var c: List[Int] = [0, 0, 2]
    var d: List[Int] = [0, 1, 2]
    var e: List[Int] = [0, 2, 1]
    var f: List[Int] = [1, 0, 0]

    assert_equal(strict_star_selector_phase(c, 0, 1), 0)
    assert_equal(first_child_hub_residual(c, 0, 1, 0, 2), 0)
    assert_equal(first_child_hub_residual(c, 0, 1, 1, 2), 0)

    assert_equal(strict_star_selector_phase(d, 0, 1), 0)
    assert_equal(strict_star_selector_phase(d, 0, 2), 0)
    assert_equal(strict_star_selector_phase(d, 1, 2), 0)

    assert_equal(strict_star_selector_phase(e, 0, 1), 1)
    assert_equal(strict_star_selector_phase(e, 0, 2), 1)
    assert_equal(strict_star_selector_phase(e, 1, 2), 0)

    assert_equal(strict_star_selector_phase(f, 0, 1), -1)
    assert_equal(strict_star_selector_phase(f, 0, 2), 1)
    assert_equal(strict_star_selector_phase(f, 1, 2), 1)


def test_all_cdef_maps_have_uniform_viable_phase() raises:
    var counts_c0 = 0
    var counts_c_none = 0
    var counts_d0 = 0
    var counts_e0 = 0
    var counts_e1 = 0
    var counts_f1 = 0
    var counts_f_none = 0

    for x in range(3):
        for y in range(3):
            for z in range(3):
                var h: List[Int] = [x, y, z]
                var t = endpoint_type(h)
                if t < 2 or t > 5:
                    continue
                for ga in range(3):
                    for gb in range(ga + 1, 3):
                        assert_true(cdef_phase_is_uniform(h, ga, gb))
                        var q = strict_star_selector_phase(h, ga, gb)
                        assert_true(q == -1 or q == 0 or q == 1)
                        if t == 2:
                            if q == 0:
                                counts_c0 += 1
                            else:
                                assert_equal(q, -1)
                                counts_c_none += 1
                        elif t == 3:
                            assert_equal(q, 0)
                            counts_d0 += 1
                        elif t == 4:
                            if q == 0:
                                counts_e0 += 1
                            else:
                                assert_equal(q, 1)
                                counts_e1 += 1
                        else:
                            if q == 1:
                                counts_f1 += 1
                            else:
                                assert_equal(q, -1)
                                counts_f_none += 1

    assert_equal(counts_c0, 12)
    assert_equal(counts_c_none, 6)
    assert_equal(counts_d0, 3)
    assert_equal(counts_e0, 3)
    assert_equal(counts_e1, 6)
    assert_equal(counts_f1, 12)
    assert_equal(counts_f_none, 6)


def test_viability_rejects_good_edge_and_coalescence() raises:
    var c: List[Int] = [0, 0, 2]
    assert_true(not strict_star_pair_viable(c, 0, 1, 0, 1))
    assert_true(not strict_star_pair_viable(c, 1, 2, 0, 1))


def test_recurrent_aligned_cycle_normal_form_is_fixed_or_alternating_e() raises:
    var none = 0
    var fixed = 0
    var alternating = 0

    for x in range(3):
        for y in range(3):
            for z in range(3):
                var h: List[Int] = [x, y, z]
                for ga in range(3):
                    for gb in range(ga + 1, 3):
                        var kind = strict_star_recurrent_cycle_kind(h, ga, gb)
                        if kind < 0:
                            none += 1
                        elif kind == 1:
                            fixed += 1
                        else:
                            assert_equal(kind, 2)
                            assert_true(alternating_e_template(h, ga, gb))
                            alternating += 1

    assert_equal(none, 45)
    assert_equal(fixed, 33)
    assert_equal(alternating, 3)


def test_alternating_e_cycle_is_exactly_the_good_edge_swap() raises:
    # Hub 0 fixed, Barge-Diamond-good edge {1,2} swapped.
    var e: List[Int] = [0, 2, 1]
    assert_true(alternating_e_template(e, 1, 2))
    assert_equal(strict_star_eventual_cycle_period(e, 1, 2, 0, 1), 2)
    assert_equal(strict_star_eventual_cycle_period(e, 1, 2, 0, 2), 2)
    assert_equal(strict_star_selector_phase(e, 1, 2), 0)

    # With a different good edge the same endpoint map has a fixed-edge
    # obstruction template instead of the alternating one.
    assert_true(not alternating_e_template(e, 0, 1))
    assert_equal(strict_star_recurrent_cycle_kind(e, 0, 1), 1)


def main() raises:
    test_named_representatives_pin_selector_phases()
    print("[PASS] test_named_representatives_pin_selector_phases")
    test_all_cdef_maps_have_uniform_viable_phase()
    print("[PASS] test_all_cdef_maps_have_uniform_viable_phase")
    test_viability_rejects_good_edge_and_coalescence()
    print("[PASS] test_viability_rejects_good_edge_and_coalescence")
    test_recurrent_aligned_cycle_normal_form_is_fixed_or_alternating_e()
    print("[PASS] test_recurrent_aligned_cycle_normal_form_is_fixed_or_alternating_e")
    test_alternating_e_cycle_is_exactly_the_good_edge_swap()
    print("[PASS] test_alternating_e_cycle_is_exactly_the_good_edge_swap")
    print("5 hub-selector Mojo tests passed.")
    require_claim("EndpointCore")
    require_contract(
        "aligned recurrent hub-star pair cycle is fixed or alternating type-E"
    )
