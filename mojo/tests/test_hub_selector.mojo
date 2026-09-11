"""Canonical Mojo regressions for the strict first-child hub phase."""

from std.testing import assert_equal, assert_true
from psc.endpoint_core import endpoint_type
from psc.hub_selector import (
    cdef_phase_is_uniform,
    first_child_hub_residual,
    strict_star_pair_viable,
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


def main() raises:
    test_named_representatives_pin_selector_phases()
    print("[PASS] test_named_representatives_pin_selector_phases")
    test_all_cdef_maps_have_uniform_viable_phase()
    print("[PASS] test_all_cdef_maps_have_uniform_viable_phase")
    test_viability_rejects_good_edge_and_coalescence()
    print("[PASS] test_viability_rejects_good_edge_and_coalescence")
    print("3 hub-selector Mojo tests passed.")
