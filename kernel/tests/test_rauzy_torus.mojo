"""Regressions for the exact Rauzy-fractal torus kernel (psc/rauzy_torus.mojo).

Pins the certified frequency floors (independently recomputed by
oracles/python/rauzy_torus.py), the fixed-point prefix, the fail-closed
enclosure-to-cell rule, the lift-profile estimator on synthetic one- and
two-lift covers, and the non-unimodular refusal. Nothing here certifies a
covering degree or the Pisot conjecture for any substitution.
"""

from std.testing import assert_equal, assert_true

from mojo_smoke.claims import require_contract
from psc.perron_field3 import build_perron_field3, cubic_add_checked, perron_tile_lengths_in
from psc.rauzy_torus import (
    FREQUENCY_SCALE,
    LIFT_SPAN,
    MAX_LIFTS_PER_CELL,
    LiftProfile,
    _scaled_floor,
    transpose3,
    MAX_POINTS,
    enclosure_cell,
    fixed_point_prefix,
    frequency_frame,
    incidence_of,
    lift_profile,
    lift_profile_of_cells,
    rauzy_points,
    sup_discrepancy_bound,
)


def _tribonacci() -> List[List[Int]]:
    return [[0, 1], [0, 2], [0]]


def test_tribonacci_frequency_floors() raises:
    var frame = frequency_frame(incidence_of(_tribonacci()))
    # floor(2^40 / beta^k), k = 1, 2, 3, for the Tribonacci constant beta.
    assert_equal(frame.f0, 597792391348)
    assert_equal(frame.f1, 325013155047)
    assert_equal(frame.f2, 176706081379)
    assert_equal(frame.f0 + frame.f1 + frame.f2, FREQUENCY_SCALE - 2)


def test_wrong_hint_falls_back_to_bisection() raises:
    # The iteration hint is never trusted: a wrong or absent hint must give
    # the same certified floor by full bisection.
    var m = incidence_of(_tribonacci())
    var field = build_perron_field3(m)
    var v = perron_tile_lengths_in(field, transpose3(m))
    var total = cubic_add_checked(cubic_add_checked(v.l0, v.l1), v.l2)
    for hint in [-1, 0, 597792391347, 597792391349]:
        assert_equal(_scaled_floor(field, v.l0, total, FREQUENCY_SCALE, hint), 597792391348)


def test_nonunimodular_is_refused() raises:
    var refused = False
    try:
        _ = frequency_frame(incidence_of([[0, 1, 1], [2, 0], [0]]))
    except:
        refused = True
    assert_true(refused)


def test_fixed_point_prefix() raises:
    var w = fixed_point_prefix(_tribonacci(), 13)
    var expected: List[Int] = [0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 2, 0, 1]
    assert_equal(len(w), 13)
    for i in range(13):
        assert_equal(w[i], expected[i])
    var refused = False
    try:
        _ = fixed_point_prefix(_tribonacci(), MAX_POINTS + 1)
    except:
        refused = True
    assert_true(refused)


def test_enclosure_straddling_a_grid_line_is_undecided() raises:
    assert_equal(len(enclosure_cell(10, 3, 8)), 0)
    var inside = enclosure_cell(-1, 2, 8)
    assert_equal(len(inside), 1)
    assert_equal(inside[0], -1)


def test_lift_profile_separates_one_and_two_lift_covers() raises:
    var once = List[List[Int]]()
    for x in range(3, 7):
        for y in range(-2, 2):
            once.append([x, y])
    var one = lift_profile_of_cells(once, 4)
    assert_equal(one.occupied(), 16)
    assert_equal(one.histogram().count(1), 16)
    # Negative control: the same block again, translated by a lattice vector,
    # covers every torus cell twice.
    var twice = once.copy()
    for c in once:
        twice.append([c[0] + 4, c[1] + 8])
    var two = lift_profile_of_cells(twice, 4)
    assert_equal(two.occupied(), 16)
    assert_equal(two.histogram().count(2), 16)
    assert_equal(two.histogram().count(1), 0)


def test_histogram_holds_every_encodable_lift_count() raises:
    # grid=1 sends every planar cell to one torus cell. Check the original
    # limit, the first count past it, and full Cartesian lift-window coverage.
    var half = LIFT_SPAN // 2
    var cells = List[List[Int]]()
    for lx in range(-half, half - 1):
        cells.append([lx, 0])
    var below = lift_profile_of_cells(cells, 1)
    assert_equal(below.histogram().count(LIFT_SPAN - 1), 1)
    assert_equal(len(below.histogram().counts), LIFT_SPAN)

    cells.append([half - 1, 0])
    var at_bound = lift_profile_of_cells(cells, 1)
    assert_equal(at_bound.histogram().count(LIFT_SPAN), 1)
    assert_equal(len(at_bound.histogram().counts), LIFT_SPAN + 1)

    cells.append([0, 1])
    var above = lift_profile_of_cells(cells, 1)
    assert_equal(above.histogram().count(LIFT_SPAN + 1), 1)
    assert_equal(len(above.histogram().counts), LIFT_SPAN + 2)

    # Regression must exercise LiftProfile.histogram(), not a standalone
    # Histogram. Every valid encoded lift is present, with one duplicate.
    var full_cells = List[List[Int]]()
    for lx in range(-half, half):
        for ly in range(-half, half):
            full_cells.append([lx, ly])
    full_cells.append([-half, -half])
    var full_profile = lift_profile_of_cells(full_cells, 1)
    assert_equal(full_profile.occupied(), 1)
    var full = full_profile.histogram()
    assert_equal(full.count(MAX_LIFTS_PER_CELL), 1)
    assert_equal(full.maximum(), MAX_LIFTS_PER_CELL)
    assert_equal(full.total(), 1)
    assert_equal(len(full.counts), MAX_LIFTS_PER_CELL + 1)


def test_lift_histogram_small_and_malformed_controls() raises:
    var empty_cells = List[List[Int]]()
    var empty = lift_profile_of_cells(empty_cells, 1).histogram()
    assert_equal(empty.maximum(), 0)
    assert_equal(empty.total(), 0)
    assert_equal(len(empty.counts), 1)

    var small: List[List[Int]] = [[0, 0], [1, 0], [0, 1], [0, 1]]
    var p = lift_profile_of_cells(small, 1)
    var h = p.histogram()
    assert_equal(h.count(3), 1)
    assert_equal(h.total(), 1)
    assert_equal(len(h.counts), 4)

    # A forged profile must not allocate past the window or discard
    # impossible negative lift counts.
    var negative: List[Int] = [-1]
    var negative_profile = LiftProfile(1, negative^, 0)
    var refused = False
    try:
        _ = negative_profile.histogram()
    except:
        refused = True
    assert_true(refused)

    var excessive: List[Int] = [MAX_LIFTS_PER_CELL + 1]
    var excessive_profile = LiftProfile(1, excessive^, 0)
    refused = False
    try:
        _ = excessive_profile.histogram()
    except:
        refused = True
    assert_true(refused)

    refused = False
    try:
        _ = lift_profile_of_cells(empty_cells, 0)
    except:
        refused = True
    assert_true(refused)

    var malformed: List[List[Int]] = [[0]]
    refused = False
    try:
        _ = lift_profile_of_cells(malformed, 1)
    except:
        refused = True
    assert_true(refused)

    var half = LIFT_SPAN // 2
    var outside_low: List[List[Int]] = [[-half - 1, 0]]
    refused = False
    try:
        _ = lift_profile_of_cells(outside_low, 1)
    except:
        refused = True
    assert_true(refused)

    var outside_high: List[List[Int]] = [[0, half]]
    refused = False
    try:
        _ = lift_profile_of_cells(outside_high, 1)
    except:
        refused = True
    assert_true(refused)


def test_tribonacci_lift_profile_regression() raises:
    var frame = frequency_frame(incidence_of(_tribonacci()))
    var points = rauzy_points(_tribonacci(), frame, 8192)
    var profile = lift_profile(points, frame.scale, 64)
    assert_equal(profile.undecided, 0)
    var h = profile.histogram()
    assert_equal(h.count(1), 3957)
    assert_equal(h.count(2), 47)
    assert_equal(h.count(3), 1)
    assert_equal(h.maximum(), 3)
    assert_equal(sup_discrepancy_bound(points), 920370025771)


def main() raises:
    test_tribonacci_frequency_floors()
    print("[PASS] Tribonacci frequency floors certified and oracle-pinned")
    test_wrong_hint_falls_back_to_bisection()
    print("[PASS] a wrong frequency hint is rejected and bisected")
    test_nonunimodular_is_refused()
    print("[PASS] non-unimodular incidence refused (solenoid, not torus)")
    test_fixed_point_prefix()
    print("[PASS] fixed-point prefix and its length budget")
    test_enclosure_straddling_a_grid_line_is_undecided()
    print("[PASS] straddling enclosures are undecided, never assigned")
    test_lift_profile_separates_one_and_two_lift_covers()
    print("[PASS] lift profile: one-lift cover vs two-lift negative control")
    test_histogram_holds_every_encodable_lift_count()
    print("[PASS] lift histogram end-to-end at 255, 256, 257 and 65536")
    test_lift_histogram_small_and_malformed_controls()
    print("[PASS] sparse lift histogram capacity and malformed-input refusal")
    test_tribonacci_lift_profile_regression()
    print("[PASS] Tribonacci 8192-point lift profile on a 64-grid")
    require_contract("rauzy torus kernel: certified floor(2^40 f_i) letter frequencies, exact discrepancy enclosures D_n = p_n - n f on the fixed-point stepped line, fail-closed cell assignment, distinct-lift profile on T^2 = H/H_Z; non-unimodular refused; diagnostic only, certifies no covering degree")
