"""Exact finite regressions for the G1b-2 observed loop quotient."""

from std.testing import assert_equal, assert_false, assert_true
from psc.loop_quotient_census import (
    addressed_samples_through_depth,
    audit_projection_modulo_loop,
)
from psc.words import Pair


def nonunimodular_pisot_sigma() -> List[List[Int]]:
    # 0 -> 1, 1 -> 021, 2 -> 001; det(M)=2.
    var a0: List[Int] = [1]
    var a1: List[Int] = [0, 2, 1]
    var a2: List[Int] = [0, 0, 1]
    var sigma = List[List[Int]]()
    sigma.append(a0^)
    sigma.append(a1^)
    sigma.append(a2^)
    return sigma^


def seed_pair() -> Pair:
    var u: List[Int] = [0, 1]
    var v: List[Int] = [1, 0]
    return Pair(u, v)


def test_known_loop_quotient_removes_staircase_collisions() raises:
    # PR #52 pinned exactly three collisions at window D-2 for each depth cap
    # D=3..7. Their full addresses form the known synchronous (1,2) recurrence.
    # Quotienting by the observed loop-connected components must remove all
    # three while leaving the raw projection count visible.
    var depth_caps: List[Int] = [3, 4, 5, 6, 7]
    var sample_counts: List[Int] = [16, 43, 107, 255, 601]

    for q in range(len(depth_caps)):
        var max_depth = depth_caps[q]
        var samples = addressed_samples_through_depth(
            nonunimodular_pisot_sigma(),
            seed_pair(),
            0,
            max_depth,
            2,
            max_depth - 2,
        )
        var audit = audit_projection_modulo_loop(samples, 1, 2)
        assert_equal(audit.sample_count, sample_counts[q])
        assert_equal(audit.projection_collision_pair_count, 3)
        assert_equal(audit.direct_loop_edge_count, 3)
        assert_equal(audit.quotiented_collision_pair_count, 3)
        assert_equal(audit.residual_collision_pair_count, 0)
        assert_false(audit.has_residual_collision())


def test_wrong_loop_label_preserves_known_residuals() raises:
    var samples = addressed_samples_through_depth(
        nonunimodular_pisot_sigma(), seed_pair(), 0, 3, 2, 1
    )
    var audit = audit_projection_modulo_loop(samples, 0, 0)
    assert_equal(audit.projection_collision_pair_count, 3)
    assert_equal(audit.direct_loop_edge_count, 0)
    assert_equal(audit.quotiented_collision_pair_count, 0)
    assert_equal(audit.residual_collision_pair_count, 3)
    assert_true(audit.has_residual_collision())
    assert_true(audit.first_residual_left >= 0)
    assert_true(audit.first_residual_right >= 0)


def test_loop_quotient_rejects_mixed_projection_bounds() raises:
    var window_one = addressed_samples_through_depth(
        nonunimodular_pisot_sigma(), seed_pair(), 0, 2, 2, 1
    )
    var window_two = addressed_samples_through_depth(
        nonunimodular_pisot_sigma(), seed_pair(), 1, 2, 2, 2
    )
    window_one.append(window_two[0].copy())

    var caught = False
    try:
        _ = audit_projection_modulo_loop(window_one, 1, 2)
    except:
        caught = True
    assert_true(caught)


def test_fixed_window_diagnostic_preserves_accounting() raises:
    # A fixed one-level window is deliberately too coarse as depth grows. This
    # test does not assert that the known loop explains every collision; it only
    # pins exact accounting while retaining any unexplained residual witness for
    # the next arithmetic-coordinate experiment.
    var samples = addressed_samples_through_depth(
        nonunimodular_pisot_sigma(), seed_pair(), 0, 7, 2, 1
    )
    var audit = audit_projection_modulo_loop(samples, 1, 2)
    assert_equal(
        audit.quotiented_collision_pair_count
        + audit.residual_collision_pair_count,
        audit.projection_collision_pair_count,
    )
    assert_true(audit.projection_collision_pair_count >= 3)
    assert_true(audit.quotiented_collision_pair_count >= 3)
    print("fixed-window depth-7 raw collisions:", audit.projection_collision_pair_count)
    print("fixed-window depth-7 loop-quotiented pairs:", audit.quotiented_collision_pair_count)
    print("fixed-window depth-7 residual collisions:", audit.residual_collision_pair_count)
    if audit.has_residual_collision():
        print("fixed-window first residual left:", audit.first_residual_left)
        print("fixed-window first residual right:", audit.first_residual_right)


def main() raises:
    test_known_loop_quotient_removes_staircase_collisions()
    print("[PASS] test_known_loop_quotient_removes_staircase_collisions")
    test_wrong_loop_label_preserves_known_residuals()
    print("[PASS] test_wrong_loop_label_preserves_known_residuals")
    test_loop_quotient_rejects_mixed_projection_bounds()
    print("[PASS] test_loop_quotient_rejects_mixed_projection_bounds")
    test_fixed_window_diagnostic_preserves_accounting()
    print("[PASS] test_fixed_window_diagnostic_preserves_accounting")
    print("4 loop-quotient-census Mojo tests passed.")
