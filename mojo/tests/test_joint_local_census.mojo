"""Canonical bounded-corpus regressions for the G1b-2 joint-local census."""

from std.testing import assert_equal, assert_false, assert_true
from psc.joint_local_census import (
    address_is_one_loop_extension,
    audit_projection,
    samples_through_depth,
    zero_return_cuts,
)
from psc.joint_local_type import joint_local_type, same_joint_local_type
from psc.renewal_address import (
    build_renewal_address_tables,
    build_renewal_pair_census_state,
    renewal_cut_address_from_state,
    same_relative_address,
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


def test_zero_return_oracle_pins_depth_four_seed_cuts() raises:
    var cuts = zero_return_cuts(nonunimodular_pisot_sigma(), seed_pair(), 4)
    assert_equal(len(cuts), 27)
    assert_equal(cuts[len(cuts) - 3], 47)
    assert_equal(cuts[len(cuts) - 2], 48)
    assert_equal(cuts[len(cuts) - 1], 49)


def test_window_requirement_staircase_on_bounded_seed_corpus() raises:
    # Radius two already exposes the entire two-letter source pair (plus
    # sentinels). Increasing the depth cap from D-1 to D reintroduces exactly
    # three projection collisions at window D-2; window D-1 separates this
    # finite corpus. This is empirical bounded-corpus evidence only.
    var depth_caps: List[Int] = [3, 4, 5, 6, 7]
    var sample_counts: List[Int] = [16, 43, 107, 255, 601]

    for q in range(len(depth_caps)):
        var max_depth = depth_caps[q]
        var coarse_window = max_depth - 2
        var fine_window = max_depth - 1

        var coarse = samples_through_depth(
            nonunimodular_pisot_sigma(),
            seed_pair(),
            0,
            max_depth,
            2,
            coarse_window,
        )
        var coarse_audit = audit_projection(coarse)
        assert_equal(coarse_audit.sample_count, sample_counts[q])
        assert_equal(coarse_audit.collision_pair_count, 3)
        assert_true(coarse_audit.has_collision())

        var fine = samples_through_depth(
            nonunimodular_pisot_sigma(),
            seed_pair(),
            0,
            max_depth,
            2,
            fine_window,
        )
        var fine_audit = audit_projection(fine)
        assert_equal(fine_audit.sample_count, sample_counts[q])
        assert_equal(fine_audit.collision_pair_count, 0)
        assert_false(fine_audit.has_collision())

        if max_depth == 3:
            assert_equal(coarse[coarse_audit.first_left].depth, 2)
            assert_equal(coarse[coarse_audit.first_left].cut, 7)
            assert_equal(coarse[coarse_audit.first_right].depth, 3)
            assert_equal(coarse[coarse_audit.first_right].cut, 19)


def test_persistent_right_edge_collisions_are_regular_loop_extensions() raises:
    var sigma = nonunimodular_pisot_sigma()
    var pair = seed_pair()

    # For each tested depth d, compare the three right-edge cuts at d-1 and d.
    # Their bounded projection collides at window d-2, but the full addresses
    # differ by exactly one additional (parent=1, child-index=2) digit on each
    # side. This classifies the witnesses as a regular recurrence candidate
    # rather than silently treating every collision as a distinct obstruction.
    for depth in range(3, 8):
        var short_tables = build_renewal_address_tables(sigma, depth - 1)
        var long_tables = build_renewal_address_tables(sigma, depth)
        var short_state = build_renewal_pair_census_state(short_tables, pair)
        var long_state = build_renewal_pair_census_state(long_tables, pair)
        var window = depth - 2

        for j in range(3):
            var short_cut = short_state.inflated_length - 3 + j
            var long_cut = long_state.inflated_length - 3 + j
            var short_address = renewal_cut_address_from_state(short_state, short_cut)
            var long_address = renewal_cut_address_from_state(long_state, long_cut)
            assert_false(same_relative_address(short_address, long_address))
            assert_true(
                address_is_one_loop_extension(short_address, long_address, 1, 2)
            )

            var short_type = joint_local_type(short_state, short_cut, 2, window)
            var long_type = joint_local_type(long_state, long_cut, 2, window)
            assert_true(same_joint_local_type(short_type, long_type))


def main() raises:
    test_zero_return_oracle_pins_depth_four_seed_cuts()
    print("[PASS] test_zero_return_oracle_pins_depth_four_seed_cuts")
    test_window_requirement_staircase_on_bounded_seed_corpus()
    print("[PASS] test_window_requirement_staircase_on_bounded_seed_corpus")
    test_persistent_right_edge_collisions_are_regular_loop_extensions()
    print("[PASS] test_persistent_right_edge_collisions_are_regular_loop_extensions")
    print("3 joint-local-census Mojo tests passed.")
