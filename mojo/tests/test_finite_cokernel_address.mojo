"""Exact finite regressions for the G1b-2 sidewise cokernel diagnostic."""

from std.testing import assert_equal, assert_false, assert_true
from psc.finite_cokernel_address import (
    audit_sidewise_cokernel,
    build_cokernel_lattice,
    same_cokernel_class,
    sidewise_prefix_translation,
)
from psc.loop_quotient_census import (
    AddressedJointLocalSample,
    addressed_samples_through_depth,
)
from psc.renewal import Diff3
from psc.renewal_address import build_renewal_address_tables
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


def test_cokernel_orders_match_det_power() raises:
    var tables = build_renewal_address_tables(nonunimodular_pisot_sigma(), 5)
    var expected: List[Int] = [2, 4, 8, 16, 32]
    for level in range(1, 6):
        var lattice = build_cokernel_lattice(tables, level)
        assert_equal(lattice.order(), expected[level - 1])


def test_cokernel_membership_is_exact() raises:
    var tables = build_renewal_address_tables(nonunimodular_pisot_sigma(), 3)
    var zero = Diff3(0, 0, 0)
    var e0 = Diff3(1, 0, 0)

    for level in range(1, 4):
        var lattice = build_cokernel_lattice(tables, level)
        assert_true(same_cokernel_class(lattice, lattice.c0, zero))
        assert_true(same_cokernel_class(lattice, lattice.c1, zero))
        assert_true(same_cokernel_class(lattice, lattice.c2, zero))

    var level_one = build_cokernel_lattice(tables, 1)
    assert_false(same_cokernel_class(level_one, e0, zero))


def test_sidewise_prefix_reconstruction_matches_correction() raises:
    var sigma = nonunimodular_pisot_sigma()
    var samples = addressed_samples_through_depth(sigma, seed_pair(), 0, 3, 2, 1)
    var tables = build_renewal_address_tables(sigma, 3)
    assert_true(len(samples) > 0)

    for i in range(len(samples)):
        var translations = sidewise_prefix_translation(tables, samples[i].address)
        var correction = samples[i].address.correction.copy()
        assert_equal(translations.top.x - translations.bottom.x, correction.x)
        assert_equal(translations.top.y - translations.bottom.y, correction.y)
        assert_equal(translations.top.z - translations.bottom.z, correction.z)


def test_fixed_window_sidewise_cokernel_staircase() raises:
    var sigma = nonunimodular_pisot_sigma()
    var samples = addressed_samples_through_depth(sigma, seed_pair(), 0, 7, 2, 1)

    var previous_survivors = 11520
    var previous_same_depth_survivors = 11520
    var exact_survivors = -1
    var same_depth_residual = -1

    for level in range(1, 6):
        var audit = audit_sidewise_cokernel(samples, sigma, level)
        assert_equal(audit.sample_count, 601)
        assert_equal(audit.projection_collision_pair_count, 12466)
        assert_equal(audit.symbolic_quotiented_pair_count, 946)
        assert_equal(audit.residual_pair_count, 11520)
        assert_equal(
            audit.cokernel_surviving_pair_count + audit.cokernel_separated_pair_count,
            audit.residual_pair_count,
        )
        assert_true(audit.cokernel_surviving_pair_count <= previous_survivors)
        assert_true(
            audit.same_depth_cokernel_surviving_pair_count
            <= previous_same_depth_survivors
        )
        assert_true(
            audit.same_depth_cokernel_surviving_pair_count
            <= audit.same_depth_residual_pair_count
        )
        assert_true(
            audit.exact_sidewise_surviving_pair_count
            <= audit.cokernel_surviving_pair_count
        )

        if level == 1:
            exact_survivors = audit.exact_sidewise_surviving_pair_count
            same_depth_residual = audit.same_depth_residual_pair_count
        else:
            assert_equal(
                audit.exact_sidewise_surviving_pair_count,
                exact_survivors,
            )
            assert_equal(audit.same_depth_residual_pair_count, same_depth_residual)

        previous_survivors = audit.cokernel_surviving_pair_count
        previous_same_depth_survivors = audit.same_depth_cokernel_surviving_pair_count

        print("finite-cokernel level:", level)
        print("finite-cokernel order:", audit.cokernel_order)
        print("finite-cokernel residual pairs:", audit.residual_pair_count)
        print("finite-cokernel same-depth residual pairs:", audit.same_depth_residual_pair_count)
        print("finite-cokernel surviving residual pairs:", audit.cokernel_surviving_pair_count)
        print("finite-cokernel separated residual pairs:", audit.cokernel_separated_pair_count)
        print(
            "finite-cokernel same-depth surviving pairs:",
            audit.same_depth_cokernel_surviving_pair_count,
        )
        print(
            "finite-cokernel exact-sidewise surviving pairs:",
            audit.exact_sidewise_surviving_pair_count,
        )
        if audit.has_cokernel_survivor():
            print("finite-cokernel first survivor left:", audit.first_cokernel_survivor_left)
            print("finite-cokernel first survivor right:", audit.first_cokernel_survivor_right)


def test_cokernel_audit_rejects_invalid_level_and_mixed_specimens() raises:
    var sigma = nonunimodular_pisot_sigma()
    var samples = addressed_samples_through_depth(sigma, seed_pair(), 0, 2, 2, 1)

    var caught_level = False
    try:
        _ = audit_sidewise_cokernel(samples, sigma, 0)
    except:
        caught_level = True
    assert_true(caught_level)

    var other = addressed_samples_through_depth(sigma, seed_pair(), 1, 2, 2, 1)
    samples.append(other[0].copy())
    var caught_specimen = False
    try:
        _ = audit_sidewise_cokernel(samples, sigma, 1)
    except:
        caught_specimen = True
    assert_true(caught_specimen)


def main() raises:
    test_cokernel_orders_match_det_power()
    print("[PASS] test_cokernel_orders_match_det_power")
    test_cokernel_membership_is_exact()
    print("[PASS] test_cokernel_membership_is_exact")
    test_sidewise_prefix_reconstruction_matches_correction()
    print("[PASS] test_sidewise_prefix_reconstruction_matches_correction")
    test_fixed_window_sidewise_cokernel_staircase()
    print("[PASS] test_fixed_window_sidewise_cokernel_staircase")
    test_cokernel_audit_rejects_invalid_level_and_mixed_specimens()
    print("[PASS] test_cokernel_audit_rejects_invalid_level_and_mixed_specimens")
    print("5 finite-cokernel-address Mojo tests passed.")
