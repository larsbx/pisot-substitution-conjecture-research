"""Exact regressions for the G1b-2 affine prefix-suffix trace diagnostic."""

from std.testing import assert_equal, assert_false, assert_true
from psc.loop_quotient_census import (
    AddressedJointLocalSample,
    addressed_samples_through_depth,
)
from psc.renewal_affine_trace import (
    affine_path_from_address,
    build_affine_trace,
    delete_proper_affine_cycle,
    first_proper_affine_repeat,
    reduce_first_proper_affine_cycle,
    same_affine_path,
)
from psc.renewal_address import (
    build_renewal_address_tables,
    build_renewal_pair_census_state,
    renewal_cut_address_from_state,
)
from psc.words import Pair


def nonunimodular_pisot_sigma() -> List[List[Int]]:
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


def _find_observation(
    samples: List[AddressedJointLocalSample], depth: Int, cut: Int
) -> Int:
    for i in range(len(samples)):
        if samples[i].depth == depth and samples[i].cut == cut:
            return i
    return -1


def test_unique_sidewise_survivor_is_one_proper_affine_pump() raises:
    # PR #56 leaves exactly one residual pair after the tested abelian sidewise
    # refinement: depth 7/cut 14 versus depth 5/cut 14.  The longer ordered
    # ancestry contains one proper internal repeated affine state.
    var sigma = nonunimodular_pisot_sigma()
    var samples = addressed_samples_through_depth(sigma, seed_pair(), 0, 7, 2, 1)
    var long_index = _find_observation(samples, 7, 14)
    var short_index = _find_observation(samples, 5, 14)
    assert_true(long_index >= 0)
    assert_true(short_index >= 0)

    var tables = build_renewal_address_tables(sigma, 7)
    var long_path = affine_path_from_address(samples[long_index].address)
    var short_path = affine_path_from_address(samples[short_index].address)
    var long_trace = build_affine_trace(tables, long_path)
    var short_trace = build_affine_trace(tables, short_path)

    assert_equal(long_trace.level, 7)
    assert_equal(short_trace.level, 5)
    var repeat = first_proper_affine_repeat(long_trace)
    assert_true(repeat.found)
    assert_equal(repeat.start, 1)
    assert_equal(repeat.end, 3)
    assert_true(long_trace.same_state(1, 3))
    assert_equal(long_trace.top_letter(1), 1)
    assert_equal(long_trace.bottom_letter(1), 0)
    var residual = long_trace.residual(1)
    assert_equal(residual.x, 0)
    assert_equal(residual.y, 0)
    assert_equal(residual.z, 0)

    var reduced = reduce_first_proper_affine_cycle(tables, long_path)
    assert_equal(reduced.level(), 5)
    assert_true(same_affine_path(reduced, short_path))

    # The observed depth-5 address has no proper internal repeated state.  Its
    # start and terminal state do agree, but boundary repeats are intentionally
    # excluded from pump deletion.
    var short_repeat = first_proper_affine_repeat(short_trace)
    assert_false(short_repeat.found)
    assert_true(short_trace.same_state(0, short_trace.level))


def test_right_edge_loop_reduces_to_certified_shallower_address() raises:
    # The previously observed synchronous (1,2) right-edge recurrence is also
    # detected by the more general affine state: one internal zero-residual
    # self-loop deletion takes the depth-4 address exactly to depth 3.
    var sigma = nonunimodular_pisot_sigma()
    var pair = seed_pair()
    var short_tables = build_renewal_address_tables(sigma, 3)
    var long_tables = build_renewal_address_tables(sigma, 4)
    var short_state = build_renewal_pair_census_state(short_tables, pair)
    var long_state = build_renewal_pair_census_state(long_tables, pair)

    for j in range(3):
        var short_cut = short_state.inflated_length - 3 + j
        var long_cut = long_state.inflated_length - 3 + j
        var short_address = renewal_cut_address_from_state(short_state, short_cut)
        var long_address = renewal_cut_address_from_state(long_state, long_cut)
        var short_path = affine_path_from_address(short_address)
        var long_path = affine_path_from_address(long_address)
        var trace = build_affine_trace(long_tables, long_path)
        var repeat = first_proper_affine_repeat(trace)
        assert_true(repeat.found)
        assert_equal(repeat.start, 1)
        assert_equal(repeat.end, 2)
        var reduced = reduce_first_proper_affine_cycle(long_tables, long_path)
        assert_true(same_affine_path(reduced, short_path))


def test_nonrepeat_cycle_deletion_fails_closed() raises:
    var sigma = nonunimodular_pisot_sigma()
    var samples = addressed_samples_through_depth(sigma, seed_pair(), 0, 5, 2, 1)
    var index = _find_observation(samples, 5, 14)
    assert_true(index >= 0)
    var tables = build_renewal_address_tables(sigma, 5)
    var path = affine_path_from_address(samples[index].address)

    # The depth-5 witness has no proper repeat.  Supplying arbitrary internal
    # endpoints must fail rather than inventing a pump relation.
    var caught = False
    try:
        _ = delete_proper_affine_cycle(tables, path, 1, 2)
    except:
        caught = True
    assert_true(caught)


def main() raises:
    test_unique_sidewise_survivor_is_one_proper_affine_pump()
    print("[PASS] test_unique_sidewise_survivor_is_one_proper_affine_pump")
    test_right_edge_loop_reduces_to_certified_shallower_address()
    print("[PASS] test_right_edge_loop_reduces_to_certified_shallower_address")
    test_nonrepeat_cycle_deletion_fails_closed()
    print("[PASS] test_nonrepeat_cycle_deletion_fails_closed")
    print("3 renewal-affine-trace Mojo tests passed.")
