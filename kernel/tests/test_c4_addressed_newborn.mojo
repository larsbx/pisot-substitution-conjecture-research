"""Addressed overlap witnesses lift to literal Sync cuts at both ends."""

from std.testing import assert_equal, assert_true, assert_false
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution, newborn_sync_positions
from psc.c4_addressed_newborn import addressed_newborn
from psc.words import Pair


def test_physical_overlap_controls() raises:
    var phase_zero: List[List[Int]] = [[0, 1], [1, 2], [0, 2, 1]]
    var t = Pair([1, 2, 0, 1], [0, 1, 1, 2])
    var a = addressed_newborn(phase_zero, t, 1, 2, [2, 1, 2], [1, 0, 1])
    assert_equal(a.ordinals, [0, 1, 2])
    assert_equal(a.parent, Pair([0, 2, 1, 1, 2], [2, 1, 1, 2, 0]))
    assert_equal(a.cut, 11)
    assert_true(a.sync_right)
    assert_true(a.cut in newborn_sync_positions(phase_zero, a.parent))

    var recurrent: List[List[Int]] = [[1], [0, 2], [2, 2, 0]]
    var s = Pair([1, 2, 2, 0, 2, 2, 0, 2, 2, 0, 1],
                 [0, 2, 2, 2, 0, 2, 2, 0, 1, 1, 2])
    var b = addressed_newborn(recurrent, s, 8, 9, [1, 0, 0], [1, 0, 1])
    assert_equal(b.ordinals, [2, 2, 1])
    assert_equal(b.parent, Pair([2, 0, 2, 2, 0, 1], [0, 1, 2, 2, 0, 2]))
    assert_equal(b.cut, 4)
    assert_true(b.sync_right)
    assert_true(b.cut in newborn_sync_positions(recurrent, b.parent))


def test_exterior_diagonal_still_has_an_interior_cut() raises:
    var t = Pair([0, 1], [1, 0])
    var left: List[List[Int]] = [[0, 1], [0], [2]]
    # Extend the witness past the first diagonal. The receipt remains at depth one.
    var a = addressed_newborn(left, t, 0, 0, [0, 1], [0, 1])
    assert_equal(a.ordinals, [0])
    assert_equal(a.cut, 1)
    assert_false(a.sync_right)
    var top = apply_substitution(left, t.u)
    var bottom = apply_substitution(left, t.v)
    assert_equal(top[a.cut - 1], bottom[a.cut - 1])
    assert_true(a.cut in newborn_sync_positions(left, t))

    # A first-diagonal receipt is not permission to ignore the remaining
    # supplied address. The next selected source is 0, whose image has size 2.
    var rejected_suffix = False
    try:
        _ = addressed_newborn(left, t, 0, 0, [0, 2], [0, 1])
    except:
        rejected_suffix = True
    assert_true(rejected_suffix)

    # Every digit is valid here, but the suffix selects different singleton
    # occurrences after the first diagonal. A prior successful prefix cannot
    # justify accepting this complete witness.
    rejected_suffix = False
    try:
        _ = addressed_newborn(left, t, 0, 0, [0, 0], [0, 1])
    except:
        rejected_suffix = True
    assert_true(rejected_suffix)

    var right: List[List[Int]] = [[1, 0], [0], [2]]
    var b = addressed_newborn(right, t, 1, 1, [0], [1])
    assert_equal(b.ordinals, [1])
    assert_equal(b.cut, 2)
    assert_true(b.sync_right)
    assert_true(b.cut in newborn_sync_positions(right, t))


def test_refuses_invalid_witnesses() raises:
    var s: List[List[Int]] = [[0, 1], [0], [2]]
    var t = Pair([0, 1], [1, 0])
    var rejected = False
    try:
        _ = addressed_newborn(s, t, 0, 0, [1], [0])  # Different factors.
    except:
        rejected = True
    assert_true(rejected)
    rejected = False
    try:
        _ = addressed_newborn(s, t, 0, 0, [0], [1])  # Invalid bottom digit.
    except:
        rejected = True
    assert_true(rejected)
    rejected = False
    try:
        _ = addressed_newborn(s, t, 1, 1, [0], [0])  # Same non-diagonal factor.
    except:
        rejected = True
    assert_true(rejected)
    rejected = False
    try:
        _ = addressed_newborn(s, t, 0, 0, [0], [0], word_cap=2)
    except:
        rejected = True
    assert_true(rejected)


def main() raises:
    test_physical_overlap_controls()
    test_exterior_diagonal_still_has_an_interior_cut()
    test_refuses_invalid_witnesses()
    print("C4 addressed overlap witnesses replay to one-step interior Sync cuts.")
    require_contract("literal addressed diagonal transport through ordered factors to the first one-step interior synchronizing newborn")
