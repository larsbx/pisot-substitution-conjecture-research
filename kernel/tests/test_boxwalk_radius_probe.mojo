"""Regression for the historical radius-8 claim: bounded exact negative witness.

This does not claim a global box-walk closure, a saturated infinite-radius
maximum, or an exhaustive constrained-family search. The named probe is a
fully replayable finite-depth computation of aligned prefix differences.
"""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.boxwalk_radius_probe import historical_swap_probe


def test_named_swap_radius_exceeds_eight_after_plateau() raises:
    var rows = historical_swap_probe(9, 30000)
    var lengths: List[Int] = [2, 5, 14, 40, 114, 324, 920, 2612, 7416, 21056]
    var radii: List[Int] = [1, 2, 4, 6, 6, 6, 8, 8, 8, 10]
    assert_equal(len(rows), len(lengths))
    for k in range(len(rows)):
        assert_equal(rows[k].depth, k)
        assert_equal(rows[k].word_length, lengths[k])
        assert_equal(rows[k].radius, radii[k])
    # At depth 9, the first radius-10 cut has EXACT Parikh difference.
    assert_equal(rows[9].first_cut, 9054)
    assert_equal(rows[9].d0, 5)
    assert_equal(rows[9].d1, 5)
    assert_equal(rows[9].d2, -10)


def test_budget_refuses_without_converting_a_probe_to_a_certificate() raises:
    var refused = False
    try:
        _ = historical_swap_probe(9, 20000)
    except:
        refused = True
    assert_true(refused)
    var partial = historical_swap_probe(8, 10000)
    assert_equal(len(partial), 9)
    assert_equal(partial[8].radius, 8)
    # Eight at depth 8 is a truncated prefix, NOT a saturation certificate.


def main() raises:
    test_named_swap_radius_exceeds_eight_after_plateau()
    print("[PASS] historical radius-eight plateau broken at depth nine")
    test_budget_refuses_without_converting_a_probe_to_a_certificate()
    print("[PASS] capped probe refuses rather than certifying")
    require_contract("fixed historical substitution (001,22,220): aligned-prefix radius on inflated swap (01,10) is 8 at depth 8 but 10 at depth 9 (first cut 9054, defect 5,5,-10); no saturation or exhaustive-family claim; per-side word budget refuses")
