"""Exact weighted hub area and physical negative interval controls."""
from std.testing import assert_equal, assert_true, assert_false
from mojo_smoke.claims import require_contract
from psc.words import Pair
from psc.c4_physical_hub_area import weighted_hub_profile


def reject(pair: Pair,hub: Int,widths: List[Int]) -> Bool:
    try:
        _=weighted_hub_profile(pair,hub,widths)
        return False
    except:
        return True


def main() raises:
    # Productive irreducible-Pisot phase-zero component, not strict.
    var phase_zero=Pair([1,2,0,1],[0,1,1,2])
    var unit=weighted_hub_profile(phase_zero,1,[1,1,1])
    assert_equal(unit.area,0)
    assert_equal(unit.negative_length,1)
    assert_equal(unit.positive_length,1)
    assert_equal(unit.negative_intervals,1)
    assert_false(unit.noncrossing)
    var weighted=weighted_hub_profile(phase_zero,1,[2,3,5])
    assert_equal(weighted.area,-3)
    assert_equal(weighted.negative_length,5)
    assert_equal(weighted.positive_length,2)
    assert_equal(weighted.total_length,13)

    # Productive, good-edge PIP recurrent phase-one negative to
    # transferring symbolic hub crossing directly to Sync.
    var phase_one=Pair(
        [1,2,2,0,2,2,0,2,2,0,1],
        [0,2,2,2,0,2,2,0,1,1,2],
    )
    unit=weighted_hub_profile(phase_one,1,[1,1,1])
    assert_equal(unit.area,7)
    assert_equal(unit.negative_length,1)
    weighted=weighted_hub_profile(phase_one,1,[2,3,5])
    assert_equal(weighted.area,26)
    assert_equal(weighted.negative_length,5)
    assert_equal(weighted.positive_length,31)

    # Strict reducible non-Pisot component: no negative hub intervals;
    # the bound of at least one bottom-first tile width is exact here.
    var reducible=Pair([2,1,0],[1,0,2])
    unit=weighted_hub_profile(reducible,2,[1,1,1])
    assert_equal(unit.area,2)
    assert_true(unit.noncrossing)
    assert_equal(unit.negative_length,0)
    weighted=weighted_hub_profile(reducible,2,[2,3,5])
    assert_equal(weighted.area,5)
    assert_true(weighted.noncrossing)
    assert_equal(weighted.positive_length,5)

    # Balanced concatenation resets the completed-hub discrepancy at
    # the internal cut. The resulting physical integral is additive.
    var twice=Pair([1,2,0,1,1,2,0,1],[0,1,1,2,0,1,1,2])
    weighted=weighted_hub_profile(twice,1,[2,3,5])
    assert_equal(weighted.area,-6)
    assert_equal(weighted.negative_length,10)

    assert_true(reject(phase_zero,1,[2,0,5]))
    assert_true(reject(phase_zero,2,[1,1,1]))
    assert_true(reject(phase_zero,1,[2,3]))
    assert_true(reject(Pair([1,2,0,1],[0,1,1,1]),1,[1,1,1]))
    assert_true(reject(Pair([1,2,0,1],[1,0,2,1]),1,[1,1,1]))
    print("C4_WEIGHTED_PHYSICAL_HUB_AREA_PASS")
    require_contract("exact arbitrary-positive-integer physical hub completion area equals the full scattered degree-two defect; genuine negative-interval and initial plateau controls; no C4 synchronization or PSC")
