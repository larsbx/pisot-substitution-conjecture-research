"""Higher-determinant BH carrier and adversarial replay."""
from std.testing import assert_equal, assert_raises, assert_true
from mojo_smoke.claims import require_contract
from psc.bh_two_parameter_carrier import (
    CarrierEdge, build_carrier, parikh_difference, tables_for, verify_carrier,
)
from psc.overlap_seed_patch import (
    OverlapState, interior_overlap, selected_overlap_child,
)
from psc.perron_field3 import CubicElt


def test_literal_rows() raises:
    var carrier = build_carrier(4, 6, 1000, 10000)
    var tables = tables_for(4, 6)
    # Independent Cartesian-product scan using the existing selected digit API.
    for src in range(len(carrier.states)):
        var state = carrier.states[src]
        var j = 0
        for top in range(len(tables.sigma[state.top])):
            for bottom in range(len(tables.sigma[state.bottom])):
                var child = selected_overlap_child(tables, state, top, bottom)
                if interior_overlap(tables, child):
                    var edge = carrier.rows[src][j]
                    assert_equal(edge.top_index, top)
                    assert_equal(edge.bottom_index, bottom)
                    assert_true(child == carrier.states[edge.target])
                    j += 1
        assert_equal(j, len(carrier.rows[src]))


def test_refusals() raises:
    with assert_raises():
        _ = build_carrier(4, 6, 1, 10000)
    with assert_raises():
        _ = build_carrier(4, 6, 1000, 1)
    with assert_raises():
        _ = build_carrier(4, 3, 1000, 10000)
    with assert_raises():
        _ = parikh_difference(4, CubicElt(1, 0, 0))
    assert_true(parikh_difference(4, CubicElt(4, 1, 0)) == CubicElt(0, 0, -1))
    assert_true(parikh_difference(4, CubicElt(0, 1, 0)) == CubicElt(-1, 0, 0))
    var carrier = build_carrier(4, 6, 1000, 10000)
    assert_true(verify_carrier(4, 6, carrier)[0] > 0)
    var root = carrier.states[0]
    carrier.states[0] = OverlapState(0, 0, CubicElt(0, 1))
    with assert_raises():
        _ = verify_carrier(4, 6, carrier)
    carrier.states[0] = root
    var empty = List[CarrierEdge]()
    var first = carrier.rows[0].copy()
    carrier.rows[0] = empty^
    with assert_raises():
        _ = verify_carrier(4, 6, carrier)
    carrier.rows[0] = first.copy()
    var original = carrier.rows[0][0]
    carrier.rows[0][0] = CarrierEdge(original.top_index + 1, original.bottom_index, original.target)
    with assert_raises():
        _ = verify_carrier(4, 6, carrier)
    carrier.rows[0][0] = CarrierEdge(original.top_index, original.bottom_index,
                                     (original.target + 1) % len(carrier.states))
    with assert_raises():
        _ = verify_carrier(4, 6, carrier)
    carrier.rows[0] = first^
    var diagonal = -1
    for i in range(len(carrier.states)):
        if carrier.states[i].is_coincidence() and len(carrier.rows[i]) > 1:
            diagonal = i
            break
    assert_true(diagonal >= 0)
    var diagonal_row = carrier.rows[diagonal].copy()
    _ = carrier.rows[diagonal].pop()
    with assert_raises():
        _ = verify_carrier(4, 6, carrier)
    carrier.rows[diagonal] = diagonal_row^
    assert_true(carrier.states[0].shift.is_zero())
    assert_true(not carrier.states[0].is_coincidence())
    var rank = carrier.coincidence_depths[0]
    carrier.coincidence_depths[0] = 0
    with assert_raises():
        _ = verify_carrier(4, 6, carrier)
    carrier.coincidence_depths[0] = rank + len(carrier.states)
    with assert_raises():
        _ = verify_carrier(4, 6, carrier)


def main() raises:
    test_literal_rows()
    test_refusals()
    print("r,k,packets,occurrences,zero_depth,coincidence_depth")
    for r in range(4, 12):
        for d in range(3):
            var carrier = build_carrier(r, r + d, 300000, 2400000)
            var receipt = verify_carrier(r, r + d, carrier)
            if r == 11 and d == 0:
                assert_equal(receipt[1], 60)
                assert_equal(receipt[2], 61)
            print(String(r) + "," + String(r + d) + "," + String(len(carrier.states)) + ","
                  + String(receipt[0]) + "," + String(receipt[1]) + "," + String(receipt[2]))
    print("verified 24 exact higher-determinant swap carriers")
    require_contract("Complete literal overlap rows and labelled coincidence depths replay for all 24 higher-determinant swap carriers, with refusal of incomplete rows, false ranks and exhausted caps.")
