"""Scope and exact graph/depth calibration for the residual b=0 edge."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_d_boundary import boundary_member, boundary_probe


def main() raises:
    var x = boundary_member(1, 0)
    assert_equal(x[0], List[Int]([0, 2, 2, 2, 1]))
    assert_equal(x[1], List[Int]([1, 2, 2, 0]))
    assert_equal(x[2], List[Int]([1, 1]))
    assert_equal(boundary_probe(1, 0), List[Int]([3, 2, 0, 1026, 6, 0]))
    assert_equal(boundary_probe(1, 1), List[Int]([6, 5, 2, 977, 6, 0]))
    assert_equal(boundary_probe(-1, 0), List[Int]([5, 6, 4, 148, 4, 0]))
    assert_equal(boundary_probe(-1, 1), List[Int]([8, 9, 6, 145, 4, 0]))
    assert_equal(boundary_probe(1, 2), List[Int]([9, 8, 4, 887, 6, 0]))
    assert_equal(boundary_probe(1, 3), List[Int]([12, 11, 6, 868, 6, 0]))
    assert_equal(boundary_probe(-1, 2), List[Int]([11, 12, 8, 145, 4, 0]))
    assert_equal(boundary_probe(-1, 3), List[Int]([14, 15, 10, 145, 4, 0]))
    var refused = False
    try:
        _ = boundary_probe(1, 0, 1)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = boundary_member(1, 9)
    except:
        refused = True
    assert_true(refused)
    require_contract("bounded class-D b=0 replay: eight parameter members, all-seed graph sizes and half-depths, state-cap and parameter-limit refusal; no family-wide hitting claim")
