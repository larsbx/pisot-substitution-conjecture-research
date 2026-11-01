"""Reconciled endpoints; original graph certificates replay separately."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_c_below_three_integration import mainline_piece, mainline_coverage_audit


def main() raises:
    assert_equal(mainline_piece(1, 10, 29), 1)
    assert_equal(mainline_piece(-1, 18, 53), 1)
    assert_equal(mainline_piece(1, 40, 104), 2)
    assert_equal(mainline_piece(1, 38, 99), 3)
    assert_equal(mainline_piece(-1, 32, 89), 3)
    for eps in [1, -1]:
        assert_equal(mainline_piece(eps, 32, 95), 3)
        assert_equal(mainline_piece(eps, 32, 96), 4)
        var onset = 128 + (0 if eps == 1 else 4)
        assert_equal(mainline_piece(eps, 32, onset - 1), 4)
        assert_equal(mainline_piece(eps, 32, onset), 5)
        print(mainline_coverage_audit(eps))
    assert_equal(mainline_piece(1, 37, 96), 0)
    var refused = False
    try:
        _ = mainline_piece(0, 32, 96)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = mainline_piece(1, 1000000000000000000, 0)
    except:
        refused = True
    assert_true(refused)
    require_contract("class C below-three mainline integration: bounded arithmetic cover uses T_C2 at n=3d and T_C at onset; original finite ends contain required subset; selected sector inverse and negative-c bridge endpoints; invalid sign and oversized audit inputs refuse; no new graph or PSC verdict")
