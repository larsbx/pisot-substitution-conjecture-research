"""Audit partition boundaries; symbolic graph verdicts are replayed separately."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_c_slope_three import BELOW, FINITE, MIDDLE, DIAGONAL, INHERITED_TOP, TAIL, LOWER_LINE, SlopePlan, coverage_audit, refusal_controls


def main() raises:
    var plus = SlopePlan(1, 4)
    assert_equal(plus.piece(24, 75), BELOW)
    assert_equal(plus.piece(23, 73), FINITE)
    assert_equal(plus.piece(24, 76), MIDDLE)
    assert_equal(plus.piece(24, 80), MIDDLE)
    # Omitting the bridging diagonals loses this actual target member.
    assert_equal(plus.piece(24, 81), DIAGONAL)
    assert_equal(plus.piece(24, 91), DIAGONAL)
    assert_equal(plus.piece(24, 92), INHERITED_TOP)
    assert_equal(plus.piece(24, 96), TAIL)
    var minus = SlopePlan(-1, 6)
    assert_equal(minus.piece(24, 77), BELOW)
    assert_equal(minus.piece(24, 78), LOWER_LINE)
    assert_equal(minus.piece(24, 79), LOWER_LINE)
    assert_equal(minus.piece(24, 80), MIDDLE)
    assert_equal(minus.piece(24, 81), DIAGONAL)
    assert_equal(minus.piece(24, 95), DIAGONAL)
    assert_equal(minus.piece(24, 96), INHERITED_TOP)
    assert_equal(minus.piece(24, 100), TAIL)
    for eps in [1, -1]:
        assert_true(coverage_audit(SlopePlan(eps, 8)).startswith("COVERAGE_AUDIT"))
    assert_true(refusal_controls().startswith("SIGN_CONTROL"))
    var refused = False
    try:
        _ = plus.piece(1000000000000000000, 0)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = SlopePlan(0, 8)
    except:
        refused = True
    assert_true(refused)
    require_contract("class C slope-three partition: finite small-gap ends, unimodular middle-cone inverse, bridging diagonals, two lower-edge lines, inherited four top layers and tail; boundary and omission controls; bounded coverage audit refuses before integer arithmetic")
