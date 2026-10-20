"""Exact counter-calibrations for the single-quadrant proposal in PR #283.

These pin local failed affine fits and a changing plus-cover label, not failure
of boundary hitting or of a future chamber/upper-cover certificate. The existing
parametric-overlap literature gate applies (docs/p1b-catch-up-free-ppvc-2026-10-07.md).
"""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.param_poly import QX, qx_const, qx_neg, tp_norm, tp_at_q, tp_add, tp_sub
from psc.symbolic_line import Eventual, LineField, _least_at
from symbolic_line_certificate import ClassWedge
from a1_normal_form_census import CLASS_D


def main() raises:
    var plus = ClassWedge(CLASS_D, [4,3,1, 3,3,1, 1,2,1]).line()
    var minus = ClassWedge(CLASS_D, [6,3,1, 7,3,1, 5,2,1]).line()
    # The first refused plus bound: -1 + q*t + p*t^2 + m*(t^2-2t) > 0.
    var hp = tp_norm([qx_const(-1), plus.run[1].copy(), plus.run[0].copy()])
    var step = tp_norm([qx_const(0), qx_const(-2), qx_const(1)])
    var p1 = _least_at(plus, 1, hp, step, 200, 200, True)
    var p2 = _least_at(plus, 1, hp, step, 400, 200, True)
    var p3 = _least_at(plus, 1, hp, step, 200, 400, True)
    assert_equal(p1, -808)
    assert_equal(p2, -1408)
    assert_equal(p3, -1007)
    assert_true((p3 - p1) % 200 != 0)

    # The first refused minus bound: 1 - p*t - q*t^2 + m*(t^2-2t) >= 0.
    var hm = tp_norm([qx_const(1), qx_neg(minus.run[0]), qx_neg(minus.run[1])])
    var m1 = _least_at(minus, 1, hm, step, 200, 200, False)
    var m2 = _least_at(minus, 1, hm, step, 400, 200, False)
    assert_equal(m1, 811)
    assert_equal(m2, 1412)
    assert_true((m2 - m1) % 200 != 0)

    # Plus sealed row 12: (x,c,-5,11,-8). c=b-1 in the ClassWedge.
    var w = List[QX]([qx_const(-5), qx_const(11), qx_const(-8)])
    var lower = tp_add(plus.ell[1], plus.t_of(w))
    var upper = tp_sub(plus.ell[0], plus.t_of(w))
    for c in [199, 1999]:
        var field = LineField(tp_at_q(plus.field.chi, 200, c))
        var ev = Eventual()
        assert_equal(field.sign_at_beta(tp_at_q(lower, 200, c), ev), 1 if c == 199 else -1)
        assert_equal(field.sign_at_beta(tp_at_q(upper, 200, c), ev), 1)
    print("CLASS_D_POSITIVE_B_OBSTRUCTION_CONTROLS_PASS")
    require_contract("Class-D positive-b proposal: exact least-run bounds at (200,200),(400,200),(200,400) refute the attempted integer-affine fits; plus upper-cover row (x,c,-5,11,-8) changes realness between (a,b)=(200,200) and (200,2000); no BH counterexample or uniform closure is asserted")
