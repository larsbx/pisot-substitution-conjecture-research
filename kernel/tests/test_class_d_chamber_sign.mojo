"""Regression for the actual negative query refused in low chamber 1.

This repairs the existing exact sign contract under the symbolic-line
literature gate; it introduces no new graph or family theorem.
"""
from std.testing import assert_equal
from mojo_smoke.claims import require_contract
from psc.param_poly import qx_const, qx_affine2, qx_neg, qx_sub, tp_norm, tp_neg, tp_at_q, tp_key, tp_add, tp_sub, tp_scale, w_add, w_sub
from psc.symbolic_line import (
    Eventual, LineField, _Closure, coefficient_sign_at_positive_root,
    NORM_UNDECIDED, coefficient_sign_above_two, SymVertex,
)
from class_d_plus_positive_b_chambers import _low_wedge, _high_wedge


def main() raises:
    var ev = Eventual()
    var h = tp_norm([qx_const(-4), qx_affine2(-5,-2,-2), qx_affine2(0,-3,-4)])
    assert_equal(coefficient_sign_at_positive_root(h,ev), -1)
    assert_equal(coefficient_sign_at_positive_root(tp_neg(h),ev), 1)
    assert_equal(coefficient_sign_at_positive_root(tp_norm([qx_const(0)]),ev), 0)
    # A positive root alone does not determine t-2, nor a changing coefficient.
    assert_equal(coefficient_sign_at_positive_root(tp_norm([qx_const(-2),qx_const(1)]),ev), NORM_UNDECIDED)
    assert_equal(coefficient_sign_at_positive_root(tp_norm([qx_affine2(0,1,-1)]),ev), NORM_UNDECIDED)
    # b can be zero on this region: a positive b coefficient is not strict.
    assert_equal(coefficient_sign_at_positive_root(tp_norm([qx_affine2(0,0,1)]),ev), NORM_UNDECIDED)
    var line = _low_wedge(1).line()
    for uv in [(0,0),(1,1),(4,1),(200,200),(800,200)]:
        var field = LineField(tp_at_q(line.field.chi,uv[0],uv[1]))
        var at = Eventual()
        assert_equal(field.sign_at_beta(tp_at_q(h,uv[0],uv[1]),at), -1)
    var cl = _Closure(line^,1,Eventual())
    # Actual first refused block: source (c,x,-e_y), RUN/LAST,
    # upper margin at the smallest legal difference m=-(q-1).
    var source = SymVertex(1,0,[qx_const(0),qx_const(0),qx_const(-1)])
    var base = w_sub(w_add(cl.line.mw(source.w),cl.prefix(0,2)),cl.prefix(1,1))
    var upper = tp_sub(cl.line.t_of(base),cl.line.ell[cl.letter(1,1)])
    var rlo = qx_neg(qx_sub(cl.line.run[1],qx_const(1)))
    assert_equal(tp_key(tp_add(upper,tp_scale(cl.line.ell[2],rlo))),tp_key(h))
    assert_equal(cl.positive(h), -1)
    # High chamber: h=(beta-2)((u+2)beta+2)>0 since chi(2)<0.
    var high = _high_wedge().line()
    var hh = tp_norm([qx_const(-4),qx_affine2(-2,-2,0),qx_affine2(2,1,0)])
    # Actual high refusal: source (c,x,e_c-e_y), FIRST/RUN,
    # upper margin at m=0. Its positive sign rejects this entire block.
    var hc = _Closure(_high_wedge().line(),1,Eventual())
    var hs = SymVertex(1,0,[qx_const(0),qx_const(1),qx_const(-1)])
    var hb = w_sub(w_add(hc.line.mw(hs.w),hc.prefix(0,1)),hc.prefix(1,0))
    assert_equal(tp_key(tp_sub(hc.line.t_of(hb),hc.line.ell[hc.letter(1,0)])),tp_key(hh))
    assert_equal(coefficient_sign_at_positive_root(hh,ev), NORM_UNDECIDED)
    assert_equal(coefficient_sign_above_two(high,hh,ev), 1)
    assert_equal(coefficient_sign_above_two(high,tp_neg(hh),ev), -1)
    assert_equal(coefficient_sign_above_two(high,tp_norm([qx_const(-3),qx_const(1)]),ev), NORM_UNDECIDED)
    # A root at the proposed lower bound does not give beta>2.
    high.field = LineField(tp_norm([qx_const(-2),qx_const(0),qx_const(-1),qx_const(1)]))
    # chi(2)=2>0: a known-positive shifted polynomial cannot override this.
    assert_equal(coefficient_sign_above_two(high,hh,ev), NORM_UNDECIDED)
    high.field = LineField(tp_norm([qx_const(0),qx_const(0),qx_const(-2),qx_const(1)]))
    assert_equal(coefficient_sign_above_two(high,hh,ev), NORM_UNDECIDED)
    print("CLASS_D_CHAMBER_NEGATIVE_QUERY_CERTIFIED")
    require_contract("plus chamber sign-reader regressions: the low-1 query has negative coefficients; the high query is (beta-2)((u+2)beta+2)>0 with certified chi(2)<0; mixed signs, changing coefficients, zero boundary coefficients, and missing strict root bounds remain undecided; no carrier closure is asserted")
