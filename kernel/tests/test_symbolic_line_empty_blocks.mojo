"""Uniform empty-block controls for the positive-b class-D wedges.

These prove why the two first non-affine fits audited in PR #283 must never be
requested: the corresponding legal run-position blocks are geometrically empty
on the whole certified wedge region.
"""
from std.testing import assert_true
from mojo_smoke.claims import require_contract
from psc.param_poly import QX, qx_const, tp_add, tp_sub, w_add, w_sub
from psc.symbolic_line import Eventual, SymVertex, _Closure, certify_wedge_pisot
from symbolic_line_certificate import ClassWedge
from a1_normal_form_census import CLASS_D


def _w(x: Int, c: Int, y: Int) -> List[QX]:
    return [qx_const(x), qx_const(c), qx_const(y)]


def main() raises:
    # Plus source (x,x,e_c), top FIRST / bottom RUN.
    # At m=0 the translation is already > ell_x, so the whole legal block
    # m>=0 is beyond the upper wall.
    var plus = ClassWedge(CLASS_D, [4,3,1, 3,3,1, 1,2,1]).line()
    var ep = Eventual()
    var cp = certify_wedge_pisot(plus, ep)
    assert_true(cp.holds)
    var pcl = _Closure(plus^, cp.ell_sign, ep^)
    var pv = SymVertex(0,0,_w(0,1,0))
    var pbase = w_sub(
        w_add(pcl.line.mw(pv.w), pcl.prefix(pv.bottom,1)),
        pcl.prefix(pv.top,0),
    )
    var pt = pcl.line.t_of(pbase)
    var pupper = tp_sub(pt, pcl.line.ell[pcl.letter(pv.top,0)])
    assert_true(pcl.positive(pupper) >= 0)

    # Minus source (c,c,-e_x), top RUN / bottom FIRST.
    # The largest legal m is 0; even there the translation is below -ell_c,
    # so every smaller legal m is outside the lower wall.
    var minus = ClassWedge(CLASS_D, [6,3,1, 7,3,1, 5,2,1]).line()
    var em = Eventual()
    var cm = certify_wedge_pisot(minus, em)
    assert_true(cm.holds)
    var mcl = _Closure(minus^, cm.ell_sign, em^)
    var mv = SymVertex(1,1,_w(-1,0,0))
    var mbase = w_sub(
        w_add(mcl.line.mw(mv.w), mcl.prefix(mv.bottom,0)),
        mcl.prefix(mv.top,1),
    )
    var mt = mcl.line.t_of(mbase)
    var mlower = tp_add(mcl.line.ell[mcl.letter(mv.bottom,0)], mt)
    assert_true(mcl.positive(mlower) <= 0)
    require_contract("positive-b class-D first non-affine occurrence blocks are uniformly geometrically empty on their certified wedges")
