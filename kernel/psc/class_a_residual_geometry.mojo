"""Uniform determinant-two class-A geometry for both signs, variable gap d.

For q=n, p=n+d, r=n+eps with eps=+1 or -1, verify in the
existing exact two-parameter Q[n,d][h] algebra:

  h^3 chi(1+1/h) = P = 1-(n+eps)h-(n+d+1-eps)h^2-dh^3,
  L=(1+(d+1-eps)h+d h^2, 1+(1-eps)h, 1+h),
  h M^T L-(1+h)L = -P (each of three columns).

These are coefficient-wise identities, not finite substitutions or signs.
A uniform countermodel also proves the accepted 89-row d=1 carrier is
NOT a real-overlap carrier for the next d=2 plus line, for all n>=4.
See docs/class-a-residual-geometry-2026-10-22.md.
"""
from psc.param_poly import (
    QX, TPoly, qx_const, qx_affine, qx_affine2, qx_add, qx_sub,
    tp_const, tp_t, tp_add, tp_sub, tp_scale, tp_mul, tp_deg,
)


def _require_poly_equal(left: TPoly, right: TPoly) raises:
    if tp_deg(tp_sub(left,right))>=0:
        raise Error("uniform class-A polynomial identity failed")


def _require_qx_equal(left: QX, right: QX) raises:
    from psc.param_poly import qx_is_zero
    if not qx_is_zero(qx_sub(left,right)):
        raise Error("uniform class-A integral-update identity failed")


def _polynomial(sign: Int) raises -> TPoly:
    if sign!=1 and sign!=-1:
        raise Error("class-A determinant sign must be +/-1")
    var n=qx_affine(0,1)
    var d=qx_affine2(0,0,1)
    var h=tp_t()
    var h2=tp_mul(h,h)
    var h3=tp_mul(h2,h)
    var linear=qx_add(n,qx_const(sign))
    var quadratic=qx_add(qx_add(n,d),qx_const(1-sign))
    return tp_sub(tp_const(qx_const(1)),
        tp_add(tp_add(tp_scale(h,linear),tp_scale(h2,quadratic)),tp_scale(h3,d)))


def _lengths(sign: Int) raises -> List[TPoly]:
    if sign!=1 and sign!=-1:
        raise Error("invalid class-A sign")
    var d=qx_affine2(0,0,1)
    var h=tp_t()
    var h2=tp_mul(h,h)
    var one=tp_const(qx_const(1))
    return [
        tp_add(tp_add(one,tp_scale(h,qx_add(d,qx_const(1-sign)))),tp_scale(h2,d)),
        tp_add(one,tp_scale(h,qx_const(1-sign))),
        tp_add(one,h),
    ]


def _check_columns(sign: Int) raises:
    var n=qx_affine(0,1)
    var d=qx_affine2(0,0,1)
    var h=tp_t()
    var one=tp_const(qx_const(1))
    var beta_h=tp_add(one,h)
    var H=tp_mul(h,h)
    var P=_polynomial(sign)
    var L=_lengths(sign)
    # M=[[2,1,1],[0,1,1],[n+d,n,n+sign]].
    var ml0=tp_add(tp_scale(L[0],qx_const(2)),tp_scale(L[2],qx_add(n,d)))
    var ml1=tp_add(tp_add(L[0],L[1]),tp_scale(L[2],n))
    var ml2=tp_add(tp_add(L[0],L[1]),tp_scale(L[2],qx_add(n,qx_const(sign))))
    for i in range(3):
        var col=ml0 if i==0 else ml1 if i==1 else ml2
        _require_poly_equal(tp_add(tp_sub(tp_mul(h,col),tp_mul(beta_h,L[i])),P),tp_const(qx_const(0)))
    # Expand h^3 f(1+1/h), where f(t) is the exact incidence cubic.
    var plus=tp_add(one,h)
    var cube=tp_mul(tp_mul(plus,plus),plus)
    var quadratic=tp_scale(tp_mul(tp_mul(plus,plus),h),qx_add(n,qx_const(sign+3)))
    var linear=tp_scale(tp_mul(tp_mul(plus,H),one),
        qx_sub(qx_add(n,qx_const(2+3*sign)),d))
    var constant=tp_scale(tp_mul(H,h),qx_const(2*sign))
    var chi=tp_sub(tp_add(tp_sub(cube,quadratic),linear),constant)
    _require_poly_equal(chi,P)
    # Length ordering: x>y>c for sign +1, x>c>y for sign -1.
    var gap=tp_add(tp_scale(h,d),tp_scale(H,d))
    _require_poly_equal(tp_sub(L[0],L[1]),gap)
    if sign==1:
        _require_poly_equal(tp_sub(L[2],L[1]),h)
    else:
        _require_poly_equal(tp_sub(L[1],L[2]),h)
    print("CLASS_A_GENERAL_GEOMETRY", "sign",sign,
          "coefficients=exact", "gap=d", "q=unbounded", "h_positive_root=conditional")


def _check_child_columns(sign: Int) raises:
    """Verify formula for the integral offset update on each basis vector."""
    if sign!=1 and sign!=-1:
        raise Error("invalid class-A sign")
    var n=qx_affine(0,1)
    var d=qx_affine2(0,0,1)
    for basis in range(3):
        var k=1 if basis==0 else 0
        var y=1 if basis==2 else 0
        var s=1
        var got_k=qx_const(k+s)
        var got_c=qx_const(s-k)
        var got_y=qx_add(qx_add(n,qx_const(sign*y)),
                         qx_const(0) if k==0 else d)
        var want_k=qx_const(2 if basis==0 else 1)
        var want_c=qx_const(0 if basis==0 else 1)
        var want_y=qx_add(n,
            d if basis==0 else qx_const(sign if basis==2 else 0))
        _require_qx_equal(got_k,want_k)
        _require_qx_equal(got_c,want_c)
        _require_qx_equal(got_y,want_y)
        # Child coordinate sum before the proper-prefix correction.
        _require_qx_equal(qx_add(qx_add(got_k,got_c),got_y),
            qx_add(qx_add(qx_add(n,qx_const(2)),qx_const(sign*y)),
                   d if k==1 else qx_const(0)))


def _check_d2_nontransfer() raises:
    """The d=1 y,y row with (s,y,k)=(0,-2,-n) fails for d=2.

    The row is [2,2,0,-2,-1,0,0,0] from the 89-row template.
    Its offset is w=(-n,n+2,-2). Its translated lower margin equals
    -1+h+4h^2+4h^3 at the unique positive root of P(n,h).
    For n>=4, that root lies in (0,1/5), so the margin is <=-76/125<0.
    """
    from psc.class_a_typed_carrier import template_rows
    var exists=False
    for row in template_rows():
        if len(row)==8 and row[0]==2 and row[1]==2 and row[2]==0 and row[3]==-2 and row[4]==-1 and row[5]==0 and row[6]==0 and row[7]==0:
            exists=True
    if not exists:
        raise Error("missing archived d=1 typed witness row")
    var h=tp_t()
    var h2=tp_mul(h,h)
    var h3=tp_mul(h2,h)
    var n=qx_affine(0,1)
    var raw=tp_sub(tp_add(tp_const(qx_const(1)),h),
        tp_add(tp_scale(tp_mul(h,tp_add(tp_const(qx_const(1)),h)),qx_add(n,n)),tp_scale(h,qx_const(2))))
    var reduced=tp_add(tp_add(tp_add(tp_const(qx_const(-1)),h),
                              tp_scale(h2,qx_const(4))),tp_scale(h3,qx_const(4)))
    # The comparison is to d=2, not the variable-gap identity.
    var p2=tp_sub(tp_const(qx_const(1)),
        tp_add(tp_add(tp_scale(h,qx_add(n,qx_const(1))),
                      tp_scale(h2,qx_add(n,qx_const(2)))),tp_scale(h3,qx_const(2))))
    _require_poly_equal(raw,tp_add(reduced,tp_scale(p2,qx_const(2))))
    # The root h<1/5, by P(n,0)=1 and 125*P(n,1/5)=88-30n<0.
    # The reduced margin is bounded above by -1+1/5+4/25+4/125=-76/125.
    if 88-30*4>=0 or (-125+25+20+4)!=-76:
        raise Error("uniform nontransfer inequality budget failed")
    print("CLASS_A_D2_NONTRANSFER", "all_n>=4", "source_d1_row=y,y,0,-2,-n",
          "strict_lower_margin_negative=true", "not_a_hitting_counterexample=true")


def certify_general_class_a_geometry() raises:
    for sign in [-1,1]:
        _check_columns(sign)
        _check_child_columns(sign)
    _check_d2_nontransfer()
    print("CLASS_A_RESIDUAL_NORMAL_FORM", "both_signs=coefficient_checked",
          "status=geometry_only", "uniform_seed_productivity=false")
