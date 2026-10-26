"""Exact coefficient certificates for the class-A l=0 boundary-distance rays.

This does NOT certify boundary hitting, the occurrence packet target, G1 or PSC.
Parameters n>=k+3 for eps=-1; n>=2(k+2) for eps=+1,
d=2n+6eps+5-k. Root signs and positivity constraints are stated and
proved in docs/class-a-boundary-layer-2026-10-26.md. This module checks
their polynomial identities for both signs in existing exact Z[n,k].
"""
from psc.param_poly import (
    QX, qx_affine, qx_affine2, qx_const, qx_add, qx_sub,
    qx_mul, qx_is_zero,
)


def _mul3(a: QX, b: QX, c: QX) -> QX:
    return qx_mul(qx_mul(a,b),c)


def _require_equal(a: QX, b: QX) raises:
    if not qx_is_zero(qx_sub(a,b)):
        raise Error("class-A boundary-layer polynomial identity failed")


def _d(sign: Int) -> QX:
    var n=qx_affine(0,1)
    var k=qx_affine2(0,0,1)
    return qx_sub(qx_add(qx_mul(qx_const(2),n),qx_const(6*sign+5)),k)


def _p(sign: Int, t: QX) raises -> QX:
    if sign!=1 and sign!=-1:
        raise Error("boundary sign must be +/-1")
    var n=qx_affine(0,1)
    var d=_d(sign)
    var A=qx_add(n,qx_const(3+sign))
    var B=qx_sub(qx_add(n,qx_const(2+3*sign)),d)
    var t2=qx_mul(t,t)
    var t3=qx_mul(t2,t)
    return qx_sub(qx_add(qx_sub(t3,qx_mul(A,t2)),qx_mul(B,t)),qx_const(2*sign))


def _check_boundary_polynomials(sign: Int, damage: Bool=False) raises:
    """Check identities universally as equalities in the integer ring Z[n,k].

    All sign comparisons that isolate roots are made from the integer bounds
    on n,k and shown explicitly in the accompanying human derivation.
    """
    if sign!=1 and sign!=-1:
        raise Error("unsupported class-A determinant sign")
    var n=qx_affine(0,1)
    var k=qx_affine2(0,0,1)
    var m=qx_add(k,qx_const(2))
    var d=_d(sign)
    var one=qx_const(1)
    var n2=qx_mul(n,n)
    var n3=qx_mul(n2,n)

    # Integer endpoint identities: P(-1), P(1), P(2), P(-2).
    _require_equal(_p(sign,qx_const(-1)),qx_mul(qx_const(-1),qx_add(k,one)))
    _require_equal(_p(sign,qx_const(1)),qx_mul(qx_const(-1),d))
    _require_equal(_p(sign,qx_const(2)),qx_mul(qx_const(-2),qx_add(n,d)))
    _require_equal(_p(sign,qx_const(-2)),
                   qx_mul(qx_const(-2),qx_add(qx_add(n,k),qx_const(7))))

    # P(-1+m/n)*n^3 = n^3+(4-eps)m n^2-(6+eps)m^2 n+m^3.
    var num=qx_sub(m,n)
    var num2=qx_mul(num,num)
    var A=qx_add(n,qx_const(3+sign))
    var B=qx_sub(qx_add(n,qx_const(2+3*sign)),d)
    var lhs=qx_sub(qx_add(qx_sub(qx_mul(num2,num),
                          _mul3(A,num2,n)),_mul3(B,num,n2)),
                          qx_mul(qx_const(2*sign),n3))
    var m2=qx_mul(m,m)
    var rhs=qx_add(
        qx_sub(qx_add(n3,_mul3(qx_const(4-sign),m,n2)),
               _mul3(qx_const(6+sign),m2,n)),
        qx_mul(m2,m))
    if damage:
        rhs=qx_add(rhs,one)
    _require_equal(lhs,rhs)

    if sign==-1:
        var atlo=qx_add(
            qx_sub(qx_add(qx_mul(k,qx_add(n,qx_const(2))),qx_const(2)),
                   qx_add(n2,qx_mul(qx_const(2),n))),qx_const(0))
        var athi=qx_add(qx_add(qx_mul(k,qx_add(n,qx_const(3))),
                         qx_mul(qx_const(3),n)),qx_const(11))
        _require_equal(_p(sign,qx_add(n,qx_const(2))),atlo)
        _require_equal(_p(sign,qx_add(n,qx_const(3))),athi)
    else:
        var atlo=qx_sub(qx_mul(k,qx_add(n,qx_const(4))),
                   qx_add(qx_add(n2,qx_mul(qx_const(10),n)),qx_const(26)))
        var athi=qx_add(qx_mul(k,qx_add(n,qx_const(6))),
                   qx_add(qx_add(n2,qx_mul(qx_const(12),n)),qx_const(34)))
        _require_equal(_p(sign,qx_add(n,qx_const(4))),atlo)
        _require_equal(_p(sign,qx_add(n,qx_const(6))),athi)


def certify_class_a_boundary_layer() raises:
    for sign in [-1,1]:
        _check_boundary_polynomials(sign)
        print("CLASS_A_BOUNDARY_LAYER", "eps", sign,
              "identities=exact_Z[n,k]", "scope=l0", "BH=false")
    print("CLASS_A_BOUNDARY_LAYER", "global_PSC=false",
          "independent_review=pending")
