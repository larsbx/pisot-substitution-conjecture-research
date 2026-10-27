"""All-chamber first/first classification of both T_m children of the seed.

Exact polynomial identities in beta over Q[t,k], plus written ordered-field
sign implications. Not a complete T_m child classifier or a descending rank.
"""
from psc.class_a_boundary_signs import chamber_parameters, _same, _cone_positive
from psc.class_a_boundary_run_pairs import certify_run_pair_chambers
from psc.param_poly import (
    QX, TPoly, qx_const, qx_add, qx_sub, qx_mul, qx_neg, qx_shift,
    tp_norm, tp_coeff, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic,
)


def _poly(a: QX, b: QX, c: QX, d: QX) -> TPoly:
    var out=TPoly()
    out.append(a.copy())
    out.append(b.copy())
    out.append(c.copy())
    out.append(d.copy())
    return tp_norm(out)


def _linear(a: QX, b: QX) -> TPoly:
    return _poly(a,b,qx_const(0),qx_const(0))


def _equal(a: TPoly, b: TPoly) raises:
    for i in range(max(len(a),len(b))):
        _same(tp_coeff(a,i),tp_coeff(b,i))


def _cubic(eps: Int, n: QX, d: QX) -> TPoly:
    return _poly(qx_const(-2*eps),qx_sub(qx_add(n,qx_const(2+3*eps)),d),
                 qx_neg(qx_add(n,qx_const(3+eps))),qx_const(1))


def _lower(eps: Int, m: Int, d: QX) -> TPoly:
    # beta*(B+a) = m*beta^2+(1-d)*beta-eps.
    return _poly(qx_const(-eps),qx_sub(qx_const(1),d),qx_const(m),qx_const(0))


def _upper(eps: Int, m: Int, n: QX, d: QX) raises -> TPoly:
    # beta*(beta-1)*(a-B), reduced modulo the characteristic cubic.
    var raw=_poly(qx_const(eps),qx_add(d,qx_const(-1-eps)),
                   qx_add(d,qx_const(m+1)),qx_const(-m))
    return tp_mod_monic(raw,_cubic(eps,n,d))


def certify_next_first(corrupt: Bool=False) raises:
    certify_run_pair_chambers()
    var minus=chamber_parameters(-1)
    var n=minus[0].copy()
    var d=minus[1].copy()
    var k=minus[2].copy()
    var t=minus[3].copy()
    var one=qx_const(1)
    var Xminus1=_linear(qx_const(-1),one)
    var G=_lower(-1,1,d)
    var A=qx_sub(qx_mul(qx_sub(t,one),qx_sub(d,one)),qx_add(t,qx_const(4)))
    var C=qx_sub(qx_const(3),t)
    # f=(X+t-1)G+A*X+(3-t).
    var rhs=tp_add(tp_mul(_linear(qx_sub(t,one),one),G),_linear(C,A))
    if corrupt:
        rhs=tp_add(rhs,_linear(one,qx_const(0)))
    _equal(_cubic(-1,n,d),rhs)
    # t>=2: A>0 and A+C>0, so A*beta+C>0 since beta>1.
    # The quotient beta+t-1>0; hence G(beta)<0, rejecting first/first.
    _cone_positive(qx_shift(A,2,0))
    _cone_positive(qx_shift(qx_add(A,C),2,0))
    # t=0,1: beta-d+b > n+3-d=1-t>=0.
    _same(qx_sub(qx_add(n,qx_const(3)),d),qx_sub(one,t))
    # The other side for m=1 is always strictly positive.
    var J1=_upper(-1,1,n,d)
    _equal(J1,_poly(one,qx_sub(n,one),qx_sub(d,n),qx_const(0)))
    for coefficient in J1:
        _cone_positive(coefficient)
    # m=2: upper margin = -((k+2)*beta+3)/beta < 0.
    _equal(_upper(-1,2,n,d),tp_scale(
        tp_mul(Xminus1,_linear(qx_const(3),qx_add(k,qx_const(2)))),qx_const(-1)))
    _cone_positive(qx_add(k,qx_const(2)))

    var plus=chamber_parameters(1)
    n=plus[0].copy()
    d=plus[1].copy()
    k=plus[2].copy()
    t=plus[3].copy()
    # m=1: beta-d+b < n+7-d < 0, for every plus member.
    _cone_positive(qx_sub(d,qx_add(n,qx_const(7))))
    # m=2: 4f=(2X+2-k)G-C*X-(k+6), C positive.
    # 2beta+2-k>2(n+4)+2-k>0, so G(beta)>0.
    var G2=_lower(1,2,d)
    var Cp=qx_add(qx_add(qx_mul(qx_const(3),qx_mul(k,k)),
                         qx_mul(qx_const(16),k)),
                   qx_add(qx_mul(qx_const(2),qx_mul(k,t)),qx_const(2)))
    var quotient=_linear(qx_sub(qx_const(2),k),qx_const(2))
    var rem=_linear(qx_neg(qx_add(k,qx_const(6))),qx_neg(Cp))
    _equal(tp_scale(_cubic(1,n,d),qx_const(4)),tp_add(tp_mul(quotient,G2),rem))
    _cone_positive(Cp)
    _cone_positive(qx_add(k,qx_const(6)))
    _cone_positive(qx_sub(qx_add(qx_mul(qx_const(2),n),qx_const(10)),k))
    # m=2: upper margin = ((6-k)*beta+3)/beta.
    # Positive at k<=6; at k>=7 it is <= -beta+3<0.
    _equal(_upper(1,2,n,d),tp_mul(Xminus1,
        _linear(qx_const(3),qx_sub(qx_const(6),k))))
    _cone_positive(qx_neg(qx_shift(qx_sub(qx_const(6),k),0,7)))
    _cone_positive(qx_add(n,one))  # beta>n+4>3
    # m=3: every reduced upper coefficient is strictly negative.
    var J3=_upper(1,3,n,d)
    for coefficient in J3:
        _cone_positive(qx_neg(coefficient))
    print("CLASS_A_BOUNDARY_NEXT_FIRST minus_T1_iff_t_le_1=true",
          "plus_T2_iff_k_le_6=true", "other_Tm_first_first=false",
          "all_k_t=true", "closed_carrier=false", "BH=false")


def next_first_allowed(eps: Int, k: Int, t: Int, m: Int) raises -> Bool:
    if (eps!=-1 and eps!=1) or k<0 or t<0:
        raise Error("invalid boundary chamber")
    var r=2 if eps==1 and k<=3 else 1
    if m!=r and m!=r+1:
        raise Error("m not one of the actual seed run/run targets")
    return (m==1 and t<=1) if eps==-1 else (m==2 and k<=6)
