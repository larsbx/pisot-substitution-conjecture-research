"""Exact all-parameter sign certificates for class-A l=0 boundary rays.

The two variables of psc.param_poly.QX are now (t,k) >= (0,0):
 eps=-1: n=k+3+t;  eps=+1: n=2(k+2)+t;
 d=2*n+6*eps+5-k. The cone verifier checks *all coefficients*
 are nonnegative and the constant coefficient is positive for a strict
 sign. Thus these are infinite-family certificates, not a finite census.

No numeric root approximations, division by zero, appeal to independent
lengths, or unimodular reduction. Only the sign lemma / geometry barrier,
not occurrence-level BH, is certified.
"""
from finite_linear_algebra.scalar import q_int
from psc.exact import q_sign
from psc.param_poly import (
    QX, qx_add, qx_sub, qx_mul, qx_affine, qx_affine2,
    qx_const, qx_const_term, qx_is_zero,
)


def _same(a: QX, b: QX) raises:
    if not qx_is_zero(qx_sub(a,b)):
        raise Error("boundary chamber exact polynomial identity mismatch")


def _cone_nonnegative(p: QX) raises:
    # All coefficients nonnegative is a sound sufficient certificate on
    # t>=0,k>=0, rather than a sample-based extrapolation.
    for row in p:
        for coefficient in row:
            if q_sign(coefficient) < 0:
                raise Error("boundary chamber cone sign not certified")


def _cone_positive(p: QX) raises:
    _cone_nonnegative(p)
    if q_sign(qx_const_term(p)) <= 0:
        raise Error("boundary chamber strict sign lacks positive constant")


def _twice(p: QX) -> QX:
    return qx_mul(qx_const(2),p)


def chamber_parameters(eps: Int) raises -> List[QX]:
    """Return exact (n,d,k,t) polynomials on the full admissible t,k cone."""
    if eps != -1 and eps != 1:
        raise Error("unsupported determinant sign")
    var t=qx_affine(0,1)
    var k=qx_affine2(0,0,1)
    var n=qx_add(t,qx_add(qx_mul(qx_const(1 if eps==-1 else 2),k),
                           qx_const(3 if eps==-1 else 4)))
    var d=qx_sub(qx_add(_twice(n),qx_const(6*eps+5)),k)
    return [n,d,k,t]


def char_at(eps: Int, n: QX, d: QX, x: QX) raises -> QX:
    if eps != -1 and eps != 1:
        raise Error("invalid sign in characteristic cubic")
    var x2=qx_mul(x,x)
    var a=qx_add(n,qx_const(3+eps))
    var b=qx_sub(qx_add(n,qx_const(2+3*eps)),d)
    return qx_sub(
        qx_add(qx_sub(qx_mul(x2,x),qx_mul(a,x2)),qx_mul(b,x)),
        qx_const(2*eps))


def certify_chamber_signs(eps: Int, corrupt: Bool=False) raises:
    """Exact sign proof on all t,k>=0.

    Three disjoint root intervals:
      minus: (-1,-1+(k+2)/n), (0,1), (n+2,n+3);
      plus:  (-1,-1+(k+2)/n), (-1+(k+2)/n,0), (n+4,n+6).
    The rational endpoint is numerator-certified with denominator n^3>0.
    Integer endpoint signs and the rational root test prove irreducibility.
    """
    var param=chamber_parameters(eps)
    var n=param[0].copy()
    var d=param[1].copy()
    var k=param[2].copy()
    var one=qx_const(1)
    var m=qx_add(k,qx_const(2))
    var nn=qx_mul(n,n)
    var nnn=qx_mul(nn,n)
    # The run length and PIP admissibility are genuine cone statements.
    _cone_positive(n)
    _cone_positive(qx_add(n,qx_const(eps)))
    _cone_positive(qx_sub(d,n))      # l=floor(n/d)=0
    _cone_positive(d)
    _cone_nonnegative(k)            # PIP boundary distance

    _same(char_at(eps,n,d,qx_const(-1)),
          qx_sub(qx_const(-1),k))
    _same(char_at(eps,n,d,one),qx_sub(qx_const(0),d))
    _same(char_at(eps,n,d,qx_const(2)),
          qx_sub(qx_const(0),_twice(qx_add(n,d))))
    _same(char_at(eps,n,d,qx_const(-2)),
          qx_sub(qx_const(0),_twice(qx_add(qx_add(n,k),qx_const(7)))))
    _cone_positive(qx_add(k,one))  # -P(-1)>0
    _cone_positive(d)             # -P(1)>0
    _cone_positive(qx_add(n,d))   # -P(2)>0
    _cone_positive(qx_add(qx_add(n,k),qx_const(7))) # -P(-2)>0

    # Clear denominator of P(-1+m/n) exactly.  This is a full
    # coefficient identity in Z[t,k], never a rational floating test.
    var znum=qx_sub(m,n)
    var lhs=qx_sub(
        qx_add(qx_sub(qx_mul(qx_mul(znum,znum),znum),
            qx_mul(qx_mul(qx_add(n,qx_const(3+eps)),
                         qx_mul(znum,znum)),n)),
            qx_mul(qx_mul(qx_sub(qx_add(n,qx_const(2+3*eps)),d),
                              znum),nn)),
        qx_mul(qx_const(2*eps),nnn))
    var mm=qx_mul(m,m)
    var rhs=qx_add(
        qx_sub(qx_add(nnn,
                    qx_mul(qx_mul(qx_const(4-eps),m),nn)),
               qx_mul(qx_mul(qx_const(6+eps),mm),n)),
        qx_mul(mm,m))
    if corrupt:
        rhs=qx_add(rhs,one)
    _same(lhs,rhs)
    _cone_positive(rhs)

    if eps==-1:
        # The next two signs pin (0,1) and (n+2,n+3).
        _same(char_at(eps,n,d,qx_const(0)),qx_const(2))
        _cone_positive(qx_sub(qx_const(0),char_at(eps,n,d,qx_add(n,qx_const(2)))))
        _cone_positive(char_at(eps,n,d,qx_add(n,qx_const(3))))
        # beta<n+3 and d >= n+2 => d>beta-1 even at t=0.
        _cone_nonnegative(qx_sub(d,qx_add(n,qx_const(2))))
    else:
        _same(char_at(eps,n,d,qx_const(0)),qx_const(-2))
        _cone_positive(qx_sub(qx_const(0),char_at(eps,n,d,qx_add(n,qx_const(4)))))
        _cone_positive(char_at(eps,n,d,qx_add(n,qx_const(6))))
        # beta<n+6 and d>=n+5.
        _cone_nonnegative(qx_sub(d,qx_add(n,qx_const(5))))

    print("CLASS_A_BOUNDARY_CHAMBER eps",eps,
          "all_t_k_nonnegative=true",
          "three_real_Pisot_roots=bracketed",
          "u_gt_one=true",
          "same_letter_run_disjoint=true",
          "BH=false")


def certify_all_chambers() raises:
    certify_chamber_signs(-1)
    certify_chamber_signs(1)
    print("CLASS_A_BOUNDARY_CHAMBER global_PSC=false",
          "human_review=pending")
