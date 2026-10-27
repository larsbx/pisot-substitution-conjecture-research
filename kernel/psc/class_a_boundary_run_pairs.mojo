"""Uniform exact relative-run index classifier for seed overlap (x,c,0).

Parent images x y^(n+d) x and c y^n x.  A paired run occurrence at
top index i and bottom index j (both y) has geometric shift
    (j-i-u)*L_y, u=d/(beta-1).
The overlap is strict iff abs(j-i-u)<1.

The existing Z[t,k] spectral certificate yields 1<u<2 for eps=-1;
for eps=+1, the exact sign of 8*f(1+d/2) gives:
    2<u<3 for 0<=k<=3, and 1<u<2 for k>=4.
No rounded real eigenvalues enter these tests. This classification is
complete ONLY for run/run children of (x,c,0), not arbitrary children,
not BH, and not a statement about a strict SCC.
"""
from finite_linear_algebra.scalar import q_int
from psc.class_a_boundary_signs import (
    chamber_parameters, char_at, certify_chamber_signs,
    _same, _cone_positive,
)
from psc.param_poly import (
    QX, qx_add, qx_sub, qx_mul, qx_neg, qx_const,
    qx_scale, qx_shift,
)


def _cube(p: QX) -> QX:
    return qx_mul(qx_mul(p,p),p)


def doubled_perron_test() raises -> QX:
    """Return F(t,k)=8f(1+d/2), checked with integer coefficients."""
    var params=chamber_parameters(1)
    var n=params[0].copy()
    var d=params[1].copy()
    var z=qx_add(d,qx_const(2)) # 2*(1+d/2)
    return qx_sub(
        qx_add(
            qx_sub(_cube(z),qx_mul(qx_mul(qx_const(2),
                qx_add(n,qx_const(4))),qx_mul(z,z))),
            qx_mul(qx_mul(qx_const(4),
                qx_sub(qx_add(n,qx_const(5)),d)),z)),
        qx_const(16))


def _fix_k(p: QX, kval: Int) raises -> QX:
    if kval<0:
        raise Error("boundary distance k must be nonnegative")
    # Source QX rows are coefficients of k^j, each a polynomial in t.
    var out=qx_const(0)
    var power=1
    for j in range(len(p)):
        var term=QX()
        term.append(p[j].copy())
        out=qx_add(out,qx_scale(term,q_int(power)))
        power*=kval
    return out^


def certify_run_pair_chambers(corrupt: Bool=False) raises:
    certify_chamber_signs(-1)
    certify_chamber_signs(1)

    # For minus, beta>n+2 => beta-1>n+1, and
    # 2(n+1)-d=k+3>0. Earlier theorem ensures u>1.
    var minus=chamber_parameters(-1)
    var k=minus[2].copy()
    var n=minus[0].copy()
    var d=minus[1].copy()
    _same(qx_sub(qx_mul(qx_const(2),
                  qx_add(n,qx_const(1))),d),qx_add(k,qx_const(3)))
    _cone_positive(qx_add(k,qx_const(3)))

    # For plus, beta>n+4 => beta-1>n+3, and
    # 3(n+3)-d=3k+t+2>0: this gives 1<u<3.
    var plus=chamber_parameters(1)
    var np=plus[0].copy()
    var dp=plus[1].copy()
    var kp=plus[2].copy()
    var tp=plus[3].copy()
    _same(qx_sub(qx_mul(qx_const(3),
                 qx_add(np,qx_const(3))),dp),
          qx_add(qx_add(qx_mul(qx_const(3),kp),tp),qx_const(2)))
    _cone_positive(qx_sub(qx_mul(qx_const(3),
                  qx_add(np,qx_const(3))),dp))

    # Since the two other real roots are in (-1,1), and
    # X=1+d/2>1, sign(f(X)) distinguishes X<beta and X>beta:
    # positive => u>2; negative => u<2.
    var F=doubled_perron_test()
    var kk=kp.copy()
    var tt=tp.copy()
    # Independent expanded identity, with first parameter t, second k.
    var expected=qx_add(
        qx_sub(
          qx_add(qx_add(qx_const(1349),
              qx_mul(qx_const(256),tt)),
              qx_mul(qx_const(12),qx_mul(tt,tt))),
          qx_mul(qx_const(15),kk)),
        qx_neg(qx_const(0)))
    # Full formula in Z[t,k]:
    # F=-9k^3-12k^2t-93k^2-4kt^2-44kt-15k
    #    +12t^2+256t+1349.
    var k2=qx_mul(kk,kk)
    expected=qx_sub(expected,qx_mul(qx_const(93),k2))
    expected=qx_sub(expected,qx_mul(qx_const(9),qx_mul(k2,kk)))
    expected=qx_sub(expected,qx_mul(qx_const(12),qx_mul(k2,tt)))
    expected=qx_sub(expected,qx_mul(qx_const(4),qx_mul(kk,qx_mul(tt,tt))))
    expected=qx_sub(expected,qx_mul(qx_const(44),qx_mul(kk,tt)))
    if corrupt:
        expected=qx_add(expected,qx_const(1))
    _same(F,expected)

    # Every fixed k=0,1,2,3 has all nonnegative t coefficients with
    # strictly positive constant, so f(1+d/2)>0 -> u>2.
    for small_k in range(4):
        _cone_positive(_fix_k(F,small_k))
    # For every k>=4, substitute k=4+q (q>=0);
    # -F(t,4+q) has all nonnegative coefficients, positive constant,
    # so f(1+d/2)<0 -> u<2.
    _cone_positive(qx_neg(qx_shift(F,0,4)))
    print("CLASS_A_BOUNDARY_RUN_PAIRS eps=-1 delta={1,2}",
          "eps=+1 k<=3 delta={2,3}",
          "eps=+1 k>=4 delta={1,2}",
          "strict_u_not_integer=true",
          "BH=false")


def run_pair_allowed(eps: Int, k: Int, delta: Int) raises -> Bool:
    """Necessary and sufficient interior geometry for run/run y/y *types*.

    Caller must also supply real word indices with 1<=i<=n+d and
    1<=j<=n and delta=j-i. This function checks only the symbolic
    relative offset chamber, not a complete occurrence witness.
    """
    if k<0 or (eps!=-1 and eps!=1):
        raise Error("outside proven boundary parameter domain")
    if eps==-1:
        return delta==1 or delta==2
    if k<=3:
        return delta==2 or delta==3
    return delta==1 or delta==2
