"""Complete first/run children of both actual T_m seed targets, all k,t.

This resolves one more of the nine child-kind guards, not forward closure/BH.
The written ordered-field proof accompanies coefficientwise Mojo identities.
"""
from finite_exact.checked_int import checked_add, checked_sub, checked_mul
from psc.class_a_boundary_signs import (
    chamber_parameters, _same, _cone_positive, _cone_nonnegative,
)
from psc.class_a_boundary_run_pairs import certify_run_pair_chambers
from psc.class_a_boundary_next_first import _poly, _linear, _equal, _cubic
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, boundary_r, check_boundary_member,
    member_transport, verify_member_edge,
)
from psc.overlap_seed_patch import SeedOverlapTables
from psc.param_poly import (
    qx_const, qx_add, qx_sub, tp_add, tp_sub, tp_mul, tp_scale,
    tp_shift, tp_mod_monic,
)


def certify_next_run(corrupt: Bool=False) raises:
    certify_run_pair_chambers()
    var zero=qx_const(0)
    var one=qx_const(1)
    var X=_linear(zero,one)
    var X2=tp_mul(X,X)
    var Xminus1=_linear(qx_const(-1),one)
    for eps in [-1,1]:
        var p=chamber_parameters(eps)
        var n=p[0].copy()
        var d=p[1].copy()
        var k=p[2].copy()
        var t=p[3].copy()
        var A=qx_add(n,qx_const(3+eps))
        var alpha=tp_sub(X,_linear(A,zero))
        var f=_cubic(eps,n,d)
        # beta*(beta-1)*(u-alpha-1-2eps/beta) = -f(beta).
        var raw=tp_sub(tp_sub(tp_sub(tp_scale(X,d),
                         tp_mul(tp_mul(X,Xminus1),alpha)),
                         tp_mul(X,Xminus1)),
                         tp_scale(Xminus1,qx_const(2*eps)))
        var expected=tp_scale(f,qx_const(-1))
        if corrupt:
            expected=tp_add(expected,_linear(one,zero))
        _equal(raw,expected)
        if eps==-1:
            # beta^2*(1-alpha-1/beta) reduces to
            # beta*(beta-t-4)+2 > 0 since beta>n+2>t+4.
            var margin=tp_sub(tp_sub(X2,tp_mul(X2,alpha)),X)
            _equal(tp_mod_monic(margin,f),
                   _poly(qx_const(2),qx_sub(zero,qx_add(t,qx_const(4))),one,zero))
            _same(qx_sub(qx_add(n,qx_const(2)),qx_add(t,qx_const(4))),qx_add(k,one))
            _cone_positive(qx_add(k,one))
            # N=n-1 >= t+1, so only the lower word bound clips.
            _cone_nonnegative(qx_sub(qx_add(n,qx_const(-1)),qx_add(t,one)))
        else:
            # alpha>2/beta; the reduced positive expression is
            # beta^2*(alpha-2/beta)=(k+t+8)*beta+2.
            var low=tp_sub(tp_mul(X2,alpha),tp_scale(X,qx_const(2)))
            _equal(tp_mod_monic(low,f),
                   _linear(qx_const(2),qx_add(qx_add(k,t),qx_const(8))))
            _cone_positive(qx_add(qx_add(k,t),qx_const(8)))
            # beta^2*(alpha-1/beta)=(k+t+9)*beta+2 >0.
            _equal(tp_mod_monic(tp_sub(tp_mul(X2,alpha),X),f),
                   _linear(qx_const(2),qx_add(qx_add(k,t),qx_const(9))))
            # alpha<1+2/beta: multiply the margin by beta^3.
            var upper=tp_shift(tp_sub(tp_add(X2,tp_scale(X,qx_const(2))),
                                    tp_mul(X2,alpha)),1)
            _equal(tp_mod_monic(upper,f),
                   _poly(qx_const(2),qx_add(qx_add(k,t),qx_const(8)),k,zero))
            _cone_nonnegative(k)
            _cone_positive(qx_add(n,qx_const(-1))) # beta>n+4>5
            _cone_positive(qx_add(qx_add(n,k),qx_const(-3))) # N>=4-k
    print("CLASS_A_BOUNDARY_NEXT_RUN all_k_t=true",
          "minus_T1_j=t-1..t+1_word_clipped",
          "plus_k_le_3_T2_j=1..4-k",
          "plus_k_ge_4_T1_j=k+t+10..k+t+13_word_clipped",
          "other_Tm_first_run=false", "closed_carrier=false", "BH=false")


def _parameters(eps: Int, k: Int, t: Int) raises -> Tuple[Int,Int]:
    if (eps!=-1 and eps!=1) or k<0 or t<0:
        raise Error("invalid boundary chamber")
    var floor=checked_add(k,3) if eps==-1 else checked_mul(2,checked_add(k,2))
    var n=checked_add(floor,t)
    var d=checked_sub(checked_add(checked_mul(2,n),6*eps+5),k)
    check_boundary_member(eps,k,n,d)
    return (n,d)


def first_run_allowed(eps: Int, k: Int, t: Int, m: Int, j: Int) raises -> Bool:
    """IFF actual strict first/run overlap, for a real run ordinal."""
    var p=_parameters(eps,k,t)
    var N=checked_add(p[0],eps)
    var r=boundary_r(eps,k)
    if m!=r and m!=r+1:
        raise Error("m is not an actual seed run/run target")
    if j<1 or j>N:
        raise Error("nonexistent y-run occurrence")
    if eps==-1:
        return m==1 and j>=t-1 and j<=checked_add(t,1)
    if k<=3:
        return m==2 and j<=4-k
    var start=checked_add(checked_add(k,t),10)
    return m==1 and j>=start and j<=checked_add(start,3)


def first_run_star(eps: Int, k: Int, t: Int, m: Int) raises -> List[BoundaryEdge]:
    """At most four true ordered occurrences, including all word-bound clips."""
    var p=_parameters(eps,k,t)
    var n=p[0]
    var d=p[1]
    var N=checked_add(n,eps)
    var r=boundary_r(eps,k)
    if m!=r and m!=r+1:
        raise Error("m is not an actual seed run/run target")
    var out=List[BoundaryEdge]()
    var lo=1
    var hi=0
    if eps==-1 and m==1:
        lo=max(1,t-1)
        hi=checked_add(t,1)
    elif eps==1 and k<=3 and m==2:
        hi=4-k
    elif eps==1 and k>=4 and m==1:
        lo=checked_add(checked_add(k,t),10)
        hi=min(N,checked_add(lo,3))
    var parent=BoundaryLabel(2,2,-1,1,m)
    for j in range(lo,checked_add(hi,1)):
        if not first_run_allowed(eps,k,t,m,j):
            raise Error("first/run packet synthesis violated its guard")
        out.append(BoundaryEdge(0,j,member_transport(eps,k,n,d,parent,0,j)))
    return out^


def verify_first_run_packet(tables: SeedOverlapTables, eps: Int, k: Int, t: Int,
                           m: Int, edge: BoundaryEdge) raises:
    var p=_parameters(eps,k,t)
    if edge.i!=0 or not first_run_allowed(eps,k,t,m,edge.j):
        raise Error("not a realizable first/run occurrence")
    verify_member_edge(tables,eps,k,p[0],p[1],BoundaryLabel(2,2,-1,1,m),
                       edge.i,edge.j,edge.target)
