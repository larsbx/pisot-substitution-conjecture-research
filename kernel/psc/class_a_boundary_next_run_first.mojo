"""Exact run/first children of the two seed-derived T_m boundary overlaps.

This solves the *run/first* typed child guard, NOT all children of T_m,
not forward-closure, a descending rank, a successful target-aware packet
or universal boundary hitting.

The proof is coefficientwise in the existing Q[t,k] polynomial algebra
and uses certified Perron sign/rational-remainder facts. Occurrence
indices are attached to literal parent image words and exact geometry
is independently replayed by verify_member_edge.
"""
from finite_exact.checked_int import checked_add, checked_sub, checked_mul
from psc.class_a_boundary_signs import (
    chamber_parameters, _same, _cone_positive,
)
from psc.class_a_boundary_next_run import (
    certify_next_run, _parameters,
)
from psc.class_a_boundary_next_first import _poly, _linear, _equal, _cubic
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, boundary_r, member_transport,
    verify_member_edge,
)
from psc.overlap_seed_patch import SeedOverlapTables
from psc.param_poly import (
    QX, qx_const, qx_add, qx_sub, qx_neg, qx_mul,
    tp_add, tp_sub, tp_mul,
)
from psc.class_a_boundary_run_pairs import _fix_k


def certify_run_first(corrupt: Bool=False) raises:
    """Infinite-chamber rounding proof with explicit root/sign premises.

    For T_m=(y,y,-1,1,m), B=beta*(m-u), a=Lx/Ly.
    Top run i vs bottom first 0: exact guard B-a < i < B+1.
    For m=r=floor(u), B<0, hence no i>=1 can pass i-1<B.

    Minus m=2: k+2+3/beta < i < k+5+alpha+2/beta.
    Plus k<=3 m=3: 3k+t+2+alpha-3/beta < i < B+1.
    Plus k>=4 m=2: k-6-3/beta < i < k-3+v,
                   v=alpha-2/beta in (0,1).
    All the other cases are empty. Real word indices impose 1<=i<=N.
    """
    certify_next_run()
    var one=qx_const(1)
    var zero=qx_const(0)
    var X=_linear(zero,one)
    var Xplus1=_linear(one,one)

    var neg=chamber_parameters(-1)
    var n=neg[0].copy()
    var d=neg[1].copy()
    var k=neg[2].copy()
    var f=_cubic(-1,n,d)
    # f(X)=(X+1)*(X^2-(n+3)X+2)+(k+1)X.
    # f(beta)=0, beta>1 => G(beta)<0, whence
    # alpha+2/beta<1 (alpha=beta-(n+2)).
    var G=_poly(qx_const(2),qx_neg(qx_add(n,qx_const(3))),
                one,zero)
    var rhs=tp_add(tp_mul(Xplus1,G),
                   _linear(zero,qx_add(k,one)))
    if corrupt:
        rhs=tp_add(rhs,_linear(one,zero))
    _equal(f,rhs)
    _cone_positive(qx_add(k,one))
    _cone_positive(qx_add(k,qx_const(3)))
    # Minus run/first upper word clip N=k+t+2:
    var t=neg[3].copy()
    _same(qx_sub(qx_add(n,qx_const(-1)),qx_add(k,qx_const(2))),t)

    var pos=chamber_parameters(1)
    n=pos[0].copy()
    d=pos[1].copy()
    k=pos[2].copy()
    t=pos[3].copy()
    f=_cubic(1,n,d)
    # Set alpha=beta-(n+4).
    # f(X)=X*(X^2-(n+4)X-3)-(k+t+7)X-2.
    # Thus alpha-3/beta>0 at the Perron root.
    var Glo=_poly(qx_const(-3),qx_neg(qx_add(n,qx_const(4))),
                  one,zero)
    _equal(f,tp_sub(tp_mul(X,Glo),_linear(qx_const(2),
                        qx_add(qx_add(k,t),qx_const(7)))))
    _cone_positive(qx_add(qx_add(k,t),qx_const(7)))
    # f(X)=(X+1)*(X^2-(n+5)X-3)+(k+2)X+1.
    # Thus alpha-3/beta<1 at the Perron root.
    var Ghi=_poly(qx_const(-3),qx_neg(qx_add(n,qx_const(5))),
                  one,zero)
    _equal(f,tp_add(tp_mul(Xplus1,Ghi),
                    _linear(one,qx_add(k,qx_const(2)))))
    _cone_positive(qx_add(k,qx_const(2)))
    # For k=0, beta>n+5 since f(n+5)=-(t+11)<0;
    # for k>=1, alpha>3/beta gives B-N>k-1+4/beta>=0.
    var endpoint=qx_add(n,qx_const(5))
    var f_at=qx_add(qx_add(qx_sub(qx_mul(qx_mul(endpoint,endpoint),endpoint),
                            qx_mul(qx_add(n,qx_const(4)),
                                   qx_mul(endpoint,endpoint))),
                            qx_mul(qx_sub(qx_add(n,qx_const(5)),d),endpoint)),
                      qx_const(-2))
    _same(f_at,qx_sub(qx_add(qx_mul(qx_const(2),qx_mul(k,k)),
                qx_add(qx_mul(k,t),qx_mul(qx_const(7),k))),
                qx_add(t,qx_const(11))))
    _cone_positive(qx_neg(_fix_k(f_at,0)))
    _same(qx_sub(qx_add(n,one),qx_add(qx_add(
                qx_mul(qx_const(3),k),t),qx_const(3))),
          qx_sub(qx_const(2),k)) # 3-k accepted indices for k<=3

    # For k>=4, v=alpha-2/beta in (0,1), already
    # certified in certify_next_run. B-a=k-6-3/beta,
    # B+1=k-3+v; N=2k+t+5 > k-3.
    _same(qx_sub(qx_add(n,one),qx_sub(k,qx_const(3))),
          qx_add(qx_add(k,t),qx_const(8)))
    print("CLASS_A_BOUNDARY_RUN_FIRST all_k_t=true",
          "minus_T2_i=k+3..min(k+5,k+t+2)",
          "plus_k_le_3_T3_i=3*k+t+3..2*k+t+5",
          "plus_k_ge_4_T2_i=max(1,k-6)..k-3",
          "other_Tm_run_first=false", "BH=false")


def run_first_allowed(eps: Int, k: Int, t: Int, m: Int, i: Int) raises -> Bool:
    """IFF strict interior run/first for an *existing top y ordinal*."""
    var p=_parameters(eps,k,t)
    var N=checked_add(p[0],eps)
    var r=boundary_r(eps,k)
    if m!=r and m!=r+1:
        raise Error("not an actual T_m source")
    if i<1 or i>N:
        raise Error("run/first occurrence index absent from sigma(y)")
    if m==r:
        return False
    if eps==-1:
        return i>=checked_add(k,3) and i<=checked_add(k,5)
    if k<=3:
        return i>=checked_add(checked_add(checked_mul(3,k),t),3)
    return i>=max(1,checked_sub(k,6)) and i<=checked_sub(k,3)


def run_first_star(eps: Int, k: Int, t: Int, m: Int) raises -> List[BoundaryEdge]:
    var p=_parameters(eps,k,t)
    var n=p[0]
    var d=p[1]
    var N=checked_add(n,eps)
    var r=boundary_r(eps,k)
    if m!=r and m!=r+1:
        raise Error("not a seed-derived T_m source")
    var out=List[BoundaryEdge]()
    if m==r:
        return out^
    var lo=1
    var hi=0
    if eps==-1:
        lo=checked_add(k,3)
        hi=min(N,checked_add(k,5))
    elif k<=3:
        lo=checked_add(checked_add(checked_mul(3,k),t),3)
        hi=N
    else:
        lo=max(1,checked_sub(k,6))
        hi=checked_sub(k,3)
    var parent=BoundaryLabel(2,2,-1,1,m)
    for i in range(lo,checked_add(hi,1)):
        if not run_first_allowed(eps,k,t,m,i):
            raise Error("run/first synthesis produced disjoint child")
        var child=member_transport(eps,k,n,d,parent,i,0)
        out.append(BoundaryEdge(i,0,child))
    return out^


def verify_run_first_packet(tables: SeedOverlapTables, eps: Int, k: Int,
                            t: Int, m: Int, edge: BoundaryEdge) raises:
    var p=_parameters(eps,k,t)
    if edge.j!=0 or not run_first_allowed(eps,k,t,m,edge.i):
        raise Error("unrealizable run/first occurrence")
    verify_member_edge(tables,eps,k,p[0],p[1],
        BoundaryLabel(2,2,-1,1,m),edge.i,edge.j,edge.target)
