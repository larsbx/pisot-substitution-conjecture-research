"""All nine child-kind guards for both boundary T_m states; no global closure."""
from finite_exact.checked_int import checked_add, checked_sub
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, boundary_r, member_transport, verify_member_edge,
)
from psc.class_a_boundary_next_run import (
    _parameters, certify_next_run, first_run_allowed, first_last_allowed,
)
from psc.class_a_boundary_next_first import (
    certify_next_first, next_first_allowed, _cubic, _poly, _linear, _equal,
)
from psc.class_a_boundary_signs import chamber_parameters, _cone_nonnegative, _cone_positive
from psc.param_poly import (
    qx_const, qx_add, qx_sub, tp_mul, tp_sub, tp_mod_monic,
)
from psc.overlap_seed_patch import SeedOverlapTables


def certify_tm_children() raises:
    certify_next_first()
    certify_next_run()
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var k=p[2].copy()
    var t=p[3].copy()
    var X=_linear(qx_const(0),qx_const(1))
    var X2=tp_mul(X,X)
    var alpha=tp_sub(X,_linear(qx_add(n,qx_const(2)),qx_const(0)))
    # 0<alpha+2/beta<1: the upper margin reduces to
    # beta^2-(t+5)*beta+2>0 since beta>n+2=t+k+5.
    var margin=tp_sub(tp_sub(X2,tp_mul(X2,alpha)),
                      tp_mul(_linear(qx_const(2),qx_const(0)),X))
    _equal(tp_mod_monic(margin,_cubic(-1,n,d)),
           _poly(qx_const(2),qx_sub(qx_const(0),qx_add(t,qx_const(5))),
                 qx_const(1),qx_const(0)))
    _cone_nonnegative(k)
    p=chamber_parameters(1)
    # At u>2, alpha-1/beta>1-3/beta>1/2; beta>n+4>=8.
    _cone_positive(qx_add(p[0],qx_const(-2)))
    print("CLASS_A_BOUNDARY_TM_CHILDREN all_nine_kinds=true",
          "all_k_t=true", "proper_word_clips=true",
          "global_forward_closure=false", "BH=false")


def _source(eps: Int, k: Int, t: Int, m: Int) raises -> Tuple[Int,Int]:
    var p=_parameters(eps,k,t)
    var r=boundary_r(eps,k)
    if m!=r and m!=r+1:
        raise Error("not an actual T_m seed target")
    return p


def _run_first(eps: Int, k: Int, t: Int, m: Int, n: Int) raises -> Tuple[Int,Int]:
    var N=checked_add(n,eps)
    if eps==-1 and m==2:
        return (checked_add(k,3),min(N,checked_add(k,5)))
    if eps==1 and k<=3 and m==3:
        return (checked_add(checked_add(n,k),-1),N)
    if eps==1 and k>=4 and m==2:
        return (max(1,k-6),k-3)
    return (1,0)


def _run_last(eps: Int, k: Int, t: Int, m: Int, n: Int) raises -> Tuple[Int,Int]:
    var N=checked_add(n,eps)
    if eps==-1 and m==1:
        return (checked_add(k,2),min(N,checked_add(k,3)))
    if eps==1 and k<=3 and m==2:
        return (checked_add(checked_add(n,k),-2),min(N,checked_add(checked_add(n,k),-1)))
    if eps==1 and k>=4 and m==1:
        return (max(1,k-7),k-6)
    return (1,0)


def _last_run(eps: Int, k: Int, t: Int, m: Int, n: Int) raises -> Tuple[Int,Int]:
    var N=checked_add(n,eps)
    if eps==-1 and m==2:
        return (max(1,t-2),t-1)
    if eps==1 and k>=4 and m==2:
        var lo=checked_add(checked_add(k,t),9)
        return (lo,min(N,checked_add(lo,1)))
    return (1,0)


def _deltas(eps: Int, k: Int, t: Int, m: Int) raises -> Tuple[Int,Int]:
    if eps==-1:
        if m==1:
            return (t,checked_add(t,1))
        return (checked_sub(-5,k),checked_sub(-4,k))
    if m==1:
        var lo=checked_add(checked_add(k,t),12)
        return (lo,checked_add(lo,1))
    if m==2:
        return (3-k,4-k)
    return (1,0) # plus T3 has no run/run intersection


def tm_child_allowed(eps: Int, k: Int, t: Int, m: Int,
                     i: Int, j: Int) raises -> Bool:
    var p=_source(eps,k,t,m)
    var n=p[0]
    var N=checked_add(n,eps)
    var last=checked_add(N,1)
    if i<0 or i>last or j<0 or j>last:
        raise Error("nonexistent child ordinal")
    if i==0:
        if j==0:
            return next_first_allowed(eps,k,t,m)
        if j==last:
            return first_last_allowed(eps,k,t,m)
        return first_run_allowed(eps,k,t,m,j)
    if i==last:
        if j==0:
            return (eps==-1 and m==2 and t<=2) or (eps==1 and k<=3 and m==3)
        if j==last:
            return (eps==-1 and m==1 and t==0) or (eps==1 and m==2 and (k==3 or k==4))
        var b=_last_run(eps,k,t,m,n)
        return j>=b[0] and j<=b[1]
    if j==0:
        var b=_run_first(eps,k,t,m,n)
        return i>=b[0] and i<=b[1]
    if j==last:
        var b=_run_last(eps,k,t,m,n)
        return i>=b[0] and i<=b[1]
    var ds=_deltas(eps,k,t,m)
    if ds[0]>ds[1]:
        return False
    var delta=checked_sub(j,i)
    return delta==ds[0] or delta==ds[1]


def _append(mut out: List[BoundaryEdge], eps: Int, k: Int, t: Int,
            m: Int, i: Int, j: Int) raises:
    var p=_source(eps,k,t,m)
    if not tm_child_allowed(eps,k,t,m,i,j):
        raise Error("synthesized T_m child failed its exact guard")
    var target=member_transport(eps,k,p[0],p[1],BoundaryLabel(2,2,-1,1,m),i,j)
    if not in_tm_target_envelope(target):
        raise Error("actual T_m child escaped the universal 50-label image")
    out.append(BoundaryEdge(i,j,target))


def tm_child_star(eps: Int, k: Int, t: Int, m: Int) raises -> List[BoundaryEdge]:
    """All actual ordered children, O(N) not a Cartesian occurrence product."""
    var p=_source(eps,k,t,m)
    var n=p[0]
    var N=checked_add(n,eps)
    var last=checked_add(N,1)
    var out=List[BoundaryEdge]()
    for i in [0,last]:
        for j in [0,last]:
            if tm_child_allowed(eps,k,t,m,i,j):
                _append(out,eps,k,t,m,i,j)
    # First/run has at most four occurrences; use the already proved range.
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
    for j in range(lo,checked_add(hi,1)):
        _append(out,eps,k,t,m,0,j)
    var b=_run_first(eps,k,t,m,n)
    for i in range(b[0],checked_add(b[1],1)):
        _append(out,eps,k,t,m,i,0)
    b=_run_last(eps,k,t,m,n)
    for i in range(b[0],checked_add(b[1],1)):
        _append(out,eps,k,t,m,i,last)
    b=_last_run(eps,k,t,m,n)
    for j in range(b[0],checked_add(b[1],1)):
        _append(out,eps,k,t,m,last,j)
    var ds=_deltas(eps,k,t,m)
    if ds[0]<=ds[1]:
        for delta in [ds[0],ds[1]]:
            var begin=max(1,checked_sub(1,delta))
            var end=min(N,checked_sub(N,delta))
            for i in range(begin,checked_add(end,1)):
                _append(out,eps,k,t,m,i,checked_add(i,delta))
    return out^


def verify_tm_packet(tables: SeedOverlapTables, eps: Int, k: Int, t: Int,
                     m: Int, edge: BoundaryEdge) raises:
    var p=_source(eps,k,t,m)
    if not tm_child_allowed(eps,k,t,m,edge.i,edge.j):
        raise Error("T_m occurrence is geometrically disjoint")
    verify_member_edge(tables,eps,k,p[0],p[1],BoundaryLabel(2,2,-1,1,m),
                       edge.i,edge.j,edge.target)


def in_tm_target_envelope(w: BoundaryLabel) -> Bool:
    """Exact union over chambers, not the child set at any one member."""
    var a=w.top
    var b=w.bottom
    var x=w.x
    var c=w.c
    var y=w.y
    if a==0 and b==0:
        return (x==0 and c==2 and y>=-4 and y<=-3) or (x==1 and c==3 and y>=-9 and y<=-3)
    if a==0 and b==2:
        return (x==1 and c==2 and y>=-5 and y<=-2) or (x==2 and c==3 and y>=-9 and y<=-6)
    if a==0 and b==1:
        return x==1 and c==2 and y>=-5 and y<=-2
    if a==2 and b==0:
        return (x==0 and c==3 and y>=-5 and y<=-2) or (x==1 and c==4 and y>=-8 and y<=-6)
    if a==2 and (b==2 or b==1):
        return (x==0 and c==2 and y>=-3 and y<=-1) or (x==1 and c==3 and y>=-6 and y<=-5)
    if a==1 and b==0:
        return (x==0 and c==3 and y>=-5 and y<=-3) or (x==1 and c==4 and y>=-9 and y<=-6)
    if a==1 and b==2:
        return x==1 and c==3 and y>=-6 and y<=-5
    if a==1 and b==1:
        return (x==0 and c==2 and y==-3) or (x==1 and c==3 and y>=-6 and y<=-5)
    return False


def tm_target_envelope() raises -> List[BoundaryLabel]:
    var out=List[BoundaryLabel]()
    for a in range(3):
        for b in range(3):
            for x in range(3):
                for c in range(2,5):
                    for y in range(-9,0):
                        var label=BoundaryLabel(a,b,x,c,y)
                        if in_tm_target_envelope(label):
                            out.append(label)
    if len(out)!=50:
        raise Error("T_m universal image cardinality is not 50")
    return out^
