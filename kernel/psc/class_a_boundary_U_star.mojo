"""Full actual child star for U=(x,y,1,2,-3), minus class-A boundary rays.

This is the first next-generation label in the full 50-target T_m image of
PR #349. It is not a full forward-closed carrier, rank, or BH certificate.

All accepted children keep the *actual pair of word ordinals* (i,j), target
letter types and all Parikh coordinates, then replay against the canonical
exact Perron-field overlap predicate. The infinite-family table follows
from 1<u=d/(beta-1)<2, b=Lc/Ly=1+1/beta and a=b+u, not a finite census.
"""
from finite_exact.checked_int import checked_add, checked_sub
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge,
)
from psc.class_a_boundary_next_run import _parameters, certify_next_run, first_run_allowed
from psc.class_a_boundary_occurrences import (
    symbolic_child, _equal3, FIRST, RUN,
)
from psc.class_a_boundary_signs import chamber_parameters, _same, _cone_positive
from psc.param_poly import QX, qx_const, qx_add, qx_sub
from psc.overlap_seed_patch import SeedOverlapTables


def U_label() -> BoundaryLabel:
    return BoundaryLabel(0,2,1,2,-3)


def _U_parameters(k: Int, t: Int) raises -> Tuple[Int,Int]:
    return _parameters(-1,k,t)


def certify_U_star() raises:
    """Coefficientwise ancestry plus all-chamber inequality primitives."""
    certify_next_run()
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var k=p[2].copy()
    var t=p[3].copy()
    var zero=qx_const(0)
    var one=qx_const(1)
    var source=List[QX]()
    for _ in range(3):
        source.append(zero.copy())
    # Actual run/run seed occurrence (i,j)=(1,2), giving T1.
    var T1=symbolic_child(-1,0,1,source,RUN,one,RUN,qx_const(2),2,2)
    var wantT=List[QX]()
    wantT.append(qx_const(-1))
    wantT.append(one.copy())
    wantT.append(one.copy())
    _equal3(T1,wantT)
    # T1 first/run bottom index t+1 gives U, for every k,t>=0.
    var U=symbolic_child(-1,2,2,T1,FIRST,zero,RUN,
                          qx_add(t,one),0,2)
    var wantU=List[QX]()
    wantU.append(one.copy())
    wantU.append(qx_const(2))
    wantU.append(qx_const(-3))
    _equal3(U,wantU)

    # Incidence update M*(1,2,-3)=(1,-1,d+3), independent of n.
    var old=List[QX]()
    old.append(one.copy())
    old.append(qx_const(2))
    old.append(qx_const(-3))
    var child=symbolic_child(-1,0,2,old,RUN,qx_add(d,qx_const(2)),
                             FIRST,zero,2,0)
    var expect=List[QX]()
    expect.append(zero.copy())
    expect.append(qx_const(-1))
    expect.append(qx_const(2))
    _equal3(child,expect)
    # The top last x and bottom last actual run y form a legitimate word
    # pair at indices n+d+1, n-1, with full target (x,y,1,-1,1).
    child=symbolic_child(-1,0,2,old,
                          2,qx_add(qx_add(n,d),one),
                          RUN,qx_add(n,qx_const(-1)),0,2)
    expect=List[QX]()
    expect.append(one.copy())
    expect.append(qx_const(-1))
    expect.append(one.copy())
    _equal3(child,expect)

    # Geometry prerequisites on the entire cone:
    # u in (1,2), beta>n+2>2, b=1+1/beta in (1,2).
    # First/last are disjoint; run/first starts at d+2.
    _cone_positive(qx_sub(n,qx_const(2))) # actual run n-1 exists
    _cone_positive(qx_sub(d,qx_const(2)))
    _same(qx_sub(qx_add(qx_add(n,d),one),qx_add(d,qx_const(2))),
          qx_sub(n,one))
    print("CLASS_A_BOUNDARY_U_STAR eps=-1 all_k_t=true",
          "one_step_ancestry=real_word",
          "typed_child_count=2*n-1",
          "universal_target_labels=12",
          "closed_carrier=false","BH=false")


def U_child_allowed(k: Int, t: Int, i: Int, j: Int) raises -> Bool:
    """IFF true strict interior child of U, for actual parent word indices."""
    var p=_U_parameters(k,t)
    var n=p[0]
    var d=p[1]
    var last_top=checked_add(checked_add(n,d),1)
    var last_bot=n
    if i<0 or i>last_top or j<0 or j>last_bot:
        raise Error("U child ordinal absent from literal image word")
    if i==0:
        return False
    if i<last_top:
        if j==0:
            return i>=checked_add(d,2) and i<=checked_add(d,5)
        if j==last_bot:
            return False
        var delta=checked_sub(i,j)
        return delta==checked_add(d,4) or delta==checked_add(d,5)
    if j==0:
        return n<=4
    if j==last_bot:
        return False
    return j>=max(1,checked_sub(n,4))


def in_U_target_envelope(w: BoundaryLabel) -> Bool:
    if w.top==2 and w.bottom==0:
        return w.x==0 and w.c==-1 and w.y>=-1 and w.y<=2
    if w.top==2 and w.bottom==2:
        return w.x==1 and w.c==-1 and w.y>=-2 and w.y<=-1
    if w.top==0 and w.bottom==0:
        return w.x==0 and w.c==-1 and w.y>=-1 and w.y<=0
    if w.top==0 and w.bottom==2:
        return w.x==1 and w.c==-1 and w.y>=-2 and w.y<=1
    return False


def U_target_envelope() -> List[BoundaryLabel]:
    var out=List[BoundaryLabel]()
    for y in range(-1,3):
        out.append(BoundaryLabel(2,0,0,-1,y))
    for y in range(-2,0):
        out.append(BoundaryLabel(2,2,1,-1,y))
    for y in range(-1,1):
        out.append(BoundaryLabel(0,0,0,-1,y))
    for y in range(-2,2):
        out.append(BoundaryLabel(0,2,1,-1,y))
    return out^


def _append(mut out: List[BoundaryEdge], k: Int,t:Int,n:Int,d:Int,
            i:Int,j:Int) raises:
    if not U_child_allowed(k,t,i,j):
        raise Error("synthetic U child not geometrically realizable")
    var target=member_transport(-1,k,n,d,U_label(),i,j)
    if not in_U_target_envelope(target):
        raise Error("U child escaped exact 12-label envelope")
    out.append(BoundaryEdge(i,j,target))


def U_child_star(k:Int,t:Int) raises -> List[BoundaryEdge]:
    """Enumerate all actual U children in O(n), retaining multiplicity."""
    var p=_U_parameters(k,t)
    var n=p[0]
    var d=p[1]
    var out=List[BoundaryEdge]()
    for i in range(checked_add(d,2),checked_add(min(checked_add(d,5),
                                                 checked_add(n,d)),1)):
        _append(out,k,t,n,d,i,0)
    for delta in [checked_add(d,4),checked_add(d,5)]:
        var upper=checked_sub(n,checked_sub(delta,d))
        for j in range(1,checked_add(upper,1)):
            _append(out,k,t,n,d,checked_add(j,delta),j)
    var last_top=checked_add(checked_add(n,d),1)
    if n<=4:
        _append(out,k,t,n,d,last_top,0)
    for j in range(max(1,checked_sub(n,4)),n):
        _append(out,k,t,n,d,last_top,j)
    if len(out)!=checked_sub(checked_add(n,n),1):
        raise Error("U occurrence star cardinality differs from 2n-1")
    return out^


def verify_U_packet(tables:SeedOverlapTables,k:Int,t:Int,
                    edge:BoundaryEdge) raises:
    var p=_U_parameters(k,t)
    if not U_child_allowed(k,t,edge.i,edge.j):
        raise Error("U packet is disjoint or not a true occurrence")
    verify_member_edge(tables,-1,k,p[0],p[1],U_label(),
                       edge.i,edge.j,edge.target)
