"""Complete minus-chamber U children; scoped outgoing carrier, not BH."""
from finite_exact.checked_int import checked_add, checked_sub
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge,
)
from psc.class_a_boundary_next_run import _parameters, certify_next_run
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _same, _cone_positive
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_mul
from psc.overlap_seed_patch import SeedOverlapTables


def reverse_label(w: BoundaryLabel) raises -> BoundaryLabel:
    return BoundaryLabel(w.bottom,w.top,checked_sub(0,w.x),
                         checked_sub(0,w.c),checked_sub(0,w.y))


def certify_u_children(corrupt: Bool=False) raises:
    # Includes the exact u-alpha=1-2/beta identity and minus 1<u<2.
    certify_next_run()
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var A=qx_add(n,d)
    var N=qx_sub(n,qx_const(1))
    var D=qx_add(d,qx_const(3))
    _cone_positive(qx_sub(n,qx_const(2)))
    # Full symbolic transport at first, arbitrary prototype run, last.
    # A free run index enters with coefficients -1 or +1; the indexed
    # prefix kernel checks those coefficients, not sampled parameters.
    var top=List[QX]()
    top.append(qx_const(0))
    top.append(qx_add(p[2],qx_const(1)))
    top.append(qx_add(A,qx_const(1)))
    var bottom=List[QX]()
    bottom.append(qx_const(0))
    bottom.append(qx_add(p[3],qx_const(1)))
    bottom.append(qx_add(N,qx_const(1)))
    var source=List[QX]()
    source.append(qx_const(1))
    source.append(qx_const(2))
    source.append(qx_const(-3))
    for tk in range(3):
        for bk in range(3):
            var ct=2 if tk==RUN else 0
            var cb=0 if bk==FIRST else (2 if bk==RUN else 1)
            var got=symbolic_child(-1,0,2,source,tk,top[tk],bk,bottom[bk],ct,cb)
            var tx=0 if tk==FIRST else 1
            var bx=0 if bk==FIRST else 1
            var ty=qx_const(0) if tk==FIRST else qx_sub(top[tk],qx_const(1))
            var by=qx_const(0) if bk==FIRST else qx_sub(bottom[bk],qx_const(1))
            var want=List[QX]()
            want.append(qx_const(1+bx-tx))
            want.append(qx_const(-1))
            want.append(qx_add(D,qx_sub(by,ty)))
            if corrupt and tk==RUN and bk==RUN:
                want[2]=qx_add(want[2],qx_const(1))
            _equal3(got,want)
    # Last/first shift = 2-n-1/beta. Its lower margin
    # is 3+u-n; 1<u<2 gives n<=4, i.e. k+t<=1.
    _same(qx_sub(qx_const(4),n),qx_sub(qx_const(1),qx_add(p[2],p[3])))
    # Constant target cancellation in the two run strips.
    for m in [1,2]:
        _same(qx_sub(D,qx_add(D,qx_const(m))),qx_const(-m))
    print("CLASS_A_BOUNDARY_U_CHILDREN all_nine_kinds=true",
          "minus_all_k_t=true", "target_image_labels=12",
          "strict_all_edge_rank_impossible_when_n_ge_5=true", "BH=false")


def u_child_allowed(k: Int, t: Int, i: Int, j: Int) raises -> Bool:
    var p=_parameters(-1,k,t)
    var n=p[0]
    var d=p[1]
    var A=checked_add(n,d)
    var N=checked_sub(n,1)
    if i<0 or i>checked_add(A,1) or j<0 or j>checked_add(N,1):
        raise Error("nonexistent U child occurrence")
    if i==0:
        return False
    if i==checked_add(A,1):
        if j==0:
            return checked_add(k,t)<=1
        return j<=N and j>=max(1,checked_sub(n,4))
    if j==0:
        return i>=checked_add(d,2) and i<=checked_add(d,5)
    if j<=N:
        var delta=checked_sub(i,j)
        return delta==checked_add(d,4) or delta==checked_add(d,5)
    return False


def in_u_target_envelope(w: BoundaryLabel) -> Bool:
    if w.top==2 and w.bottom==0:
        return w.x==0 and w.c==-1 and w.y>=-1 and w.y<=2
    if w.top==2 and w.bottom==2:
        return w.x==1 and w.c==-1 and (w.y==-1 or w.y==-2)
    if w.top==0 and w.bottom==0:
        return w.x==0 and w.c==-1 and (w.y==0 or w.y==-1)
    if w.top==0 and w.bottom==2:
        return w.x==1 and w.c==-1 and w.y>=-2 and w.y<=1
    return False


def u_target_envelope() -> List[BoundaryLabel]:
    var out=List[BoundaryLabel]()
    for y in range(-1,3):
        out.append(BoundaryLabel(2,0,0,-1,y))
    for y in [-2,-1]:
        out.append(BoundaryLabel(2,2,1,-1,y))
    for y in [-1,0]:
        out.append(BoundaryLabel(0,0,0,-1,y))
    for y in range(-2,2):
        out.append(BoundaryLabel(0,2,1,-1,y))
    return out^


def _append(mut out: List[BoundaryEdge], k: Int, t: Int, i: Int, j: Int) raises:
    var p=_parameters(-1,k,t)
    if not u_child_allowed(k,t,i,j):
        raise Error("synthesized U child failed its exact guard")
    var target=member_transport(-1,k,p[0],p[1],BoundaryLabel(0,2,1,2,-3),i,j)
    if not in_u_target_envelope(target):
        raise Error("U child escaped its 12-label image")
    out.append(BoundaryEdge(i,j,target))


def u_child_star(k: Int, t: Int) raises -> List[BoundaryEdge]:
    """O(n) output-sensitive occurrence synthesis, including all endpoint kinds."""
    var p=_parameters(-1,k,t)
    var n=p[0]
    var d=p[1]
    var A=checked_add(n,d)
    var out=List[BoundaryEdge]()
    for i in range(checked_add(d,2),checked_add(min(A,checked_add(d,5)),1)):
        _append(out,k,t,i,0)
    for m in [1,2]:
        var delta=checked_add(checked_add(d,3),m)
        for j in range(1,checked_add(min(n-1,checked_sub(A,delta)),1)):
            _append(out,k,t,checked_add(j,delta),j)
    if checked_add(k,t)<=1:
        _append(out,k,t,checked_add(A,1),0)
    for j in range(max(1,n-4),n):
        _append(out,k,t,checked_add(A,1),j)
    return out^


def verify_u_packet(tables: SeedOverlapTables, k: Int, t: Int,
                    edge: BoundaryEdge) raises:
    var p=_parameters(-1,k,t)
    if not u_child_allowed(k,t,edge.i,edge.j):
        raise Error("U occurrence is geometrically disjoint")
    verify_member_edge(tables,-1,k,p[0],p[1],BoundaryLabel(0,2,1,2,-3),
                       edge.i,edge.j,edge.target)
