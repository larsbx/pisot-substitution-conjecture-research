"""Parameter-dependent escape for the complete signed unit-strip candidate.

K*abs(p)<=n-1. A bounded negative pump reaches one of four typed exits.
This is local selected productivity, not all-child closure or X coverage.
"""
from finite_exact.checked_int import checked_add, checked_sub, checked_mul, checked_abs
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, verify_member_edge
from psc.class_a_x_ladder import reversed_label
from psc.class_a_x_transfer_plane import plane_source, plane_middle, unit_descent_path
from psc.overlap_seed_patch import SeedOverlapTables


def strip_source(p: Int) raises -> BoundaryLabel:
    return plane_source(1,0,p)


def _z(r: Int,s: Int,u: Int) raises -> BoundaryLabel:
    return BoundaryLabel(0,2,r,checked_add(checked_mul(3,r),s),
        checked_sub(checked_sub(u,s),checked_mul(6,r)))


def _cap(r: Int,u: Int) raises -> BoundaryLabel:
    return BoundaryLabel(0,0,checked_sub(0,r),checked_sub(1,checked_mul(3,r)),
        checked_sub(checked_add(checked_mul(6,r),u),1))


def _push(mut edges: List[BoundaryEdge],i: Int,j: Int,w: BoundaryLabel,cap: Int) raises:
    if len(edges)>=cap:
        raise Error("signed strip path cap: no verdict")
    edges.append(BoundaryEdge(i,j,w))


def _tail(mut edges: List[BoundaryEdge],k: Int,t: Int,r: Int,
          flip: Bool,skip: Int,cap: Int) raises:
    var tail=unit_descent_path(k,t,r,flip,cap)
    for a in range(skip,len(tail)):
        _push(edges,tail[a].i,tail[a].j,tail[a].target,cap)


def signed_strip_path(k: Int,t: Int,p: Int,flip: Bool=False,
                      step_cap: Int=10000) raises -> List[BoundaryEdge]:
    if k<0 or t<0 or step_cap<1:
        raise Error("invalid signed strip parameters or cap")
    var K=checked_add(k,1)
    var n=checked_add(checked_add(k,t),3)
    var d=checked_add(checked_add(k,checked_mul(2,t)),5)
    var A=checked_add(n,d)
    var radius=checked_abs(p)
    if checked_mul(K,radius)>n-1:
        raise Error("outside proved signed unit-strip domain")
    if p>=0:
        return unit_descent_path(k,t,p,flip,step_cap)
    var bound=(n-1)//K
    var r=radius
    var edges=List[BoundaryEdge]()
    # Each pump raises r by one inside r<=bound, so bound-r decreases.
    while checked_mul(K,r)<=t-2:
        var a=checked_mul(K,r)
        _push(edges,checked_add(checked_add(n,4),a),0,plane_middle(1,0,checked_sub(0,r)),step_cap)
        var next_r=checked_add(r,1)
        if next_r>bound:
            raise Error("negative pump escaped its proved integer budget")
        _push(edges,0,checked_add(checked_add(checked_mul(2,n),4),a),strip_source(checked_sub(0,next_r)),step_cap)
        r=next_r
    var a=checked_mul(K,r)
    var R=checked_add(r,1)
    if a==t-1:
        _push(edges,checked_add(checked_add(n,4),a),0,plane_middle(1,0,checked_sub(0,r)),step_cap)
        _push(edges,0,checked_add(A,1),_cap(R,1),step_cap)
        _push(edges,checked_add(A,1),checked_add(t,4),_z(checked_add(R,1),-2,2),step_cap)
        _push(edges,checked_add(t,8),0,reversed_label(strip_source(R)),step_cap)
        _tail(edges,k,t,R,True,0,step_cap)
    elif a==t:
        _push(edges,checked_add(checked_add(n,4),a),0,plane_middle(1,0,checked_sub(0,r)),step_cap)
        _push(edges,0,checked_add(A,1),_cap(R,0),step_cap)
        _push(edges,checked_add(A,1),checked_add(d,3),_z(R,0,1),step_cap)
        _push(edges,5,0,plane_middle(1,0,R),step_cap)
        _tail(edges,k,t,R,False,1,step_cap)
    elif a==checked_add(t,1):
        _push(edges,checked_add(A,1),n-1,_z(R,-2,1),step_cap)
        _push(edges,2,0,plane_middle(1,0,R),step_cap)
        _tail(edges,k,t,R,False,1,step_cap)
    else:
        if a<checked_add(t,2):
            raise Error("integer wall partition failed")
        _push(edges,checked_add(A,1),checked_sub(checked_sub(d,a),1),_z(R,-2,2),step_cap)
        _push(edges,checked_sub(checked_add(checked_mul(2,n),3),checked_mul(K,R)),0,
              reversed_label(strip_source(r)),step_cap)
        _tail(edges,k,t,r,True,0,step_cap)
    if len(edges)>checked_add(checked_mul(4,bound),6):
        raise Error("signed strip selected path exceeded proved budget")
    if flip:
        var reversed_edges=List[BoundaryEdge]()
        for edge in edges:
            reversed_edges.append(BoundaryEdge(edge.j,edge.i,reversed_label(edge.target)))
        return reversed_edges^
    return edges^


def verify_signed_strip(tables: SeedOverlapTables,k: Int,t: Int,p: Int,
                        flip: Bool=False) raises -> Int:
    var edges=signed_strip_path(k,t,p,flip)
    var parent=strip_source(p)
    if flip:
        parent=reversed_label(parent)
    var n=checked_add(checked_add(k,t),3)
    var d=checked_add(checked_add(k,checked_mul(2,t)),5)
    for edge in edges:
        verify_member_edge(tables,-1,k,n,d,parent,edge.i,edge.j,edge.target)
        parent=edge.target
    if parent!=BoundaryLabel(2,2,0,0,0):
        raise Error("signed strip path did not end at typed full-zero coincidence")
    return len(edges)
