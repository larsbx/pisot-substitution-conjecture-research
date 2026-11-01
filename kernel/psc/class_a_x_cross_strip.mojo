"""Typed RUN shear into the proved class-A signed unit-strip paths.

Z(p,s,1)=(x,y,p,3p+s,1-s-6p). Productive sectors:
p>=0, Kp<=n-1, -3<=s<=3; or p<0, K|p|<=t, -3<=s<=1.
No forward closure or coverage of all X descendants is asserted.
"""
from finite_exact.checked_int import checked_add, checked_sub, checked_mul, checked_abs
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, verify_member_edge
from psc.class_a_x_signed_strip import signed_strip_path
from psc.class_a_x_ladder import reversed_label
from psc.overlap_seed_patch import SeedOverlapTables


def cross_strip_source(p: Int,s: Int) raises -> BoundaryLabel:
    return BoundaryLabel(0,2,p,checked_add(checked_mul(3,p),s),
        checked_sub(checked_sub(1,s),checked_mul(6,p)))


def cross_strip_path(k: Int,t: Int,p: Int,s: Int,flip: Bool=False,
                     step_cap: Int=10000) raises -> List[BoundaryEdge]:
    if k<0 or t<0 or s< -3 or s>3:
        raise Error("outside cross-strip productive sectors")
    var K=checked_add(k,1)
    var n=checked_add(checked_add(k,t),3)
    var size=checked_mul(K,checked_abs(p))
    if (p>=0 and size>n-1) or (p<0 and (size>t or s>1)):
        raise Error("outside cross-strip radial or negative-sector guards")
    var path=signed_strip_path(k,t,p,False,step_cap)
    # M(0,m,-m)=(0,0,m), exactly cancelled by moving the top RUN
    # occurrence m places. Only the first edge changes; its target is fixed.
    path[0].i=checked_add(path[0].i,checked_sub(s,1))
    var A=checked_add(n,checked_add(checked_add(k,checked_mul(2,t)),5))
    if path[0].i<1 or path[0].i>A:
        raise Error("proved cross-strip entrance left the actual RUN")
    if flip:
        var reversed_edges=List[BoundaryEdge]()
        for edge in path:
            reversed_edges.append(BoundaryEdge(edge.j,edge.i,reversed_label(edge.target)))
        return reversed_edges^
    return path^


def verify_cross_strip(tables: SeedOverlapTables,k: Int,t: Int,p: Int,s: Int,
                       flip: Bool=False) raises -> Int:
    var packet=cross_strip_path(k,t,p,s,flip)
    var parent=cross_strip_source(p,s)
    if flip:
        parent=reversed_label(parent)
    var n=checked_add(checked_add(k,t),3)
    var d=checked_add(checked_add(k,checked_mul(2,t)),5)
    for edge in packet:
        verify_member_edge(tables,-1,k,n,d,parent,edge.i,edge.j,edge.target)
        parent=edge.target
    if parent!=BoundaryLabel(2,2,0,0,0):
        raise Error("cross-strip selected path did not reach typed coincidence")
    return len(packet)
