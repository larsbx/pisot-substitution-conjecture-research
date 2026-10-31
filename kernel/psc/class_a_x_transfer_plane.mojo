"""Guarded odd-plane transport and a unit-descent productive family.

The generic polynomial identity is NOT an assertion of word-valid indices
or strict overlap. The proved productive slice is z=1,s=0,p>=0 with
(k+1)p<=k+t+6. Its sole LAST correction is retained explicitly.
"""
from finite_exact.checked_int import checked_add, checked_sub, checked_mul
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, verify_member_edge
from psc.class_a_x_ladder import reversed_label
from psc.overlap_seed_patch import SeedOverlapTables


def plane_source(z: Int,s: Int,p: Int) raises -> BoundaryLabel:
    # 3*x+3*c+2*y=2*z+1 and c-3*x=2*s+1.
    var c=checked_add(checked_add(checked_mul(3,p),checked_mul(2,s)),1)
    var y=checked_sub(checked_sub(checked_sub(z,checked_mul(6,p)),checked_mul(3,s)),1)
    return BoundaryLabel(0,2,p,c,y)


def plane_middle(z: Int,s: Int,p: Int) raises -> BoundaryLabel:
    var x=checked_sub(checked_sub(checked_sub(z,p),s),1)
    var c=checked_sub(checked_sub(z,checked_mul(3,p)),s)
    var y=checked_sub(checked_add(checked_add(checked_mul(6,p),checked_mul(3,s)),1),checked_mul(4,z))
    return BoundaryLabel(2,0,x,c,y)


def plane_indices(k: Int,t: Int,z: Int,s: Int,p: Int) raises -> List[Int]:
    if k<0 or t<0:
        raise Error("outside minus parameter cone")
    var K=checked_add(k,1)
    var n=checked_add(checked_add(k,t),3)
    var d=checked_add(checked_add(k,checked_mul(2,t)),5)
    var i=checked_add(checked_sub(checked_mul(checked_sub(z,s),n),checked_mul(K,p)),
                      checked_add(checked_mul(3,z),1))
    var j=checked_add(checked_add(checked_sub(checked_mul(checked_add(K,3),z),checked_mul(K,p)),
                                  checked_mul(checked_sub(n,K),s)),checked_add(d,1))
    return [i,j]


def verify_plane_transfer(tables: SeedOverlapTables,k: Int,t: Int,
                          z: Int,s: Int,p: Int) raises:
    # Conditional generic rule: actual word/geometry verification may REFUSE.
    var n=checked_add(checked_add(k,t),3)
    var d=checked_add(checked_add(k,checked_mul(2,t)),5)
    var ij=plane_indices(k,t,z,s,p)
    var mid=plane_middle(z,s,p)
    verify_member_edge(tables,-1,k,n,d,plane_source(z,s,p),ij[0],0,mid)
    verify_member_edge(tables,-1,k,n,d,mid,0,ij[1],plane_source(z,s,checked_sub(p,z)))


def unit_descent_path(k: Int,t: Int,p: Int,flip: Bool=False,
                      step_cap: Int=10000) raises -> List[BoundaryEdge]:
    if k<0 or t<0 or p<0:
        raise Error("outside nonnegative unit-descent domain")
    var n=checked_add(checked_add(k,t),3)
    if checked_mul(checked_add(k,1),p)>checked_add(n,3):
        raise Error("unit descent index outside proved bound")
    if checked_add(checked_mul(2,p),2)>step_cap:
        raise Error("unit descent path cap: no verdict")
    var edges=List[BoundaryEdge]()
    var r=p
    while r>=1:
        var ij=plane_indices(k,t,1,0,r)
        edges.append(BoundaryEdge(ij[0],0,plane_middle(1,0,r)))
        var target=plane_source(1,0,r-1)
        if k==0 and t==0 and r==1:
            # j=A+1 is LAST x, not RUN y. The full offset is unchanged.
            target=BoundaryLabel(0,0,0,1,0)
        edges.append(BoundaryEdge(0,ij[1],target))
        r-=1
    edges.append(BoundaryEdge(checked_add(n,2),0,BoundaryLabel(2,0,0,1,-1)))
    edges.append(BoundaryEdge(2,1,BoundaryLabel(2,2,0,0,0)))
    if flip:
        var reversed_edges=List[BoundaryEdge]()
        for edge in edges:
            reversed_edges.append(BoundaryEdge(edge.j,edge.i,reversed_label(edge.target)))
        return reversed_edges^
    return edges^


def verify_unit_descent(tables: SeedOverlapTables,k: Int,t: Int,p: Int,
                        flip: Bool=False) raises -> Int:
    var edges=unit_descent_path(k,t,p,flip)
    var parent=plane_source(1,0,p)
    if flip:
        parent=reversed_label(parent)
    var n=checked_add(checked_add(k,t),3)
    var d=checked_add(checked_add(k,checked_mul(2,t)),5)
    for edge in edges:
        verify_member_edge(tables,-1,k,n,d,parent,edge.i,edge.j,edge.target)
        parent=edge.target
    if parent!=BoundaryLabel(2,2,0,0,0):
        raise Error("unit descent did not reach typed full-zero coincidence")
    return len(edges)


def verify_exception_base(tables: SeedOverlapTables,k: Int,t: Int,
                          flip: Bool=False) raises:
    if k<0 or t<0:
        raise Error("outside minus exception-base parameters")
    var n=checked_add(checked_add(k,t),3)
    var d=checked_add(checked_add(k,checked_mul(2,t)),5)
    var root=BoundaryLabel(0,0,0,1,0)
    var mid=BoundaryLabel(2,0,0,1,-1)
    var coin=BoundaryLabel(2,2,0,0,0)
    if flip:
        verify_member_edge(tables,-1,k,n,d,reversed_label(root),0,checked_add(n,2),reversed_label(mid))
        verify_member_edge(tables,-1,k,n,d,reversed_label(mid),1,2,coin)
    else:
        verify_member_edge(tables,-1,k,n,d,root,checked_add(n,2),0,mid)
        verify_member_edge(tables,-1,k,n,d,mid,2,1,coin)
