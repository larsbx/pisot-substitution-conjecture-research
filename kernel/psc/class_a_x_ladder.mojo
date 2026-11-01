"""Canonical member-level indexed ladder and exact native edge replay.

Uniform derivation: docs/class-a-x-productivity-2026-10-31.md.
This is a productive local family, not a forward-closed carrier.
"""
from finite_exact.checked_int import checked_add, checked_sub, checked_mul
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, verify_member_edge
from psc.overlap_seed_patch import SeedOverlapTables


def ladder_a(m: Int) raises -> BoundaryLabel:
    if m<1:
        raise Error("ladder index must be positive")
    return BoundaryLabel(0,2,checked_mul(2,m),checked_add(checked_mul(6,m),1),
                         checked_sub(1,checked_mul(12,m)))


def ladder_b(m: Int) raises -> BoundaryLabel:
    if m<2:
        raise Error("transfer index must be at least two")
    return BoundaryLabel(2,0,checked_sub(1,checked_mul(2,m)),
                         checked_sub(2,checked_mul(6,m)),checked_sub(checked_mul(12,m),7))


def reversed_label(w: BoundaryLabel) raises -> BoundaryLabel:
    return BoundaryLabel(w.bottom,w.top,checked_sub(0,w.x),
                         checked_sub(0,w.c),checked_sub(0,w.y))


def ladder_path(k: Int,t: Int,m: Int,flip: Bool=False,
                step_cap: Int=10000) raises -> List[BoundaryEdge]:
    if k<0 or t<0 or m<1:
        raise Error("outside nonnegative ladder parameters")
    if checked_add(checked_mul(2,k),t)<2:
        raise Error("base RUN is LAST or nonexistent on this face")
    if checked_mul(checked_add(k,1),m)>checked_add(checked_add(k,t),6):
        raise Error("ladder transfer outside proved index bounds")
    if checked_add(checked_mul(2,m),4)>step_cap:
        raise Error("ladder path cap: no verdict")
    var n=checked_add(checked_add(k,t),3)
    var d=checked_add(checked_add(k,checked_mul(2,t)),5)
    var A=checked_add(n,d)
    var edges=List[BoundaryEdge]()
    var r=m
    while r>=2:
        var twice=checked_mul(checked_mul(2,checked_add(k,1)),r)
        var i=checked_sub(checked_add(checked_add(d,k),8),twice)
        var j=checked_sub(checked_add(checked_add(d,checked_mul(2,k)),9),twice)
        edges.append(BoundaryEdge(i,0,ladder_b(r)))
        edges.append(BoundaryEdge(0,j,ladder_a(r-1)))
        r-=1
    edges.append(BoundaryEdge(checked_sub(checked_add(d,5),k),0,
                              BoundaryLabel(2,0,-1,-4,6)))
    edges.append(BoundaryEdge(0,checked_add(t,6),BoundaryLabel(0,2,1,2,-3)))
    edges.append(BoundaryEdge(checked_add(A,1),n-1,BoundaryLabel(0,2,1,-1,1)))
    edges.append(BoundaryEdge(checked_add(A,1),0,BoundaryLabel(0,0,1,0,-1)))
    edges.append(BoundaryEdge(checked_add(d,1),0,BoundaryLabel(2,0,0,-1,1)))
    edges.append(BoundaryEdge(1,2,BoundaryLabel(2,2,0,0,0)))
    if flip:
        var reversed_edges=List[BoundaryEdge]()
        for edge in edges:
            reversed_edges.append(BoundaryEdge(edge.j,edge.i,reversed_label(edge.target)))
        return reversed_edges^
    return edges^


def verify_ladder(tables: SeedOverlapTables,k: Int,t: Int,m: Int,
                  flip: Bool=False) raises -> Int:
    var edges=ladder_path(k,t,m,flip)
    var parent=ladder_a(m)
    if flip:
        parent=reversed_label(parent)
    var n=checked_add(checked_add(k,t),3)
    var d=checked_add(checked_add(k,checked_mul(2,t)),5)
    for edge in edges:
        verify_member_edge(tables,-1,k,n,d,parent,edge.i,edge.j,edge.target)
        parent=edge.target
    if parent!=BoundaryLabel(2,2,0,0,0):
        raise Error("ladder did not reach typed full-zero coincidence")
    return len(edges)
