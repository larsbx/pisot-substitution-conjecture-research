"""Complete minus W/Z/X/Q children and an exact six-step seed coincidence path.

Physical one-seed productivity only, not universal BH or a closed carrier.
Proof and all strict guards: docs/class-a-boundary-w-carrier-2026-10-27.md.
"""
from finite_exact.checked_int import checked_add, checked_sub
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge,
)
from psc.class_a_boundary_u_children import certify_u_children
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters
from psc.param_poly import QX, qx_const, qx_add, qx_sub
from psc.overlap_seed_patch import SeedOverlapTables

comptime W=0
comptime Z=1
comptime X=2
comptime Q=3


def local_source(kind: Int) raises -> BoundaryLabel:
    if kind==W:
        return BoundaryLabel(1,0,0,1,-1)
    if kind==Z:
        return BoundaryLabel(1,0,0,0,1)
    if kind==X:
        return BoundaryLabel(0,0,1,0,-1)
    if kind==Q:
        return BoundaryLabel(2,0,0,-1,1)
    raise Error("unknown W/Z/X/Q source")


def _inflated(kind: Int, n: QX, d: QX) raises -> List[QX]:
    if kind==W:
        return [qx_const(0),qx_const(0),qx_const(1)]
    if kind==Z:
        return [qx_const(1),qx_const(1),qx_sub(n,qx_const(1))]
    if kind==X:
        return [qx_const(1),qx_const(-1),qx_add(d,qx_const(1))]
    if kind==Q:
        return [qx_const(0),qx_const(0),qx_const(-1)]
    raise Error("unknown symbolic source")


def _offset(w: BoundaryLabel) -> List[QX]:
    return [qx_const(w.x),qx_const(w.c),qx_const(w.y)]


def selected_path_label(stage: Int) raises -> BoundaryLabel:
    if stage==0:
        return BoundaryLabel(0,1,0,0,0)
    if stage==1:
        return BoundaryLabel(2,2,-1,1,1)
    if stage==2:
        return BoundaryLabel(0,2,1,2,-3)
    if stage==3:
        return BoundaryLabel(2,0,0,-1,2)
    if stage==4:
        return local_source(W)
    if stage==5:
        return local_source(Q)
    if stage==6:
        return BoundaryLabel(2,2,0,0,0)
    raise Error("stage outside selected seven-state packet")


def selected_path_rank(w: BoundaryLabel) raises -> Int:
    for stage in range(7):
        if w==selected_path_label(stage):
            return 6-stage
    raise Error("no rank assigned outside selected path packet")


def typed_coincidence(w: BoundaryLabel) -> Bool:
    return w.top==w.bottom and w.x==0 and w.c==0 and w.y==0


def certify_w_children(corrupt: Bool=False) raises:
    certify_u_children()
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var A=qx_add(n,d)
    # Literal prefix transport is affine in each free run ordinal.
    # The legal basis 1,2 fixes both coefficients while n,d stay symbolic.
    for kind in range(4):
        var source=local_source(kind)
        var base=_inflated(kind,n,d)
        var top_run=A.copy() if kind==X else (qx_sub(n,qx_const(1)) if kind==Q else n.copy())
        for ri in [1,2]:
            for rj in [1,2]:
                var top=List[QX]()
                top.append(qx_const(0))
                top.append(qx_const(ri))
                top.append(qx_add(top_run,qx_const(1)))
                var bottom=List[QX]()
                bottom.append(qx_const(0))
                bottom.append(qx_const(rj))
                bottom.append(qx_add(A,qx_const(1)))
                for tk in range(3):
                    for bk in range(3):
                        var ct=source.top if tk==FIRST else (2 if tk==RUN else (1 if source.top==2 else 0))
                        if tk==FIRST and source.top==2:
                            ct=0
                        var cb=2 if bk==RUN else 0
                        var got=symbolic_child(-1,source.top,0,_offset(source),
                            tk,top[tk],bk,bottom[bk],ct,cb)
                        var tx=0 if tk==FIRST or source.top==1 else 1
                        var tc=1 if tk!=FIRST and source.top==1 else 0
                        var bx=0 if bk==FIRST else 1
                        var ty=qx_const(0) if tk==FIRST else qx_sub(top[tk],qx_const(1))
                        var by=qx_const(0) if bk==FIRST else qx_sub(bottom[bk],qx_const(1))
                        var want=List[QX]()
                        want.append(qx_add(base[0],qx_const(bx-tx)))
                        want.append(qx_sub(base[1],qx_const(tc)))
                        want.append(qx_add(base[2],qx_sub(by,ty)))
                        if corrupt and kind==W and tk==RUN and bk==RUN:
                            want[2]=qx_add(want[2],qx_const(1))
                        _equal3(got,want)
    # Each of the six selected occurrences is cone-word-legal, with full
    # typed Parikh transport checked as an identity in Q[t,k].
    for stage in range(6):
        var source=selected_path_label(stage)
        var target=selected_path_label(stage+1)
        var tk=RUN
        var bk=FIRST
        var i=qx_const(1)
        var j=qx_const(0)
        if stage==0:
            bk=RUN
            j=qx_const(2)
        elif stage==1:
            tk=FIRST
            bk=RUN
            i=qx_const(0)
            j=qx_add(p[3],qx_const(1))
        elif stage==2:
            i=qx_add(d,qx_const(2))
        elif stage==3:
            tk=LAST
            i=n.copy()
        elif stage==5:
            bk=RUN
            j=qx_const(2)
        var got=symbolic_child(-1,source.top,source.bottom,_offset(source),
            tk,i,bk,j,target.top,target.bottom)
        _equal3(got,_offset(target))
        if selected_path_rank(target)>=selected_path_rank(source):
            raise Error("selected path rank failed")
    if not typed_coincidence(selected_path_label(6)):
        raise Error("path terminal is not typed zero coincidence")
    print("CLASS_A_BOUNDARY_W_CHILDREN four_complete_sources=true",
          "minus_all_k_t=true", "outgoing_union_labels=17",
          "six_step_seed_physical_coincidence=true",
          "rank_scope=selected_seven_state_packet", "universal_BH=false")


def _dimensions(kind: Int, k: Int, t: Int) raises -> Tuple[Int,Int,Int,Int]:
    var p=_parameters(-1,k,t)
    _=local_source(kind)
    var n=p[0]
    var d=p[1]
    var A=checked_add(n,d)
    var top_run=A if kind==X else (n-1 if kind==Q else n)
    return (n,d,top_run,A)


def local_child_allowed(kind: Int, k: Int, t: Int, i: Int, j: Int) raises -> Bool:
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var d=p[1]
    var R=p[2]
    var A=p[3]
    if i<0 or i>checked_add(R,1) or j<0 or j>checked_add(A,1):
        raise Error("nonexistent local child occurrence")
    if kind==Z:
        return i==n+1 and j==0
    if kind==Q:
        if i==0:
            return j<=1
        if i==n:
            return j==n+1 or j==n+2
        return j==checked_add(i,1)
    if kind==W and i==0:
        return j==0
    if i==R+1:
        return j>=n-2 and j<=n+1
    if i>=1 and i<=R:
        if j==0:
            return i<=3 if kind==W else (i>=d and i<=d+3)
        if j<=A:
            var delta=checked_sub(i,j)
            return (delta==2 or delta==3) if kind==W else (delta==d+2 or delta==d+3)
    return False


def local_target_envelope() -> List[BoundaryLabel]:
    var out=List[BoundaryLabel]()
    for y in range(-1,3):
        out.append(BoundaryLabel(2,0,0,-1,y))
    for y in [-2,-1]:
        out.append(BoundaryLabel(2,2,1,-1,y))
    for y in range(-2,2):
        out.append(BoundaryLabel(0,2,1,-1,y))
    out.append(BoundaryLabel(1,0,0,0,1))
    out.append(BoundaryLabel(0,0,1,0,-1))
    out.append(BoundaryLabel(0,0,0,0,-1))
    out.append(BoundaryLabel(0,2,1,0,-1))
    out.append(BoundaryLabel(2,2,0,0,0))
    out.append(BoundaryLabel(1,2,0,0,0))
    out.append(BoundaryLabel(1,2,0,0,1))
    return out^


def in_local_target_envelope(w: BoundaryLabel) -> Bool:
    if w.top==2 and w.bottom==0 and w.x==0 and w.c==-1:
        return w.y>=-1 and w.y<=2
    if w.top==2 and w.bottom==2 and w.x==1 and w.c==-1:
        return w.y==-2 or w.y==-1
    if w.top==0 and w.bottom==2 and w.x==1 and w.c==-1:
        return w.y>=-2 and w.y<=1
    return (w==BoundaryLabel(1,0,0,0,1) or w==BoundaryLabel(0,0,1,0,-1)
            or w==BoundaryLabel(0,0,0,0,-1) or w==BoundaryLabel(0,2,1,0,-1)
            or w==BoundaryLabel(2,2,0,0,0) or w==BoundaryLabel(1,2,0,0,0)
            or w==BoundaryLabel(1,2,0,0,1))


def _append(mut out: List[BoundaryEdge], kind: Int, k: Int, t: Int, i: Int, j: Int) raises:
    var p=_dimensions(kind,k,t)
    if not local_child_allowed(kind,k,t,i,j):
        raise Error("synthesized local child failed strict guard")
    var target=member_transport(-1,k,p[0],p[1],local_source(kind),i,j)
    if not in_local_target_envelope(target):
        raise Error("local child escaped uniform target packet")
    out.append(BoundaryEdge(i,j,target))


def local_child_star(kind: Int, k: Int, t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var d=p[1]
    var R=p[2]
    var A=p[3]
    var out=List[BoundaryEdge]()
    if kind==Z:
        _append(out,kind,k,t,n+1,0)
    elif kind==Q:
        _append(out,kind,k,t,0,0)
        _append(out,kind,k,t,0,1)
        for i in range(1,n):
            _append(out,kind,k,t,i,i+1)
        _append(out,kind,k,t,n,n+1)
        _append(out,kind,k,t,n,n+2)
    else:
        if kind==W:
            _append(out,kind,k,t,0,0)
        var first=1 if kind==W else d
        var end=3 if kind==W else d+3
        for i in range(first,checked_add(end,1)):
            _append(out,kind,k,t,i,0)
        var delta0=2 if kind==W else d+2
        for delta in [delta0,checked_add(delta0,1)]:
            for j in range(1,checked_add(min(A,checked_sub(R,delta)),1)):
                _append(out,kind,k,t,checked_add(j,delta),j)
        for j in range(n-2,n+2):
            _append(out,kind,k,t,checked_add(R,1),j)
    return out^


def verify_local_packet(tables: SeedOverlapTables, kind: Int, k: Int, t: Int,
                        edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not local_child_allowed(kind,k,t,edge.i,edge.j):
        raise Error("local child is geometrically disjoint")
    verify_member_edge(tables,-1,k,p[0],p[1],local_source(kind),edge.i,edge.j,edge.target)


def minus_seed_path(k: Int, t: Int) raises -> List[BoundaryEdge]:
    var p=_parameters(-1,k,t)
    var out=List[BoundaryEdge]()
    out.append(BoundaryEdge(1,2,selected_path_label(1)))
    out.append(BoundaryEdge(0,checked_add(t,1),selected_path_label(2)))
    out.append(BoundaryEdge(checked_add(p[1],2),0,selected_path_label(3)))
    out.append(BoundaryEdge(p[0],0,selected_path_label(4)))
    out.append(BoundaryEdge(1,0,selected_path_label(5)))
    out.append(BoundaryEdge(1,2,selected_path_label(6)))
    return out^


def verify_minus_seed_path(tables: SeedOverlapTables, k: Int, t: Int,
                          packet: List[BoundaryEdge]) raises:
    var p=_parameters(-1,k,t)
    var want=minus_seed_path(k,t)
    if len(packet)!=6:
        raise Error("incomplete six-step path")
    var source=selected_path_label(0)
    for stage in range(6):
        var edge=packet[stage]
        if edge.i!=want[stage].i or edge.j!=want[stage].j or edge.target!=want[stage].target:
            raise Error("path occurrence or typed target differs from certified packet")
        verify_member_edge(tables,-1,k,p[0],p[1],source,edge.i,edge.j,edge.target)
        if selected_path_rank(edge.target)>=selected_path_rank(source):
            raise Error("selected path does not decrease")
        source=edge.target
    if not typed_coincidence(source):
        raise Error("path did not reach typed coincidence")
