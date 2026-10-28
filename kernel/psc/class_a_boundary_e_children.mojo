"""Six oriented E/H packets: complete children and <=2-step typed coincidence.

Minus boundary only. Neither global closure nor universal BH is asserted.
"""
from finite_exact.checked_int import checked_add, checked_sub, checked_mul
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge,
)
from psc.class_a_boundary_u_children import certify_u_children, reverse_label
from psc.class_a_boundary_w_children import typed_coincidence
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _same, _cone_nonnegative
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg
from psc.overlap_seed_patch import SeedOverlapTables

# Even kind is the displayed base packet; odd kind is its actual reversal.
# 0/1: E+ / E-, 2/3: H1 / R(H1), 4/5: H2 / R(H2).
def eh_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=6:
        raise Error("unknown E/H oriented packet")
    var base=BoundaryLabel(0,0,0,0,1) if kind//2==0 else BoundaryLabel(0,2,0,-1,kind//2)
    return reverse_label(base) if kind%2==1 else base


def _offset(w: BoundaryLabel) -> List[QX]:
    return [qx_const(w.x),qx_const(w.c),qx_const(w.y)]


def _symbolic_inflated(kind: Int, n: QX) -> List[QX]:
    var group=kind//2
    var out=List[QX]()
    out.append(qx_const(0 if group==1 else 1))
    out.append(qx_const(0 if group==1 else 1))
    out.append(qx_const(-1) if group==1 else qx_sub(n,qx_const(1 if group==0 else 2)))
    if kind%2==1:
        for z in range(3):
            out[z]=qx_neg(out[z])
    return out^


def certify_eh_children(corrupt: Bool=False) raises:
    # Supplies minus alpha+h<1 as an exact polynomial-remainder sign fact,
    # together with the root bracket, 1<u<2 and beta-a=n+h.
    certify_u_children()
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var A=qx_add(n,d)
    var N=qx_sub(n,qx_const(1))
    # H2's last two run ordinals are always actual, including the t=0 face.
    _same(qx_sub(A,qx_add(qx_add(n,n),qx_const(2))),p[3])
    _cone_nonnegative(p[3])
    for kind in range(6):
        var source=eh_source(kind)
        var base=_symbolic_inflated(kind,n)
        var R=A.copy() if source.top==0 else N.copy()
        var B=A.copy() if source.bottom==0 else N.copy()
        for ri in [1,2]:
            for rj in [1,2]:
                var top=List[QX]()
                top.append(qx_const(0))
                top.append(qx_const(ri))
                top.append(qx_add(R,qx_const(1)))
                var bottom=List[QX]()
                bottom.append(qx_const(0))
                bottom.append(qx_const(rj))
                bottom.append(qx_add(B,qx_const(1)))
                for tk in range(3):
                    for bk in range(3):
                        var ct=2 if tk==RUN else (1 if tk==LAST and source.top==2 else 0)
                        var cb=2 if bk==RUN else (1 if bk==LAST and source.bottom==2 else 0)
                        var got=symbolic_child(-1,source.top,source.bottom,_offset(source),
                            tk,top[tk],bk,bottom[bk],ct,cb)
                        var tx=0 if tk==FIRST else 1
                        var bx=0 if bk==FIRST else 1
                        var ty=qx_const(0) if tk==FIRST else qx_sub(top[tk],qx_const(1))
                        var by=qx_const(0) if bk==FIRST else qx_sub(bottom[bk],qx_const(1))
                        var want=List[QX]()
                        want.append(qx_add(base[0],qx_const(bx-tx)))
                        want.append(base[1].copy())
                        want.append(qx_add(base[2],qx_sub(by,ty)))
                        if corrupt and kind==0 and tk==RUN and bk==RUN:
                            want[2]=qx_add(want[2],qx_const(1))
                        _equal3(got,want)
        # Explicit path identities, including cone-certified occurrence bounds.
        var group=kind//2
        var i=qx_add(n,qx_const(1 if group==0 else 0))
        var j=qx_const(0)
        var target=eh_source(3)
        var tk=RUN
        var bk=FIRST
        if group==1:
            i=qx_const(1)
            j=qx_const(2)
            bk=RUN
            target=BoundaryLabel(2,2,0,0,0)
        if kind%2==1:
            var old_i=i.copy()
            i=j.copy()
            j=old_i.copy()
            var old_tk=tk
            tk=bk
            bk=old_tk
            target=reverse_label(target)
        var got=symbolic_child(-1,source.top,source.bottom,_offset(source),
                              tk,i,bk,j,target.top,target.bottom)
        _equal3(got,_offset(target))
    print("CLASS_A_BOUNDARY_EH six_complete_oriented_sources=true",
          "minus_all_k_t=true", "uniform_image_labels=29",
          "each_source_typed_coincidence_in_at_most_two_steps=true", "BH=false")


def _dimensions(kind: Int, k: Int, t: Int) raises -> Tuple[Int,Int,Int,Int]:
    var p=_parameters(-1,k,t)
    var source=eh_source(kind)
    var A=checked_add(p[0],p[1])
    var N=checked_sub(p[0],1)
    return (p[0],p[1],A if source.top==0 else N,A if source.bottom==0 else N)


def eh_child_allowed(kind: Int, k: Int, t: Int, i: Int, j: Int) raises -> Bool:
    var p=_dimensions(kind,k,t)
    if i<0 or i>checked_add(p[2],1) or j<0 or j>checked_add(p[3],1):
        raise Error("nonexistent E/H occurrence")
    var a=j if kind%2==1 else i
    var b=i if kind%2==1 else j
    var n=p[0]
    var d=p[1]
    var A=checked_add(n,d)
    var group=kind//2
    if group==0:
        if a>=1 and a<=A:
            if b==0:
                return a>=n+1 and a<=n+3
            if b>=1 and b<=A:
                var delta=checked_sub(a,b)
                return delta==n+2 or delta==n+3
        return a==A+1 and b>=d-2 and b<=d
    if group==1:
        if a==0:
            return b<=1
        if b>=1 and b<=n-1 and a>=1 and a<=A:
            return b==checked_add(a,1)
        return b==n and (a==n-1 or a==n)
    if a>=1 and a<=A:
        if b==0:
            return a>=n and a<=n+2
        if b>=1 and b<=n-1:
            var delta=checked_sub(a,b)
            return delta==n+1 or delta==n+2
        var twice_n=checked_mul(2,n)
        return b==n and (a==checked_add(twice_n,1) or a==checked_add(twice_n,2))
    return False


def _in_base_image(w: BoundaryLabel) -> Bool:
    if w.top==2 and w.bottom==0 and w.x==0 and w.c==1:
        return w.y>=-3 and w.y<=-1
    if w.top==2 and (w.bottom==2 or w.bottom==1) and w.x==1 and w.c==1:
        return w.y==-4 or w.y==-3
    if w.top==0 and w.bottom==2 and w.x==1 and w.c==1:
        return w.y>=-4 and w.y<=-2
    if w==BoundaryLabel(0,0,0,0,-1) or w==BoundaryLabel(0,2,1,0,-1):
        return True
    if w==BoundaryLabel(2,2,0,0,0):
        return True
    return w.top==2 and w.bottom==1 and w.x==0 and w.c==0 and (w.y==0 or w.y==-1)


def in_eh_image(w: BoundaryLabel) raises -> Bool:
    return _in_base_image(w) or _in_base_image(reverse_label(w))


def eh_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for y in range(-3,0):
        base.append(BoundaryLabel(2,0,0,1,y))
    for y in [-4,-3]:
        base.append(BoundaryLabel(2,2,1,1,y))
        base.append(BoundaryLabel(2,1,1,1,y))
    for y in range(-4,-1):
        base.append(BoundaryLabel(0,2,1,1,y))
    base.append(BoundaryLabel(0,0,0,0,-1))
    base.append(BoundaryLabel(0,2,1,0,-1))
    base.append(BoundaryLabel(2,2,0,0,0))
    base.append(BoundaryLabel(2,1,0,0,0))
    base.append(BoundaryLabel(2,1,0,0,-1))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        var rev=reverse_label(w)
        if rev!=w:
            out.append(rev)
    return out^


def _append(mut out: List[BoundaryEdge], kind: Int, k: Int, t: Int,
            i: Int, j: Int) raises:
    var p=_dimensions(kind,k,t)
    var a=j if kind%2==1 else i
    var b=i if kind%2==1 else j
    if not eh_child_allowed(kind,k,t,a,b):
        raise Error("synthesized E/H occurrence failed its strict guard")
    var target=member_transport(-1,k,p[0],p[1],eh_source(kind),a,b)
    if not in_eh_image(target):
        raise Error("E/H child escaped the uniform 29-label target packet")
    out.append(BoundaryEdge(a,b,target))


def eh_child_star(kind: Int, k: Int, t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var d=p[1]
    var A=checked_add(n,d)
    var group=kind//2
    var out=List[BoundaryEdge]()
    if group==0:
        for i in range(n+1,n+4):
            _append(out,kind,k,t,i,0)
        for delta in [n+2,n+3]:
            for j in range(1,checked_add(checked_sub(A,delta),1)):
                _append(out,kind,k,t,checked_add(j,delta),j)
        for j in range(d-2,d+1):
            _append(out,kind,k,t,A+1,j)
    elif group==1:
        _append(out,kind,k,t,0,0)
        _append(out,kind,k,t,0,1)
        for i in range(1,n-1):
            _append(out,kind,k,t,i,i+1)
        _append(out,kind,k,t,n-1,n)
        _append(out,kind,k,t,n,n)
    else:
        for i in range(n,n+3):
            _append(out,kind,k,t,i,0)
        for delta in [n+1,n+2]:
            for j in range(1,n):
                _append(out,kind,k,t,checked_add(j,delta),j)
        var twice_n=checked_mul(2,n)
        _append(out,kind,k,t,checked_add(twice_n,1),n)
        _append(out,kind,k,t,checked_add(twice_n,2),n)
    return out^


def verify_eh_packet(tables: SeedOverlapTables, kind: Int, k: Int, t: Int,
                     edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not eh_child_allowed(kind,k,t,edge.i,edge.j):
        raise Error("word-legal E/H child is geometrically disjoint")
    verify_member_edge(tables,-1,k,p[0],p[1],eh_source(kind),edge.i,edge.j,edge.target)


def short_eh_path(kind: Int, k: Int, t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var group=kind//2
    var out=List[BoundaryEdge]()
    if group!=1:
        var i=p[0]+1 if group==0 else p[0]
        out.append(BoundaryEdge(0 if kind%2==1 else i,i if kind%2==1 else 0,
                               eh_source(2 if kind%2==1 else 3)))
    var reversed=kind%2==0 if group!=1 else kind%2==1
    out.append(BoundaryEdge(2 if reversed else 1,1 if reversed else 2,
                           BoundaryLabel(2,2,0,0,0)))
    return out^


def eh_selected_rank(w: BoundaryLabel) raises -> Int:
    if w==BoundaryLabel(2,2,0,0,0):
        return 0
    for kind in range(6):
        if w==eh_source(kind):
            return 1 if kind//2==1 else 2
    raise Error("rank undefined outside selected E/H packet")


def verify_short_eh_path(tables: SeedOverlapTables, kind: Int, k: Int, t: Int,
                         packet: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    var want=short_eh_path(kind,k,t)
    if len(packet)!=len(want):
        raise Error("incomplete E/H short path")
    var current_kind=kind
    for step in range(len(packet)):
        var edge=packet[step]
        if edge.i!=want[step].i or edge.j!=want[step].j or edge.target!=want[step].target:
            raise Error("E/H path occurrence or target corrupted")
        var source=eh_source(current_kind)
        verify_eh_packet(tables,current_kind,k,t,edge)
        if eh_selected_rank(edge.target)>=eh_selected_rank(source):
            raise Error("selected short path failed strict descent")
        if step+1<len(packet):
            current_kind=2 if kind%2==1 else 3
    if not typed_coincidence(packet[len(packet)-1].target):
        raise Error("E/H path terminal is not typed coincidence")
