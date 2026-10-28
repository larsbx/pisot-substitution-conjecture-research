"""Complete B3/reversal stars, two-edge typed exits and a scoped registry.

Exact nine-kind guard derivation: docs/class-a-boundary-b3-carrier-2026-10-28.md.
Selected exits do not certify productivity of all direct children.
"""
from finite_exact.checked_int import checked_add, checked_mul
from std.collections import Dict
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_r3_children import certify_r3_children, r3_source, enlarged_candidate, star_interface
from psc.class_a_boundary_e_children import eh_source, _offset
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, _child, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _cone_positive, _cone_nonnegative
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def b3_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=2:
        raise Error("unknown B3 orientation")
    var w=BoundaryLabel(2,0,0,-1,0)
    return reverse_label(w) if kind==1 else w


def b3_star_interface(w: BoundaryLabel,include_b3: Bool=False) raises -> Int:
    # Preserve R3's ID meanings. Add existing H1/H2, then the new B3 interface.
    var old=star_interface(w,True)
    if old!=0:
        return old
    for flip in range(2):
        if w==eh_source(2+flip):
            return 15
        if w==eh_source(4+flip):
            return 16
        if include_b3 and w==b3_source(flip):
            return 17
    return 0


def b3_registered_exit(w: BoundaryLabel,include_b3: Bool=False) raises -> Bool:
    var route=b3_star_interface(w,include_b3)
    return route!=0 and route!=7 # T2 has a star, no uniform exit registered here


def _transition(n: QX,d: QX,kind: Int,tk: Int,i: QX,bk: Int,j: QX,target: BoundaryLabel) raises:
    var w=b3_source(kind)
    if _child(w.top,tk)!=target.top or _child(w.bottom,bk)!=target.bottom:
        raise Error("B3 symbolic actual types refused")
    var pt=_prefix(w.top,tk,i,-1,n,d)
    var pb=_prefix(w.bottom,bk,j,-1,n,d)
    var sign=1 if kind==0 else -1
    var base: List[QX]=[qx_const(-sign),qx_const(-sign),qx_neg(n) if kind==0 else n.copy()]
    var got=List[QX]()
    for z in range(3):
        got.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
    _equal3(got,_offset(target))


def certify_b3_children(corrupt: Bool=False) raises:
    certify_r3_children() # ancestry, inherited H/P exits and exact chamber signs
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var t=p[3].copy()
    var A=qx_add(n,d)
    var N=qx_sub(n,qx_const(1))
    _cone_positive(qx_sub(d,qx_const(4)))
    _cone_nonnegative(qx_sub(qx_sub(d,qx_const(3)),N)) # t
    _cone_nonnegative(qx_sub(A,qx_add(n,qx_const(4))))
    # The second RR strip loses precisely its top endpoint on t=0.
    _equal3([qx_sub(qx_sub(d,qx_const(4)),N),qx_const(0),qx_const(0)],
            [qx_sub(t,qx_const(1)),qx_const(0),qx_const(0)])
    var beta=_linear(qx_const(0),qx_const(1))
    var beta2=tp_mul(beta,beta)
    var f=_cubic(-1,n,d)
    var ba=tp_sub(tp_sub(beta2,tp_scale(beta,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    for kind in range(2):
        var w=b3_source(kind)
        var sign=1 if kind==0 else -1
        var base: List[QX]=[qx_const(-sign),qx_const(-sign),qx_neg(n) if kind==0 else n.copy()]
        var field=tp_scale(bb,qx_const(-sign))
        var image=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(beta,base[2]))
        if corrupt:
            image=tp_add(image,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(tp_mul(beta,field),f),tp_mod_monic(image,f))
        _equal(tp_mod_monic(image,f),tp_scale(tp_add(beta2,beta),qx_const(-sign)))
        var R=N.copy() if kind==0 else A.copy()
        var B=A.copy() if kind==0 else N.copy()
        for ri in [1,2]:
            for rj in [1,2]:
                var top: List[QX]=[qx_const(0),qx_const(ri),qx_add(R,qx_const(1))]
                var bottom: List[QX]=[qx_const(0),qx_const(rj),qx_add(B,qx_const(1))]
                for tk in range(3):
                    for bk in range(3):
                        var got=symbolic_child(-1,w.top,w.bottom,_offset(w),tk,top[tk],bk,bottom[bk],_child(w.top,tk),_child(w.bottom,bk))
                        var pt=_prefix(w.top,tk,top[tk],-1,n,d)
                        var pb=_prefix(w.bottom,bk,bottom[bk],-1,n,d)
                        var want=List[QX]()
                        for z in range(3):
                            want.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
                        _equal3(got,want)
        # Uniform actual R3 ancestry (d+1,0), including n=3.
        var parent=r3_source(kind)
        _equal3(symbolic_child(-1,parent.top,parent.bottom,_offset(parent),RUN if kind==0 else FIRST,qx_add(d,qx_const(1)) if kind==0 else qx_const(0),FIRST if kind==0 else RUN,qx_const(0) if kind==0 else qx_add(d,qx_const(1)),w.top,w.bottom),_offset(w))
        # B3 FIRST/RUN (0,n+2)->H1; reuse H1(1,2)->C.
        _transition(n,d,kind,FIRST if kind==0 else RUN,qx_const(0) if kind==0 else qx_add(n,qx_const(2)),RUN if kind==0 else FIRST,qx_add(n,qx_const(2)) if kind==0 else qx_const(0),eh_source(2+kind))
    # Every FR target and both RR labels have uniform representatives.
    for r in [1,2,3]:
        _transition(n,d,0,FIRST,qx_const(0),RUN,qx_add(n,qx_const(r+1)),BoundaryLabel(0,2,0,-1,r))
    for r in [3,4]:
        _transition(n,d,0,RUN,qx_const(1),RUN,qx_add(n,qx_const(r+1)),BoundaryLabel(2,2,-1,-1,r))
    # Conditional endpoints live on explicit shifted cones, not false uniform RUNs.
    var k=p[2].copy()
    for tt in [0,1]:
        var ns=qx_add(k,qx_const(3+tt))
        var ds=qx_add(k,qx_const(5+2*tt))
        var As=qx_add(ns,ds)
        _transition(ns,ds,0,LAST,ns,LAST,qx_add(As,qx_const(1)),BoundaryLabel(1,0,-1,-1,3+tt))
        if tt==0:
            _transition(ns,ds,0,RUN,qx_sub(ns,qx_const(1)),LAST,qx_add(As,qx_const(1)),BoundaryLabel(2,0,-1,-1,4))
    for dt in [1,2]:
        var ns=qx_add(n,qx_const(dt))
        var ds=qx_add(d,qx_const(2*dt))
        _transition(ns,ds,0,LAST,ns,RUN,qx_add(qx_add(ns,ns),qx_const(dt+2)),BoundaryLabel(1,2,-1,-1,dt+2))
    print("CLASS_A_BOUNDARY_B3 two_complete_oriented_stars=true", "count=2n+2_at_t0_else_2n+3", "union_labels=20", "typed_exit_two_edges=true", "candidate41_escape_via_H1=true", "all_direct_child_productivity_proved=false", "BH=false")


def _dimensions(kind: Int,k: Int,t: Int) raises -> Tuple[Int,Int,Int,Int]:
    _=b3_source(kind)
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,8)
    return(p[0],p[1],A,p[0]-1)


def b3_child_allowed(kind: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    var p=_dimensions(kind,k,t)
    var R=p[3] if kind==0 else p[2]
    var B=p[2] if kind==0 else p[3]
    if i<0 or i>R+1 or j<0 or j>B+1:
        raise Error("nonexistent B3 occurrence")
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    var n=p[0]
    var A=p[2]
    if a==0:
        return b>=n+2 and b<=n+4
    if a<=n-1:
        if b>=1 and b<=A:
            return b-a==n+3 or b-a==n+4
        return t==0 and a==n-1 and b==A+1
    return (b==A+1 and t<=1) or (b>=2*n+3 and b<=2*n+4 and b<=A)


def b3_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for r in [1,2,3]:
        base.append(BoundaryLabel(0,2,0,-1,r))
    for r in [3,4]:
        base.append(BoundaryLabel(2,2,-1,-1,r))
        base.append(BoundaryLabel(1,2,-1,-1,r))
        base.append(BoundaryLabel(1,0,-1,-1,r))
    base.append(BoundaryLabel(2,0,-1,-1,4))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def in_b3_image(w: BoundaryLabel) raises -> Bool:
    var z=w if w.c<0 else reverse_label(w)
    if z.c!=-1:
        return False
    if z.top==0 and z.bottom==2:
        return z.x==0 and z.y>=1 and z.y<=3
    if z.x!=-1:
        return False
    if (z.top==2 and z.bottom==2) or (z.top==1 and (z.bottom==0 or z.bottom==2)):
        return z.y==3 or z.y==4
    return z.top==2 and z.bottom==0 and z.y==4


def _append(mut out: List[BoundaryEdge],kind: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(kind,k,t)
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if not b3_child_allowed(kind,k,t,a,b):
        raise Error("synthesized B3 guard failed")
    var target=member_transport(-1,k,p[0],p[1],b3_source(kind),a,b)
    if not in_b3_image(target):
        raise Error("B3 target escaped exact image")
    out.append(BoundaryEdge(a,b,target))


def b3_child_star(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var A=p[2]
    var out=List[BoundaryEdge]()
    for j in range(n+2,n+5):
        _append(out,kind,k,t,0,j)
    for delta in [n+3,n+4]:
        for i in range(1,min(n-1,A-delta)+1):
            _append(out,kind,k,t,i,i+delta)
    if t==0:
        _append(out,kind,k,t,n-1,A+1)
    for j in range(2*n+3,min(2*n+4,A)+1):
        _append(out,kind,k,t,n,j)
    if t<=1:
        _append(out,kind,k,t,n,A+1)
    return out^


def verify_b3_packet(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not b3_child_allowed(kind,k,t,edge.i,edge.j) or not in_b3_image(edge.target):
        raise Error("B3 packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],b3_source(kind),edge.i,edge.j,edge.target)


def verify_b3_star(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edges: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    if len(edges)!=2*p[0]+(2 if t==0 else 3):
        raise Error("incomplete B3 indexed star")
    var stride=checked_add(p[2] if kind==0 else p[3],2)
    var seen=Dict[Int,Bool]()
    for edge in edges:
        verify_b3_packet(tables,kind,k,t,edge)
        var key=checked_add(checked_mul(edge.i,stride),edge.j)
        if key in seen:
            raise Error("duplicate B3 occurrence")
        seen[key]=True


def b3_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var flip=kind==1
    return [BoundaryEdge(p[0]+2 if flip else 0,0 if flip else p[0]+2,eh_source(2+kind)),
            BoundaryEdge(2 if flip else 1,1 if flip else 2,BoundaryLabel(2,2,0,0,0))]


def verify_b3_path(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    var want=b3_path(kind,k,t)
    if len(steps)!=len(want):
        raise Error("incomplete B3 path")
    var w=b3_source(kind)
    for z in range(len(steps)):
        var edge=steps[z]
        if edge.i!=want[z].i or edge.j!=want[z].j or edge.target!=want[z].target:
            raise Error("B3 intended typed intermediate or index mismatch")
        verify_member_edge(tables,-1,k,p[0],p[1],w,edge.i,edge.j,edge.target)
        w=edge.target
    if w!=BoundaryLabel(2,2,0,0,0):
        raise Error("B3 terminal is not typed coincidence")
