"""Complete R5/reversal indexed stars; inherited three-edge selected exits.

Derivation: docs/class-a-boundary-r5-carrier-2026-10-28.md. No global closure.
"""
from finite_exact.checked_int import checked_add, checked_mul
from std.collections import Dict
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_y4_children import certify_y4_children, y4_source, y4_path, verify_y4_path, y4_star_interface, y4_exit_interface
from psc.class_a_boundary_p_children import p_source
from psc.class_a_boundary_h3_children import chain_source
from psc.class_a_boundary_r4_children import _image, _transition
from psc.class_a_boundary_e_children import _offset
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, _child, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _cone_nonnegative
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def r5_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=2:
        raise Error("unknown R5 orientation")
    return y4_source(2+kind)


def r5_star_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=y4_star_interface(w,True)
    if old!=0:
        return old
    for flip in range(2):
        # Existing complete stars newly bound for this image, not reclassified.
        if w==p_source(4+flip):
            return 34 # B2
        if w==p_source(6+flip):
            return 35 # B2h
        if w==chain_source(4+flip):
            return 36 # K
        if include_new and w==r5_source(flip):
            return 29 # R5 already had an exit
    return 0


def r5_exit_interface(w: BoundaryLabel) raises -> Int:
    var old=y4_exit_interface(w,True)
    if old!=0:
        return old
    for flip in range(2):
        if w==p_source(4+flip):
            return 34
        if w==p_source(6+flip):
            return 35
        if w==chain_source(4+flip):
            return 36
    return 0


def certify_r5_children(corrupt: Bool=False) raises:
    certify_y4_children() # inherited source exit, K/B2/B2h and exact chamber bounds
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var t=p[3].copy()
    var A=qx_add(n,d)
    var N=qx_sub(n,qx_const(1))
    _cone_nonnegative(qx_sub(A,qx_add(N,qx_add(t,qx_const(1)))))
    _cone_nonnegative(qx_sub(A,qx_add(n,qx_add(t,qx_const(1)))))
    var beta=_linear(qx_const(0),qx_const(1))
    var beta2=tp_mul(beta,beta)
    var f=_cubic(-1,n,d)
    var ba=tp_sub(tp_sub(beta2,tp_scale(beta,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    for kind in range(2):
        var w=r5_source(kind)
        var sign=1 if kind==0 else -1
        var base=_image(w,n,d)
        _equal3(base,[qx_const(0),qx_const(-2*sign),qx_add(t,qx_const(3)) if kind==0 else qx_neg(qx_add(t,qx_const(3)))])
        var field=tp_add(tp_add(tp_scale(ba,qx_const(w.x)),tp_scale(bb,qx_const(w.c))),tp_scale(beta,qx_const(w.y)))
        var image=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(beta,base[2]))
        if corrupt:
            image=tp_add(image,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(tp_mul(beta,field),f),tp_mod_monic(image,f))
        _equal(tp_mod_monic(image,f),tp_scale(_linear(qx_const(-2),qx_add(t,qx_const(1))),qx_const(sign)))
        var R=A.copy() if kind==0 else N.copy()
        var B=N.copy() if kind==0 else A.copy()
        for ri in [1,2]:
            for rj in [1,2]:
                var top=[qx_const(0),qx_const(ri),qx_add(R,qx_const(1))]
                var bottom=[qx_const(0),qx_const(rj),qx_add(B,qx_const(1))]
                for tk in range(3):
                    for bk in range(3):
                        var got=symbolic_child(-1,w.top,w.bottom,_offset(w),tk,top[tk],bk,bottom[bk],_child(w.top,tk),_child(w.bottom,bk))
                        var pt=_prefix(w.top,tk,top[tk],-1,n,d)
                        var pb=_prefix(w.bottom,bk,bottom[bk],-1,n,d)
                        var want=List[QX]()
                        for z in range(3):
                            want.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
                        _equal3(got,want)
        _transition(n,d,y4_source(kind),LAST if kind==0 else RUN,qx_add(A,qx_const(1)) if kind==0 else N.copy(),RUN if kind==0 else LAST,N.copy() if kind==0 else qx_add(A,qx_const(1)),w)
        _transition(n,d,w,RUN,qx_add(t,qx_const(1)) if kind==0 else qx_const(1),RUN,qx_const(1) if kind==0 else qx_add(t,qx_const(1)),p_source(7-kind))
        for delta in [0,1]:
            _transition(n,d,w,RUN,qx_add(t,qx_const(1+delta)) if kind==0 else qx_const(1),RUN,qx_const(1) if kind==0 else qx_add(t,qx_const(1+delta)),p_source(7-kind-2*delta))
        for delta in [0,1]:
            var i=qx_add(n,qx_add(t,qx_const(delta)))
            var target=BoundaryLabel(2,1,0,-2,3-delta)
            _transition(n,d,w,RUN if kind==0 else LAST,i.copy() if kind==0 else n.copy(),LAST if kind==0 else RUN,n.copy() if kind==0 else i.copy(),reverse_label(target) if kind==1 else target)
    # Attainment cones: RF r=3/4/5 first appears at t=0/1/2.
    for flip in range(2):
        for step in range(3):
            var ns=qx_add(n,qx_const(step))
            var ds=qx_add(d,qx_const(2*step))
            var target=BoundaryLabel(2,0,-1,-2,3+step)
            _transition(ns,ds,r5_source(flip),RUN if flip==0 else FIRST,qx_add(t,qx_const(1)) if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_add(t,qx_const(1)),reverse_label(target) if flip==1 else target)
        for tt in [0,1]:
            var ns=qx_add(p[2],qx_const(3+tt))
            var ds=qx_add(p[2],qx_const(5+2*tt))
            var target=BoundaryLabel(0,0,0,-2,3+tt)
            _transition(ns,ds,r5_source(flip),FIRST,qx_const(0),FIRST,qx_const(0),reverse_label(target) if flip==1 else target)
    print("CLASS_A_BOUNDARY_R5 two_complete_oriented_stars=true", "count=2n+2_if_t0_else_2n+3", "union_labels=18", "source_exit_three=true", "all_child_productivity_proved=false", "closed_carrier=false", "global_BH=false")


def _dimensions(kind: Int,k: Int,t: Int) raises -> Tuple[Int,Int,Int,Int]:
    _=r5_source(kind)
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,12)
    return(p[0],p[1],A,p[0]-1)


def r5_child_allowed(kind: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    var p=_dimensions(kind,k,t)
    var R=p[2] if kind==0 else p[3]
    var B=p[3] if kind==0 else p[2]
    if i<0 or i>R+1 or j<0 or j>B+1:
        raise Error("nonexistent R5 occurrence")
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if a==0:
        return b==0 and t<=1
    if a<=p[2]:
        if b==0:
            return a>=max(1,t-1) and a<=t+1
        if b<=p[3]:
            return a-b==t or a-b==t+1
        return a==p[0]+t or a==p[0]+t+1
    return False


def r5_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for r in [3,4]:
        base.append(BoundaryLabel(0,0,0,-2,r))
    for r in range(3,6):
        base.append(BoundaryLabel(2,0,-1,-2,r))
    for r in [2,3]:
        base.append(BoundaryLabel(2,2,0,-2,r))
        base.append(BoundaryLabel(2,1,0,-2,r))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def in_r5_image(w: BoundaryLabel) raises -> Bool:
    var z=w if w.c<0 else reverse_label(w)
    if z.c!=-2:
        return False
    if z.top==0 and z.bottom==0 and z.x==0:
        return z.y==3 or z.y==4
    if z.top==2 and z.bottom==0 and z.x==-1:
        return z.y>=3 and z.y<=5
    return z.top==2 and (z.bottom==1 or z.bottom==2) and z.x==0 and (z.y==2 or z.y==3)


def _append(mut out: List[BoundaryEdge],kind: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(kind,k,t)
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if not r5_child_allowed(kind,k,t,a,b):
        raise Error("synthesized R5 guard failed")
    var target=member_transport(-1,k,p[0],p[1],r5_source(kind),a,b)
    if not in_r5_image(target):
        raise Error("R5 target escaped exact image")
    out.append(BoundaryEdge(a,b,target))


def r5_child_star(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var out=List[BoundaryEdge]()
    if t<=1:
        _append(out,kind,k,t,0,0)
    for i in range(max(1,t-1),t+2):
        _append(out,kind,k,t,i,0)
    for delta in [t,t+1]:
        for j in range(1,p[3]+1):
            _append(out,kind,k,t,j+delta,j)
    for i in [p[0]+t,p[0]+t+1]:
        _append(out,kind,k,t,i,p[0])
    return out^


def verify_r5_packet(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not r5_child_allowed(kind,k,t,edge.i,edge.j) or not in_r5_image(edge.target):
        raise Error("R5 packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],r5_source(kind),edge.i,edge.j,edge.target)


def verify_r5_star(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edges: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    if len(edges)!=2*p[0]+(2 if t==0 else 3):
        raise Error("incomplete R5 indexed star")
    var stride=checked_add(p[3] if kind==0 else p[2],2)
    var seen=Dict[Int,Bool]()
    for edge in edges:
        verify_r5_packet(tables,kind,k,t,edge)
        var key=checked_add(checked_mul(edge.i,stride),edge.j)
        if key in seen:
            raise Error("duplicate R5 occurrence")
        seen[key]=True


def r5_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=_dimensions(kind,k,t)
    return y4_path(2+kind,k,t)


def verify_r5_path(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    _=_dimensions(kind,k,t)
    if len(steps)!=3:
        raise Error("R5 selected path must have three edges")
    verify_y4_path(tables,2+kind,k,t,steps)
