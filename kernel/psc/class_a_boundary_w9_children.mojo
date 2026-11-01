"""W9 complete indexed stars and a constant sixteen-label memberwise image."""
from finite_exact.checked_int import checked_add, checked_mul
from std.collections import Dict
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_j9_children import _dimensions
from psc.class_a_boundary_p9_children import p9_companion, p9_companion_path
from psc.class_a_boundary_h9_children import certify_h9_children, h9_star_interface, h9_exit_interface
from psc.class_a_boundary_r4_children import _image, _transition, r4_source, r4_path
from psc.class_a_boundary_j8_children import j8_source, j8_path
from psc.class_a_boundary_e7_children import verify_e7_steps
from psc.class_a_boundary_e_children import _offset, eh_source, short_eh_path
from psc.class_a_boundary_h3_children import chain_source, chain_path
from psc.class_a_boundary_y4_children import y4_source, y4_path, _reverse_steps
from psc.class_a_boundary_b5_children import b5_source, b5_path
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, _child, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters
from psc.param_poly import QX, qx_mul, qx_const, qx_add, qx_sub, qx_neg, tp_add, tp_sub, tp_scale, tp_mul, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def w9_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=2:raise Error("unknown W9 orientation")
    return p9_companion(kind)


def w9_star_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=h9_star_interface(w,True)
    if old!=0:return old
    if include_new and (w==w9_source(0) or w==w9_source(1)):return 64
    return 0


def w9_companion(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=12:raise Error("unknown W9 companion")
    var base: List[BoundaryLabel]=[BoundaryLabel(2,0,-1,-2,5),BoundaryLabel(0,2,0,-2,2),BoundaryLabel(0,2,0,-2,3),BoundaryLabel(0,2,0,-2,4),BoundaryLabel(2,2,0,-2,2),BoundaryLabel(2,2,0,-2,3)]
    var w=base[kind//2]
    return reverse_label(w) if kind%2==1 else w


def w9_exit_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=h9_exit_interface(w,True)
    if old!=0:return old
    if include_new:
        for kind in range(12):
            if w==w9_companion(kind):return 69+kind//2
    return 0


def certify_w9_children(corrupt: Bool=False) raises:
    certify_h9_children()
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var k=p[2].copy()
    var A=qx_add(n,d)
    var beta=_linear(qx_const(0),qx_const(1))
    var f=_cubic(-1,n,d)
    var ba=tp_sub(tp_sub(tp_mul(beta,beta),tp_scale(beta,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    for flip in range(2):
        var w=w9_source(flip)
        var base=_image(w,n,d)
        var want: List[QX]=[qx_const(0),qx_const(-2),qx_add(qx_sub(n,k),qx_const(4))]
        if flip==1:
            for z in range(3):want[z]=qx_neg(want[z])
        _equal3(base,want)
        var image=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(beta,base[2]))
        var expected=_linear(qx_const(-2),qx_add(p[3],qx_const(5)))
        if flip==1:expected=tp_scale(expected,qx_const(-1))
        if corrupt:expected=tp_add(expected,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(image,f),tp_mod_monic(expected,f))
        for ri in [1,2]:
            for rj in [1,2]:
                var top: List[QX]=[qx_const(0),qx_const(ri),qx_add(A,qx_const(1))]
                var bottom: List[QX]=[qx_const(0),qx_const(rj),qx_add(A,qx_const(1))]
                for tk in range(3):
                    for bk in range(3):
                        var got=symbolic_child(-1,w.top,w.bottom,_offset(w),tk,top[tk],bk,bottom[bk],_child(w.top,tk),_child(w.bottom,bk))
                        var pt=_prefix(w.top,tk,top[tk],-1,n,d)
                        var pb=_prefix(w.bottom,bk,bottom[bk],-1,n,d)
                        var target=List[QX]()
                        for z in range(3):target.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
                        _equal3(got,target)
    for kind in range(12):
        var group=kind//2
        var r=2 if group==1 or group==4 else (3 if group==2 or group==5 else 4)
        var want: List[QX]=[qx_const(1),qx_const(3),qx_sub(k,qx_const(4))]
        if group!=0:want=[qx_const(r-2),qx_const(r-2),qx_sub(qx_mul(n,qx_const(r-2)),qx_const(r))]
        if kind%2==1:
            for z in range(3):want[z]=qx_neg(want[z])
        var w=w9_companion(kind)
        var got=_image(w,n,d)
        _equal3(got,want)
        var field=tp_add(tp_add(tp_scale(ba,qx_const(w.x)),tp_scale(bb,qx_const(w.c))),tp_scale(beta,qx_const(w.y)))
        var image=tp_add(tp_add(tp_scale(ba,got[0]),tp_scale(bb,got[1])),tp_scale(beta,got[2]))
        _equal(tp_mod_monic(tp_mul(beta,field),f),tp_mod_monic(image,f))
        var pos=qx_add(k,qx_const(1))
        var target=j8_source(5)
        var run_top=True
        if group==1 or group==4:
            pos=qx_const(2);target=y4_source(0);run_top=False
        elif group==2 or group==5:
            pos=qx_sub(n,qx_const(1));target=eh_source(3)
        elif group==3:
            pos=qx_add(qx_add(n,n),qx_const(1));target=chain_source(2)
        if kind%2==1:
            target=reverse_label(target)
            run_top=not run_top
        _transition(n,d,w,RUN if run_top else FIRST,pos.copy() if run_top else qx_const(0),FIRST if run_top else RUN,qx_const(0) if run_top else pos.copy(),target)
    print("CLASS_A_BOUNDARY_W9 complete_oriented_stars=2 memberwise_image_labels=16 count=4n+1 source_exit=4 all_actual_first_choice_walk_le_6=true closed_carrier=false global_BH=false")


def w9_count(k: Int,t: Int) raises -> Int:
    var p=_dimensions(0,k,t)
    return checked_add(checked_mul(4,p[0]),1)


def w9_child_allowed(kind: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    _=w9_source(kind)
    var p=_dimensions(0,k,t)
    var A=p[2]
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if a<0 or a>A+1 or b<0 or b>A+1:raise Error("nonexistent W9 occurrence")
    if a>=1 and a<=A:
        if b==0:return a>=t+3 and a<=t+5
        return b>=1 and b<=A and (a-b==t+4 or a-b==t+5)
    return a==A+1 and b>=A-t-4 and b<=A-t-2


def w9_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for r in [3,4,5]:base.append(BoundaryLabel(2,0,-1,-2,r))
    for r in [2,3]:base.append(BoundaryLabel(2,2,0,-2,r))
    for r in [2,3,4]:base.append(BoundaryLabel(0,2,0,-2,r))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def in_w9_image(w: BoundaryLabel) raises -> Bool:
    var z=w if w.c<0 else reverse_label(w)
    if z.c != -2:return False
    if z.top==2 and z.bottom==0:return z.x == -1 and z.y>=3 and z.y<=5
    if z.x!=0 or z.bottom!=2:return False
    if z.top==2:return z.y==2 or z.y==3
    return z.top==0 and z.y>=2 and z.y<=4


def _append(mut out: List[BoundaryEdge],kind: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(0,k,t)
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if not w9_child_allowed(kind,k,t,a,b):raise Error("W9 synthesized guard failed")
    var target=member_transport(-1,k,p[0],p[1],w9_source(kind),a,b)
    if not in_w9_image(target):raise Error("W9 target escaped image")
    out.append(BoundaryEdge(a,b,target))


def w9_child_star(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=w9_source(kind)
    var p=_dimensions(0,k,t)
    var A=p[2]
    _=w9_count(k,t)
    var out=List[BoundaryEdge]()
    for i in range(t+3,t+6):_append(out,kind,k,t,i,0)
    for delta in [t+4,t+5]:
        for j in range(1,A-delta+1):_append(out,kind,k,t,j+delta,j)
    for j in range(A-t-4,A-t-1):_append(out,kind,k,t,A+1,j)
    return out^


def verify_w9_packet(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(0,k,t)
    if not w9_child_allowed(kind,k,t,edge.i,edge.j) or not in_w9_image(edge.target):raise Error("W9 packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],w9_source(kind),edge.i,edge.j,edge.target)


def verify_w9_star(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edges: List[BoundaryEdge]) raises:
    _=w9_source(kind)
    if len(edges)!=w9_count(k,t):raise Error("incomplete W9 star")
    var p=_dimensions(0,k,t)
    var seen=Dict[Int,Bool]()
    for edge in edges:
        verify_w9_packet(tables,kind,k,t,edge)
        var key=checked_add(checked_mul(edge.i,checked_add(p[2],2)),edge.j)
        if key in seen:raise Error("duplicate W9 occurrence")
        seen[key]=True


def w9_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=w9_source(kind)
    return p9_companion_path(kind,k,t)


def verify_w9_path(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    verify_e7_steps(tables,w9_source(kind),k,t,steps,w9_path(kind,k,t))




def _extend(mut out: List[BoundaryEdge],suffix: List[BoundaryEdge]):
    for edge in suffix:out.append(edge)


def w9_companion_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=w9_companion(kind)
    var p=_dimensions(0,k,t)
    var group=kind//2
    var out=List[BoundaryEdge]()
    if group==0:
        out.append(BoundaryEdge(k+1,0,j8_source(5)))
        _extend(out,j8_path(5,k,t))
    elif group==1 or group==4:
        out.append(BoundaryEdge(0,2,y4_source(0)))
        _extend(out,y4_path(0,k,t))
    elif group==2 or group==5:
        out.append(BoundaryEdge(p[0]-1,0,eh_source(3)))
        _extend(out,short_eh_path(3,k,t))
    else:
        out.append(BoundaryEdge(2*p[0]+1,0,chain_source(2)))
        _extend(out,chain_path(2,k,t))
    if kind%2==1:_reverse_steps(out)
    return out^


def w9_child_tail(w: BoundaryLabel,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=_dimensions(0,k,t)
    if not in_w9_image(w):raise Error("outside W9 image tail interface")
    for flip in range(2):
        if w==b5_source(flip):return b5_path(flip,k,t)
        if w==p9_companion(2+flip):return p9_companion_path(2+flip,k,t)
        for group in range(6):
            if w==w9_companion(2*group+flip):return w9_companion_path(2*group+flip,k,t)
    raise Error("W9 complete image tail dispatcher missed a label")


def w9_child_walk(kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises -> List[BoundaryEdge]:
    var p=_dimensions(0,k,t)
    if not w9_child_allowed(kind,k,t,edge.i,edge.j) or member_transport(-1,k,p[0],p[1],w9_source(kind),edge.i,edge.j)!=edge.target:raise Error("wrong first W9 packet")
    var out: List[BoundaryEdge]=[edge]
    _extend(out,w9_child_tail(edge.target,k,t))
    return out^


def verify_w9_walk(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge,steps: List[BoundaryEdge]) raises:
    if len(steps)>6:raise Error("W9 selected first-choice bound exceeded")
    verify_e7_steps(tables,w9_source(kind),k,t,steps,w9_child_walk(kind,k,t,edge))
