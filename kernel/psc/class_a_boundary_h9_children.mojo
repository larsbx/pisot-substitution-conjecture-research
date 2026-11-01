"""H9 complete actual indexed stars, retaining equal-target endpoint events."""
from finite_exact.checked_int import checked_add, checked_mul
from std.collections import Dict
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_j9_children import j9_source, j9_path, _dimensions
from psc.class_a_boundary_p9_children import certify_p9_children, p9_star_interface, p9_exit_interface, p9_companion, p9_companion_path
from psc.class_a_boundary_r4_children import _image, _transition, r4_source, r4_path
from psc.class_a_boundary_j8_children import j8_source, j8_path
from psc.class_a_boundary_e7_children import verify_e7_steps
from psc.class_a_boundary_e_children import _offset
from psc.class_a_boundary_y4_children import y4_child_tail, _reverse_steps
from psc.class_a_boundary_b5_children import b5_source, b5_path
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, _child, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg, tp_add, tp_sub, tp_scale, tp_mul, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def h9_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=2:raise Error("unknown H9 orientation")
    return j9_source(4+kind)


def h9_star_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=p9_star_interface(w,True)
    if old!=0:return old
    if include_new and (w==h9_source(0) or w==h9_source(1)):return 63
    return 0


def h9_companion(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=6:raise Error("unknown H9 companion")
    var w=BoundaryLabel(2,0,-1,-3,4+kind//2)
    return reverse_label(w) if kind%2==1 else w


def h9_exit_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=p9_exit_interface(w,True)
    if old!=0:return old
    if include_new:
        for kind in range(6):
            if w==h9_companion(kind):return 66+kind//2
    return 0


def certify_h9_children(corrupt: Bool=False) raises:
    certify_p9_children()
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
        var w=h9_source(flip)
        var base=_image(w,n,d)
        var want: List[QX]=[qx_const(-1),qx_const(-3),qx_sub(qx_const(5),k)]
        if flip==1:
            for z in range(3):want[z]=qx_neg(want[z])
        _equal3(base,want)
        var image=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(beta,base[2]))
        var expected=tp_add(tp_scale(tp_mul(beta,beta),qx_const(-1)),_linear(qx_const(-2),qx_add(qx_sub(n,k),qx_const(2))))
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
    for kind in range(6):
        var w=h9_companion(kind)
        var r=kind//2
        var want: List[QX]=[qx_const(r-1),qx_const(r+1),qx_add(qx_sub(k,qx_add(n,n)),qx_const(-3))]
        if r==1:want[2]=qx_sub(qx_sub(k,n),qx_const(4))
        elif r==2:want[2]=qx_sub(k,qx_const(5))
        if kind%2==1:
            for z in range(3):want[z]=qx_neg(want[z])
        var got=_image(w,n,d)
        _equal3(got,want)
        var field=tp_add(tp_add(tp_scale(ba,qx_const(w.x)),tp_scale(bb,qx_const(w.c))),tp_scale(beta,qx_const(w.y)))
        var image=tp_add(tp_add(tp_scale(ba,got[0]),tp_scale(bb,got[1])),tp_scale(beta,got[2]))
        _equal(tp_mod_monic(tp_mul(beta,field),f),tp_mod_monic(image,f))
    for flip in range(2):
        for group in range(3):
            var pos=qx_add(d,qx_const(3)) if group==0 else (qx_add(p[3],qx_const(5)) if group==1 else qx_add(k,qx_const(1)))
            var target=BoundaryLabel(0,2,0,1,-2) if group==0 else (b5_source(1) if group==1 else r4_source(11))
            if flip==1:target=reverse_label(target)
            var run_top=(group==2) != (flip==1)
            _transition(n,d,h9_companion(2*group+flip),RUN if run_top else FIRST,pos.copy() if run_top else qx_const(0),FIRST if run_top else RUN,qx_const(0) if run_top else pos.copy(),target)
    print("CLASS_A_BOUNDARY_H9 complete_oriented_stars=2 chamber_union_labels=20 count_k_le_1=2A+3 count_k_ge_2=2A-2k+5 source_exit=6 every_actual_first_choice_walk_le_7=true closed_carrier=false global_BH=false")


def h9_count(k: Int,t: Int) raises -> Int:
    var p=_dimensions(0,k,t)
    return checked_add(checked_mul(2,p[2] if k<=1 else p[2]-k),3 if k<=1 else 5)


def h9_child_allowed(kind: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    _=h9_source(kind)
    var p=_dimensions(0,k,t)
    var A=p[2]
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if a<0 or a>A+1 or b<0 or b>A+1:raise Error("nonexistent H9 occurrence")
    if a==0:return (k<=1) if b==0 else b>=max(1,k-1) and b<=k+1
    if a<=A:
        if b>=1 and b<=A:return b-a==k or b-a==k+1
        return b==A+1 and a>=A-k and a<=min(A,A-k+2)
    return b==A+1 and k<=1


def h9_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for r in [4,5]:base.append(BoundaryLabel(0,0,-1,-3,r))
    for r in range(3,6):base.append(BoundaryLabel(0,2,0,-3,r))
    for r in [5,6]:base.append(BoundaryLabel(2,2,-1,-3,r))
    for r in range(4,7):base.append(BoundaryLabel(2,0,-1,-3,r))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def in_h9_image(w: BoundaryLabel) raises -> Bool:
    var z=w if w.c<0 else reverse_label(w)
    if z.c != -3:return False
    if z.top==0 and z.bottom==0:return z.x == -1 and (z.y==4 or z.y==5)
    if z.top==0 and z.bottom==2:return z.x==0 and z.y>=3 and z.y<=5
    if z.x != -1 or z.top!=2:return False
    if z.bottom==2:return z.y==5 or z.y==6
    return z.bottom==0 and z.y>=4 and z.y<=6


def _append(mut out: List[BoundaryEdge],kind: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(0,k,t)
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if not h9_child_allowed(kind,k,t,a,b):raise Error("H9 synthesized guard failed")
    var target=member_transport(-1,k,p[0],p[1],h9_source(kind),a,b)
    if not in_h9_image(target):raise Error("H9 target escaped image")
    out.append(BoundaryEdge(a,b,target))


def h9_child_star(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=h9_source(kind)
    var p=_dimensions(0,k,t)
    var A=p[2]
    _=h9_count(k,t)
    var out=List[BoundaryEdge]()
    if k<=1:_append(out,kind,k,t,0,0)
    for j in range(max(1,k-1),k+2):_append(out,kind,k,t,0,j)
    for delta in [k,k+1]:
        for i in range(1,A-delta+1):_append(out,kind,k,t,i,i+delta)
    for i in range(A-k,min(A,A-k+2)+1):_append(out,kind,k,t,i,A+1)
    if k<=1:_append(out,kind,k,t,A+1,A+1)
    return out^


def verify_h9_packet(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(0,k,t)
    if not h9_child_allowed(kind,k,t,edge.i,edge.j) or not in_h9_image(edge.target):raise Error("H9 packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],h9_source(kind),edge.i,edge.j,edge.target)


def verify_h9_star(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edges: List[BoundaryEdge]) raises:
    _=h9_source(kind)
    if len(edges)!=h9_count(k,t):raise Error("incomplete H9 star")
    var p=_dimensions(0,k,t)
    var seen=Dict[Int,Bool]()
    for edge in edges:
        verify_h9_packet(tables,kind,k,t,edge)
        var key=checked_add(checked_mul(edge.i,checked_add(p[2],2)),edge.j)
        if key in seen:raise Error("duplicate H9 occurrence")
        seen[key]=True


def h9_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=h9_source(kind)
    return j9_path(4+kind,k,t)


def verify_h9_path(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    verify_e7_steps(tables,h9_source(kind),k,t,steps,h9_path(kind,k,t))



def _extend(mut out: List[BoundaryEdge],suffix: List[BoundaryEdge]):
    for edge in suffix:out.append(edge)


def h9_companion_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=h9_companion(kind)
    var p=_dimensions(0,k,t)
    var out=List[BoundaryEdge]()
    if kind//2==0:
        var target=BoundaryLabel(0,2,0,1,-2)
        out.append(BoundaryEdge(0,p[1]+3,target))
        _extend(out,y4_child_tail(target,k,t))
    elif kind//2==1:
        out.append(BoundaryEdge(0,t+5,b5_source(1)))
        _extend(out,b5_path(1,k,t))
    else:
        out.append(BoundaryEdge(k+1,0,r4_source(11)))
        _extend(out,r4_path(11,k,t))
    if kind%2==1:_reverse_steps(out)
    return out^


def h9_child_tail(w: BoundaryLabel,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=_dimensions(0,k,t)
    if not in_h9_image(w):raise Error("outside H9 image tail interface")
    for flip in range(2):
        if w==p9_companion(flip):return p9_companion_path(flip,k,t)
        for group in [1,2,3,4]:
            if w==j8_source(2*group+flip):return j8_path(2*group+flip,k,t)
        for group in [2,5]:
            if w==r4_source(2*group+flip):return r4_path(2*group+flip,k,t)
        for group in range(3):
            if w==h9_companion(2*group+flip):return h9_companion_path(2*group+flip,k,t)
    raise Error("H9 complete image tail dispatch missed a label")


def h9_child_walk(kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises -> List[BoundaryEdge]:
    var p=_dimensions(0,k,t)
    if not h9_child_allowed(kind,k,t,edge.i,edge.j) or member_transport(-1,k,p[0],p[1],h9_source(kind),edge.i,edge.j)!=edge.target:raise Error("wrong first H9 packet")
    var out: List[BoundaryEdge]=[edge]
    _extend(out,h9_child_tail(edge.target,k,t))
    return out^


def verify_h9_walk(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge,steps: List[BoundaryEdge]) raises:
    if len(steps)>7:raise Error("H9 selected first-choice bound exceeded")
    verify_e7_steps(tables,h9_source(kind),k,t,steps,h9_child_walk(kind,k,t,edge))
