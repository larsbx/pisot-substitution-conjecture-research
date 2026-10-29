"""P9 complete oriented stars. Existing selected exits remain separate."""
from finite_exact.checked_int import checked_add, checked_mul
from std.collections import Dict
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_j9_children import certify_j9_children, j9_source, j9_star_interface, j9_exit_interface, j9_path, _dimensions
from psc.class_a_boundary_e7_children import verify_e7_steps
from psc.class_a_boundary_r4_children import _image, _transition, r4_source, r4_path
from psc.class_a_boundary_j8_children import j8_source, j8_path
from psc.class_a_boundary_b5_children import b5_source, b5_path
from psc.class_a_boundary_y4_children import _reverse_steps
from psc.class_a_boundary_e_children import _offset
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, _child, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg, tp_add, tp_sub, tp_scale, tp_mul, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def p9_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=2:raise Error("unknown P9 orientation")
    return j9_source(2+kind)


def p9_star_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=j9_star_interface(w,True)
    if old!=0:return old
    if include_new and (w==p9_source(0) or w==p9_source(1)):return 62
    return 0


def p9_companion(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=6:raise Error("unknown P9 companion")
    var base: List[BoundaryLabel]=[BoundaryLabel(0,0,1,3,-5),BoundaryLabel(2,0,-1,-2,4),BoundaryLabel(0,2,2,3,-6)]
    var w=base[kind//2]
    return reverse_label(w) if kind%2==1 else w


def p9_exit_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=j9_exit_interface(w,True)
    if old!=0:return old
    if include_new:
        for kind in range(4):
            if w==p9_companion(kind):return 64+kind//2
    return 0


def certify_p9_children(corrupt: Bool=False) raises:
    certify_j9_children()
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var k=p[2].copy()
    var beta=_linear(qx_const(0),qx_const(1))
    var f=_cubic(-1,n,d)
    var ba=tp_sub(tp_sub(tp_mul(beta,beta),tp_scale(beta,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    # beta*G=beta^2+(k-n-3)*beta+2, G=k-1+w.
    for flip in range(2):
        var w=p9_source(flip)
        var base=_image(w,n,d)
        var want: List[QX]=[qx_const(1),qx_const(3),qx_sub(k,qx_const(6))]
        if flip==1:
            for z in range(3):want[z]=qx_neg(want[z])
        _equal3(base,want)
        var image=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(beta,base[2]))
        var expected=tp_add(tp_mul(beta,beta),_linear(qx_const(2),qx_sub(qx_sub(k,n),qx_const(3))))
        if flip==1:expected=tp_scale(expected,qx_const(-1))
        if corrupt:expected=tp_add(expected,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(image,f),tp_mod_monic(expected,f))
        var R=qx_add(n,d) if flip==0 else qx_sub(n,qx_const(1))
        var B=qx_sub(n,qx_const(1)) if flip==0 else qx_add(n,d)
        for ri in [1,2]:
            for rj in [1,2]:
                var top: List[QX]=[qx_const(0),qx_const(ri),qx_add(R,qx_const(1))]
                var bottom: List[QX]=[qx_const(0),qx_const(rj),qx_add(B,qx_const(1))]
                for tk in range(3):
                    for bk in range(3):
                        var got=symbolic_child(-1,w.top,w.bottom,_offset(w),tk,top[tk],bk,bottom[bk],_child(w.top,tk),_child(w.bottom,bk))
                        var pt=_prefix(w.top,tk,top[tk],-1,n,d)
                        var pb=_prefix(w.bottom,bk,bottom[bk],-1,n,d)
                        var target=List[QX]()
                        for z in range(3):target.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
                        _equal3(got,target)
    for kind in range(6):
        var w=p9_companion(kind)
        var want: List[QX]=[qx_const(0),qx_const(-2),qx_add(qx_sub(n,k),qx_const(4))]
        if kind//2==1:want=[qx_const(0),qx_const(2),qx_sub(qx_sub(k,n),qx_const(3))]
        elif kind//2==2:want=[qx_const(1),qx_const(-3),qx_add(qx_sub(qx_add(qx_add(n,n),n),qx_add(k,k)),qx_const(4))]
        if kind%2==1:
            for z in range(3):want[z]=qx_neg(want[z])
        var got=_image(w,n,d)
        _equal3(got,want)
        var field=tp_add(tp_add(tp_scale(ba,qx_const(w.x)),tp_scale(bb,qx_const(w.c))),tp_scale(beta,qx_const(w.y)))
        var image=tp_add(tp_add(tp_scale(ba,got[0]),tp_scale(bb,got[1])),tp_scale(beta,got[2]))
        _equal(tp_mod_monic(tp_mul(beta,field),f),tp_mod_monic(image,f))
    for flip in range(2):
        var r=qx_add(p[3],qx_const(4))
        _transition(n,d,p9_companion(flip),RUN if flip==0 else FIRST,r.copy() if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else r.copy(),p9_companion(2+flip))
        _transition(n,d,p9_companion(2+flip),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else r.copy(),RUN if flip==0 else FIRST,r.copy() if flip==0 else qx_const(0),b5_source(1-flip))
        var nr=qx_add(p[3],qx_const(3))
        var dr=qx_add(qx_add(p[3],p[3]),qx_const(5))
        var last=qx_add(qx_add(nr,dr),qx_const(1))
        _transition(nr,dr,p9_companion(4+flip),LAST if flip==0 else FIRST,last.copy() if flip==0 else qx_const(0),FIRST if flip==0 else LAST,qx_const(0) if flip==0 else last.copy(),j8_source(20+flip))
    print("CLASS_A_BOUNDARY_P9 complete_oriented_stars=2 chamber_union_labels=24 count=2n+2+[k>=2] selected_exit_k0=7 selected_exit_kpositive=6 all_child_productivity=true max_selected_first_choice_walk=9 closed_carrier=false global_BH=false")


def p9_count(k: Int,t: Int) raises -> Int:
    var p=_dimensions(0,k,t)
    return checked_add(checked_mul(2,p[0]),2+(1 if k>=2 else 0))


def p9_child_allowed(kind: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    _=p9_source(kind)
    var p=_dimensions(0,k,t)
    var n=p[0]
    var A=p[2]
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if a<0 or a>A+1 or b<0 or b>n:raise Error("nonexistent P9 occurrence")
    if a==0:return (k<=2) if b==0 else (k==0 and b==1)
    if a<=A:
        if b==0:return a>=max(1,k-2) and a<=k
        if b<n:return a-b==k or a-b==k-1
        return a>=k+n-1 and a<=k+n+(1 if k==0 else 0)
    return False


def p9_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for r in range(-6,-3):base.append(BoundaryLabel(0,0,1,3,r))
    base.append(BoundaryLabel(0,2,2,3,-6))
    for r in range(-5,-2):base.append(BoundaryLabel(2,0,0,3,r))
    for r in [-6,-5]:base.append(BoundaryLabel(2,2,1,3,r))
    for r in range(-7,-4):base.append(BoundaryLabel(2,1,1,3,r))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def in_p9_image(w: BoundaryLabel) raises -> Bool:
    var z=w if w.c>0 else reverse_label(w)
    if z.c!=3:return False
    if z.top==0 and z.bottom==0:return z.x==1 and z.y>=-6 and z.y<=-4
    if z.top==0 and z.bottom==2:return z.x==2 and z.y == -6
    if z.top==2 and z.bottom==0:return z.x==0 and z.y>=-5 and z.y<=-3
    if z.x!=1 or z.top!=2:return False
    if z.bottom==2:return z.y == -6 or z.y == -5
    return z.bottom==1 and z.y>=-7 and z.y<=-5


def _append(mut out: List[BoundaryEdge],kind: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(0,k,t)
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if not p9_child_allowed(kind,k,t,a,b):raise Error("P9 synthesized guard failed")
    var target=member_transport(-1,k,p[0],p[1],p9_source(kind),a,b)
    if not in_p9_image(target):raise Error("P9 target escaped chamber image")
    out.append(BoundaryEdge(a,b,target))


def p9_child_star(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=p9_source(kind)
    var p=_dimensions(0,k,t)
    var n=p[0]
    var out=List[BoundaryEdge]()
    if k<=2:_append(out,kind,k,t,0,0)
    if k==0:_append(out,kind,k,t,0,1)
    for i in range(max(1,k-2),k+1):_append(out,kind,k,t,i,0)
    for delta in [k,k-1]:
        for j in range(max(1,1-delta),n):_append(out,kind,k,t,j+delta,j)
    for i in range(k+n-1,k+n+1+(1 if k==0 else 0)):_append(out,kind,k,t,i,n)
    return out^


def verify_p9_packet(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(0,k,t)
    if not p9_child_allowed(kind,k,t,edge.i,edge.j) or not in_p9_image(edge.target):raise Error("P9 packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],p9_source(kind),edge.i,edge.j,edge.target)


def verify_p9_star(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edges: List[BoundaryEdge]) raises:
    if len(edges)!=p9_count(k,t):raise Error("incomplete P9 star")
    var p=_dimensions(0,k,t)
    var stride=checked_add(p[0] if kind==0 else p[2],1 if kind==0 else 2)
    var seen=Dict[Int,Bool]()
    for edge in edges:
        verify_p9_packet(tables,kind,k,t,edge)
        var key=checked_add(checked_mul(edge.i,stride),edge.j)
        if key in seen:raise Error("duplicate P9 occurrence")
        seen[key]=True


def p9_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=p9_source(kind)
    return j9_path(2+kind,k,t)


def verify_p9_path(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    verify_e7_steps(tables,p9_source(kind),k,t,steps,p9_path(kind,k,t))



def _extend(mut out: List[BoundaryEdge],suffix: List[BoundaryEdge]):
    for edge in suffix:out.append(edge)


def p9_companion_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=p9_companion(kind)
    var p=_dimensions(0,k,t)
    var out=List[BoundaryEdge]()
    if kind//2==0:
        out.append(BoundaryEdge(t+4,0,p9_companion(2)))
        _extend(out,p9_companion_path(2,k,t))
    elif kind//2==1:
        out.append(BoundaryEdge(0,t+4,b5_source(1)))
        _extend(out,b5_path(1,k,t))
    else:
        if k!=0:raise Error("X9 selected tail is k=0-only")
        out.append(BoundaryEdge(p[2]+1,0,j8_source(20)))
        _extend(out,j8_path(20,k,t))
    if kind%2==1:_reverse_steps(out)
    return out^


def p9_child_tail(w: BoundaryLabel,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=_dimensions(0,k,t)
    if not in_p9_image(w):raise Error("outside P9 image tail interface")
    for flip in range(2):
        if w==j9_source(4+flip):return j9_path(4+flip,k,t)
        if w==p9_companion(flip):return p9_companion_path(flip,k,t)
        if w==p9_companion(4+flip):return p9_companion_path(4+flip,k,t)
        for group in [1,2,3,4,5,6,13]:
            if w==j8_source(2*group+flip):return j8_path(2*group+flip,k,t)
        for group in [2,5]:
            if w==r4_source(2*group+flip):return r4_path(2*group+flip,k,t)
    raise Error("P9 image tail dispatch missed a label")


def p9_child_walk(kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises -> List[BoundaryEdge]:
    var p=_dimensions(0,k,t)
    if not p9_child_allowed(kind,k,t,edge.i,edge.j) or member_transport(-1,k,p[0],p[1],p9_source(kind),edge.i,edge.j)!=edge.target:raise Error("wrong P9 first packet")
    var out: List[BoundaryEdge]=[edge]
    _extend(out,p9_child_tail(edge.target,k,t))
    return out^


def verify_p9_walk(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge,steps: List[BoundaryEdge]) raises:
    if len(steps)>9:raise Error("P9 selected first-choice bound exceeded")
    verify_e7_steps(tables,p9_source(kind),k,t,steps,p9_child_walk(kind,k,t,edge))
