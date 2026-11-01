"""Complete E7 stars with exact half-chambers and uniform selected exits.

Only E7 receives new stars. All-child productivity is certified on t<=1 only.
"""
from finite_exact.checked_int import checked_add, checked_mul
from std.collections import Dict
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_b4_children import b4_source, b4_path
from psc.class_a_boundary_e2_children import e2_source, e2_path
from psc.class_a_boundary_e6_children import certify_e6_children, e6_star_interface, e6_exit_interface
from psc.class_a_boundary_b5_children import b5_source, b5_child_tail, in_b5_image
from psc.class_a_boundary_h3_children import chain_source, chain_path, alpha_high
from psc.class_a_boundary_h5_children import h5_child_source, h5_child_path
from psc.class_a_boundary_p_children import p_source, p_path
from psc.class_a_boundary_p3_children import p3_source
from psc.class_a_boundary_y4_children import _reverse_steps
from psc.class_a_boundary_r4_children import _image, _transition
from psc.class_a_boundary_e_children import _offset
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, _child, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _cone_nonnegative
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_mul, qx_neg, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def e7_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=6:raise Error("unknown E7/companion orientation")
    var w=b5_source(4)
    if kind//2>=1:w=BoundaryLabel(0,0,1,2,-2-kind//2) # U7=-3, V7=-4
    return reverse_label(w) if kind%2==1 else w


def e7_star_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=e6_star_interface(w,True)
    if old!=0:return old
    for flip in range(2):
        if w==chain_source(2+flip):return 42 # inherited J complete star
        if w==h5_child_source(flip):return 46 # inherited H5 complete star
        if include_new and w==e7_source(flip):return 43
    return 0


def e7_exit_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=e6_exit_interface(w,True)
    if old!=0:return old
    for flip in range(2):
        if w==chain_source(2+flip):return 42
        if w==h5_child_source(flip):return 46
    if include_new and (w==e7_source(0) or w==e7_source(1)):return 43
    return 0


def _expected(kind: Int,n: QX,d: QX,t: QX) raises -> List[QX]:
    _=e7_source(kind)
    var out: List[QX]=[qx_const(2),qx_const(2),qx_sub(qx_add(n,n),qx_const(1))]
    if kind//2==1:out=[qx_const(1),qx_const(-1),qx_add(d,qx_const(3))]
    elif kind//2==2:out=[qx_const(0),qx_const(-2),qx_add(t,qx_const(6))]
    if kind%2==1:
        for z in range(3):out[z]=qx_neg(out[z])
    return out^


def certify_e7_children(corrupt: Bool=False) raises:
    certify_e6_children() # includes exact half separator and B2/H5/J suffixes
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var k=p[2].copy()
    var t=p[3].copy()
    var A=qx_add(n,d)
    _cone_nonnegative(qx_sub(A,qx_add(d,qx_const(3))))
    _cone_nonnegative(qx_sub(A,qx_add(t,qx_const(5))))
    var beta=_linear(qx_const(0),qx_const(1))
    var beta2=tp_mul(beta,beta)
    var f=_cubic(-1,n,d)
    var ba=tp_sub(tp_sub(beta2,tp_scale(beta,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    for kind in range(6):
        var w=e7_source(kind)
        var base=_image(w,n,d)
        _equal3(base,_expected(kind,n,d,t))
        var field=tp_add(tp_add(tp_scale(ba,qx_const(w.x)),tp_scale(bb,qx_const(w.c))),tp_scale(beta,qx_const(w.y)))
        var image=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(beta,base[2]))
        if corrupt:image=tp_add(image,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(tp_mul(beta,field),f),tp_mod_monic(image,f))
        if kind//2==0:
            var betaG=tp_add(tp_scale(beta2,qx_const(2)),beta)
            if kind%2==1:betaG=tp_scale(betaG,qx_const(-1))
            _equal(tp_mod_monic(image,f),tp_mod_monic(betaG,f))
            for ri in [1,2]:
                for rj in [1,2]:
                    var top: List[QX]=[qx_const(0),qx_const(ri),qx_add(A,qx_const(1))]
                    var bottom: List[QX]=[qx_const(0),qx_const(rj),qx_add(A,qx_const(1))]
                    for tk in range(3):
                        for bk in range(3):
                            var got=symbolic_child(-1,w.top,w.bottom,_offset(w),tk,top[tk],bk,bottom[bk],_child(w.top,tk),_child(w.bottom,bk))
                            var pt=_prefix(w.top,tk,top[tk],-1,n,d)
                            var pb=_prefix(w.bottom,bk,bottom[bk],-1,n,d)
                            var want=List[QX]()
                            for z in range(3):want.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
                            _equal3(got,want)
    for flip in range(2):
        if e7_source(2+flip)!=b4_source(3-flip):raise Error("U7 must retain the existing D0 identity")
        if e7_source(4+flip)!=e2_source(2+flip):raise Error("V7 must retain the existing Dxx identity")
        # t=0,1 LAST/FIRST source exit on each complete k cone.
        for tt in [0,1]:
            var nn=qx_add(k,qx_const(3+tt))
            var dd=qx_add(k,qx_const(5+2*tt))
            var AA=qx_add(nn,dd)
            _transition(nn,dd,e7_source(flip),LAST if flip==0 else FIRST,qx_add(AA,qx_const(1)) if flip==0 else qx_const(0),FIRST if flip==0 else LAST,qx_const(0) if flip==0 else qx_add(AA,qx_const(1)),e7_source(2+2*tt+flip))
        # t=t'+2: 2n+4 is now a true RUN, including t=2's last run.
        var ns=qx_add(n,qx_const(2))
        var ds=qx_add(d,qx_const(4))
        var index=qx_add(qx_add(ns,ns),qx_const(4))
        _transition(ns,ds,e7_source(flip),RUN if flip==0 else FIRST,index.copy() if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else index.copy(),chain_source(2+flip))
        _transition(n,d,e7_source(2+flip),RUN if flip==0 else FIRST,qx_add(d,qx_const(3)) if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_add(d,qx_const(3)),p3_source(2+flip))
        _transition(n,d,e7_source(4+flip),RUN,qx_add(t,qx_const(5)) if flip==0 else qx_const(1),RUN,qx_const(1) if flip==0 else qx_add(t,qx_const(5)),p_source(5-flip))
    print("CLASS_A_BOUNDARY_E7 two_complete_oriented_stars=true", "count=max(1,2t-1)", "chamber_union_labels=32", "half_split_inherited=true", "source_exit_t0_t1=3", "source_exit_tge2=5", "all_direct_children_productive_tle1=true", "all_t_all_child_productivity=false", "closed_carrier=false", "global_BH=false")


def _dimensions(kind: Int,k: Int,t: Int) raises -> Tuple[Int,Int,Int,Int]:
    _=e7_source(kind)
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,16)
    return(p[0],p[1],A,p[0]-1)


def e7_child_allowed(kind: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    if kind<0 or kind>=2:raise Error("only E7 has a new complete-star interface")
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var A=p[2]
    if i<0 or i>A+1 or j<0 or j>A+1:raise Error("nonexistent E7 occurrence")
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    var e=1 if alpha_high(k,t) else 0
    if a>=1 and a<=A:
        if b==0:return a>=2*n+4 and a<=2*n+6+e
        return b>=1 and b<=A and (a-b==2*n+5+e or a-b==2*n+6+e)
    if a==A+1:
        return t<=3+e if b==0 else b>=max(1,t-3-e) and b<=t-1
    return False


def e7_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for r in range(-7,-3):base.append(BoundaryLabel(2,0,1,2,r))
    for r in range(-8,-5):base.append(BoundaryLabel(2,2,2,2,r))
    for r in range(-7,-2):base.append(BoundaryLabel(0,0,1,2,r))
    for r in range(-8,-4):base.append(BoundaryLabel(0,2,2,2,r))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def in_e7_image(w: BoundaryLabel) raises -> Bool:
    var z=w if w.c>0 else reverse_label(w)
    if z.c!=2:return False
    if z.top==2 and z.bottom==0:return z.x==1 and z.y>=-7 and z.y<=-4
    if z.top==2 and z.bottom==2:return z.x==2 and z.y>=-8 and z.y<=-6
    if z.top==0 and z.bottom==0:return z.x==1 and z.y>=-7 and z.y<=-3
    return z.top==0 and z.bottom==2 and z.x==2 and z.y>=-8 and z.y<=-5


def _append(mut out: List[BoundaryEdge],kind: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(kind,k,t)
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if not e7_child_allowed(kind,k,t,a,b):raise Error("synthesized E7 guard failed")
    var target=member_transport(-1,k,p[0],p[1],e7_source(kind),a,b)
    if not in_e7_image(target):raise Error("E7 target escaped image")
    out.append(BoundaryEdge(a,b,target))


def e7_child_star(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    if kind<0 or kind>=2:raise Error("no new companion complete-star request")
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var A=p[2]
    var e=1 if alpha_high(k,t) else 0
    var out=List[BoundaryEdge]()
    for i in range(2*n+4,min(A,2*n+6+e)+1):_append(out,kind,k,t,i,0)
    for delta in [2*n+5+e,2*n+6+e]:
        for j in range(1,A-delta+1):_append(out,kind,k,t,j+delta,j)
    if t<=3+e:_append(out,kind,k,t,A+1,0)
    for j in range(max(1,t-3-e),t):_append(out,kind,k,t,A+1,j)
    return out^


def verify_e7_packet(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not e7_child_allowed(kind,k,t,edge.i,edge.j) or not in_e7_image(edge.target):raise Error("E7 packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],e7_source(kind),edge.i,edge.j,edge.target)


def verify_e7_star(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edges: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    if len(edges)!=max(1,2*t-1):raise Error("incomplete E7 indexed star")
    var seen=Dict[Int,Bool]()
    var stride=checked_add(p[2],2)
    for edge in edges:
        verify_e7_packet(tables,kind,k,t,edge)
        var key=checked_add(checked_mul(edge.i,stride),edge.j)
        if key in seen:raise Error("duplicate E7 occurrence")
        seen[key]=True


def e7_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var out=List[BoundaryEdge]()
    if kind//2==0:
        if t<=1:
            out.append(BoundaryEdge(p[2]+1,0,e7_source(2+2*t)))
            var suffix=e7_path(2+2*t,k,t)
            for edge in suffix:out.append(edge)
        else:
            out.append(BoundaryEdge(2*p[0]+4,0,chain_source(2)))
            var suffix=chain_path(2,k,t)
            for edge in suffix:out.append(edge)
    elif kind//2==1:
        return b4_path(3-kind%2,k,t)
    else:
        if p[0]==3:return e2_path(2+kind%2,k,t)
        out.append(BoundaryEdge(t+5,1,p_source(5)))
        var suffix=p_path(5,k,t)
        for edge in suffix:out.append(edge)
    if kind%2==1:_reverse_steps(out)
    return out^


def e7_registered_tail(w: BoundaryLabel,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=_dimensions(0,k,t)
    if not in_e7_image(w):raise Error("outside E7 image tail interface")
    for flip in range(2):
        if w==chain_source(2+flip):return chain_path(2+flip,k,t)
        if w==h5_child_source(flip):return h5_child_path(flip,k,t)
        for group in [1,2]:
            if w==e7_source(2*group+flip):return e7_path(2*group+flip,k,t)
    raise Error("no registered uniform E7-image tail for this label")


def e7_uniform_b5_tail(w: BoundaryLabel,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=_dimensions(0,k,t)
    if not in_b5_image(w):raise Error("outside B5 image uniform tail interface")
    for flip in range(2):
        if w==e7_source(flip):return e7_path(flip,k,t)
    return b5_child_tail(w,k,t)


def verify_e7_steps(tables: SeedOverlapTables,w0: BoundaryLabel,k: Int,t: Int,steps: List[BoundaryEdge],want: List[BoundaryEdge]) raises:
    var p=_dimensions(0,k,t)
    if len(steps)!=len(want):raise Error("incomplete E7 typed path")
    var w=w0
    for z in range(len(steps)):
        var e=steps[z]
        if e.i!=want[z].i or e.j!=want[z].j or e.target!=want[z].target:raise Error("E7 intended intermediate/index mismatch")
        verify_member_edge(tables,-1,k,p[0],p[1],w,e.i,e.j,e.target)
        w=e.target
    if w!=BoundaryLabel(2,2,0,0,0):raise Error("E7 terminal is not typed coincidence")


def verify_e7_path(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    verify_e7_steps(tables,e7_source(kind),k,t,steps,e7_path(kind,k,t))
