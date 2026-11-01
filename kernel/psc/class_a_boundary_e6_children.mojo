"""Complete E6 stars and bounded tails through every actual first choice."""
from finite_exact.checked_int import checked_add, checked_mul
from std.collections import Dict
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_b5_children import certify_b5_children, b5_source, b5_path, b5_star_interface, b5_exit_interface
from psc.class_a_boundary_r4_children import r4_source, r4_path, _image, _transition
from psc.class_a_boundary_h3_children import chain_source, chain_path
from psc.class_a_boundary_p_children import p_source, p_path
from psc.class_a_boundary_p3_children import p3_source
from psc.class_a_boundary_e_children import eh_source, short_eh_path, _offset
from psc.class_a_boundary_y4_children import _reverse_steps
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, _child, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _cone_nonnegative
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_mul, qx_neg, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def e6_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=8:raise Error("unknown E6/companion orientation")
    var w=b5_source(2)
    if kind//2>=1:w=BoundaryLabel(0,2,1,1,kind//2-5) # J6/K6/L6: -4,-3,-2
    return reverse_label(w) if kind%2==1 else w


def e6_star_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=b5_star_interface(w,True)
    if old!=0:return old
    if include_new and (w==e6_source(0) or w==e6_source(1)):return 38
    return 0


def e6_exit_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=b5_exit_interface(w,True)
    if old!=0:return old
    if include_new:
        for kind in range(2,8):
            if w==e6_source(kind):return 38+kind//2
    return 0


def _expected(kind: Int,n: QX,d: QX,k: QX,t: QX) raises -> List[QX]:
    _=e6_source(kind)
    var out: List[QX]=[qx_const(1),qx_const(1),n.copy()]
    if kind//2==1:out=[qx_const(-1),qx_const(-3),qx_sub(qx_const(3),k)]
    elif kind//2==2:out=[qx_const(0),qx_const(-2),qx_add(t,qx_const(5))]
    elif kind//2==3:out=[qx_const(1),qx_const(-1),qx_add(d,qx_const(2))]
    if kind%2==1:
        for z in range(3):out[z]=qx_neg(out[z])
    return out^


def certify_e6_children(corrupt: Bool=False) raises:
    certify_b5_children()
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var k=p[2].copy()
    var t=p[3].copy()
    var A=qx_add(n,d)
    _cone_nonnegative(qx_sub(A,qx_add(n,qx_const(4))))
    _cone_nonnegative(qx_sub(d,qx_const(4)))
    var beta=_linear(qx_const(0),qx_const(1))
    var beta2=tp_mul(beta,beta)
    var f=_cubic(-1,n,d)
    var ba=tp_sub(tp_sub(beta2,tp_scale(beta,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    for kind in range(8):
        var w=e6_source(kind)
        var base=_image(w,n,d)
        _equal3(base,_expected(kind,n,d,k,t))
        var field=tp_add(tp_add(tp_scale(ba,qx_const(w.x)),tp_scale(bb,qx_const(w.c))),tp_scale(beta,qx_const(w.y)))
        var image=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(beta,base[2]))
        if corrupt:image=tp_add(image,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(tp_mul(beta,field),f),tp_mod_monic(image,f))
        if kind//2==0:
            var betaG=tp_add(beta2,beta)
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
        for group in [1,2,3]:
            var j=qx_add(d,qx_const(group-4))
            _transition(n,d,e6_source(flip),LAST if flip==0 else RUN,qx_add(A,qx_const(1)) if flip==0 else j.copy(),RUN if flip==0 else LAST,j.copy() if flip==0 else qx_add(A,qx_const(1)),e6_source(2*group+flip))
        _transition(n,d,e6_source(2+flip),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_add(k,qx_const(1)),RUN if flip==0 else FIRST,qx_add(k,qx_const(1)) if flip==0 else qx_const(0),r4_source(4+flip))
        _transition(n,d,e6_source(4+flip),RUN if flip==0 else FIRST,qx_add(t,qx_const(3)) if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_add(t,qx_const(3)),b5_source(flip))
        _transition(n,d,e6_source(6+flip),RUN if flip==0 else FIRST,qx_add(d,qx_const(2)) if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_add(d,qx_const(2)),p3_source(2+flip))
        # Actual three-cycle at the sole n=3 member only.
        _transition(qx_const(3),qx_const(5),b5_source(flip),FIRST if flip==0 else LAST,qx_const(0) if flip==0 else qx_const(9),LAST if flip==0 else FIRST,qx_const(9) if flip==0 else qx_const(0),e6_source(flip))
    print("CLASS_A_BOUNDARY_E6 two_complete_oriented_stars=true", "count=2d-1", "union_labels=16", "source_exit_two=true", "every_direct_child_tail_at_most_eight=true", "walk_bound=9", "n3_three_cycle=true", "image_escape_via_K6=true", "closed_carrier=false", "global_BH=false")


def _dimensions(kind: Int,k: Int,t: Int) raises -> Tuple[Int,Int,Int,Int]:
    _=e6_source(kind)
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,12)
    return(p[0],p[1],A,p[0]-1)


def e6_child_allowed(kind: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    if kind<0 or kind>=2:raise Error("only E6 has a new complete-star interface")
    var p=_dimensions(kind,k,t)
    var A=p[2]
    if i<0 or i>A+1 or j<0 or j>A+1:raise Error("nonexistent E6 occurrence")
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if a>=1 and a<=A:
        if b==0:return a>=p[0]+2 and a<=p[0]+4
        return b>=1 and b<=A and (a-b==p[0]+3 or a-b==p[0]+4)
    return a==A+1 and b>=p[1]-3 and b<=p[1]-1


def e6_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for r in [-3,-2,-1]:base.append(BoundaryLabel(2,0,0,1,r))
    for r in [-4,-3]:base.append(BoundaryLabel(2,2,1,1,r))
    for r in [-4,-3,-2]:base.append(BoundaryLabel(0,2,1,1,r))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def in_e6_image(w: BoundaryLabel) raises -> Bool:
    var z=w if w.c>0 else reverse_label(w)
    if z.c!=1:return False
    if z.top==2 and z.bottom==0:return z.x==0 and z.y>=-3 and z.y<=-1
    if z.top==2 and z.bottom==2:return z.x==1 and (z.y==-4 or z.y==-3)
    return z.top==0 and z.bottom==2 and z.x==1 and z.y>=-4 and z.y<=-2


def _append(mut out: List[BoundaryEdge],kind: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(kind,k,t)
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if not e6_child_allowed(kind,k,t,a,b):raise Error("synthesized E6 guard failed")
    var target=member_transport(-1,k,p[0],p[1],e6_source(kind),a,b)
    if not in_e6_image(target):raise Error("E6 target escaped image")
    out.append(BoundaryEdge(a,b,target))


def e6_child_star(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    if kind<0 or kind>=2:raise Error("no new companion complete-star request")
    var p=_dimensions(kind,k,t)
    var out=List[BoundaryEdge]()
    for i in range(p[0]+2,p[0]+5):_append(out,kind,k,t,i,0)
    for delta in [p[0]+3,p[0]+4]:
        for j in range(1,p[2]-delta+1):_append(out,kind,k,t,j+delta,j)
    for j in range(p[1]-3,p[1]):_append(out,kind,k,t,p[2]+1,j)
    return out^


def verify_e6_packet(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not e6_child_allowed(kind,k,t,edge.i,edge.j) or not in_e6_image(edge.target):raise Error("E6 packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],e6_source(kind),edge.i,edge.j,edge.target)


def verify_e6_star(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edges: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    if len(edges)!=2*p[1]-1:raise Error("incomplete E6 indexed star")
    var seen=Dict[Int,Bool]()
    var stride=checked_add(p[2],2)
    for edge in edges:
        verify_e6_packet(tables,kind,k,t,edge)
        var key=checked_add(checked_mul(edge.i,stride),edge.j)
        if key in seen:raise Error("duplicate E6 occurrence")
        seen[key]=True


def e6_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    if kind//2==0:return b5_path(2+kind%2,k,t)
    var out=List[BoundaryEdge]()
    if kind//2==1:
        out.append(BoundaryEdge(0,k+1,r4_source(4)))
        var suffix=r4_path(4,k,t)
        for edge in suffix:out.append(edge)
    elif kind//2==2:
        out.append(BoundaryEdge(t+3,0,b5_source(0)))
        var suffix=b5_path(0,k,t)
        for edge in suffix:out.append(edge)
    else:
        out.append(BoundaryEdge(p[1]+2,0,p3_source(2)))
        out.append(BoundaryEdge(1,2,BoundaryLabel(2,2,0,0,0)))
    if kind%2==1:_reverse_steps(out)
    return out^


def e6_child_tail(w: BoundaryLabel,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=_dimensions(0,k,t)
    if not in_e6_image(w):raise Error("no E6-image tail interface")
    for flip in range(2):
        if w==eh_source(2+flip):return short_eh_path(2+flip,k,t)
        if w==eh_source(4+flip):return short_eh_path(4+flip,k,t)
        if w==chain_source(flip):return chain_path(flip,k,t)
        for group in [0,1]:
            if w==p_source(2*group+flip):return p_path(2*group+flip,k,t)
        for group in [1,2,3]:
            if w==e6_source(2*group+flip):return e6_path(2*group+flip,k,t)
    raise Error("E6 image dispatch missed a label")


def e6_walk(kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    if not e6_child_allowed(kind,k,t,edge.i,edge.j) or member_transport(-1,k,p[0],p[1],e6_source(kind),edge.i,edge.j)!=edge.target:raise Error("wrong E6 first indexed packet")
    var out: List[BoundaryEdge]=[edge]
    var suffix=e6_child_tail(edge.target,k,t)
    for step in suffix:out.append(step)
    return out^


def _verify(tables: SeedOverlapTables,w0: BoundaryLabel,k: Int,t: Int,steps: List[BoundaryEdge],want: List[BoundaryEdge]) raises:
    var p=_dimensions(0,k,t)
    if len(steps)!=len(want):raise Error("incomplete E6 typed path")
    var w=w0
    for z in range(len(steps)):
        var e=steps[z]
        if e.i!=want[z].i or e.j!=want[z].j or e.target!=want[z].target:raise Error("E6 intended intermediate/index mismatch")
        verify_member_edge(tables,-1,k,p[0],p[1],w,e.i,e.j,e.target)
        w=e.target
    if w!=BoundaryLabel(2,2,0,0,0):raise Error("E6 terminal is not typed coincidence")


def verify_e6_path(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    _verify(tables,e6_source(kind),k,t,steps,e6_path(kind,k,t))


def verify_e6_walk(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge,steps: List[BoundaryEdge]) raises:
    verify_e6_packet(tables,kind,k,t,edge)
    if len(steps)>9:raise Error("E6 full walk exceeds nine edges")
    _verify(tables,e6_source(kind),k,t,steps,e6_walk(kind,k,t,edge))
