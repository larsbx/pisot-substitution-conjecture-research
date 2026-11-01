"""Complete existing D0 stars and <=8-edge walks for every first choice.

Base orientation is U7=R(D0); its two-edge exit and all image tails are reused.
"""
from finite_exact.checked_int import checked_add, checked_mul
from std.collections import Dict
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_e7_children import certify_e7_children, e7_source, e7_path, e7_star_interface, e7_exit_interface, e7_uniform_b5_tail, verify_e7_steps
from psc.class_a_boundary_b5_children import b5_source
from psc.class_a_boundary_r4_children import _image
from psc.class_a_boundary_e_children import _offset
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, _child
from psc.class_a_boundary_signs import chamber_parameters
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def d0_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=2:raise Error("unknown D0 orientation")
    return e7_source(2+kind) # U7 then original D0; preserve full typed identity


def d0_star_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=e7_star_interface(w,True)
    if old!=0:return old
    if include_new and (w==d0_source(0) or w==d0_source(1)):return 20
    return 0


def d0_exit_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    _=include_new
    return e7_exit_interface(w,True) # no new source or companion exit


def certify_d0_children(corrupt: Bool=False) raises:
    certify_e7_children()
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var A=qx_add(n,d)
    var beta=_linear(qx_const(0),qx_const(1))
    var beta2=tp_mul(beta,beta)
    var f=_cubic(-1,n,d)
    var ba=tp_sub(tp_sub(beta2,tp_scale(beta,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    for kind in range(2):
        var w=d0_source(kind)
        var base=_image(w,n,d)
        var expected: List[QX]=[qx_const(1),qx_const(-1),qx_add(d,qx_const(3))]
        if kind==1:
            for z in range(3):expected[z]=qx_neg(expected[z])
        _equal3(base,expected)
        # Same offset as R(B5), but sources have different actual tile types.
        _equal3(base,_image(b5_source(1-kind),n,d))
        if w==b5_source(1-kind):raise Error("D0 and B5 must remain distinct sources")
        var field=tp_add(tp_add(tp_scale(ba,qx_const(w.x)),tp_scale(bb,qx_const(w.c))),tp_scale(beta,qx_const(w.y)))
        var image=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(beta,base[2]))
        if corrupt:image=tp_add(image,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(tp_mul(beta,field),f),tp_mod_monic(image,f))
        # beta*(d+4+zeta), where beta*zeta=beta^2-(n+2)*beta-2.
        var betaG=tp_add(beta2,_linear(qx_const(-2),qx_add(qx_sub(d,n),qx_const(2))))
        if kind==1:betaG=tp_scale(betaG,qx_const(-1))
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
    print("CLASS_A_BOUNDARY_D0 two_complete_oriented_stars=true", "count=2n-1", "chamber_union_labels=24", "image_equals_B5=true", "source_exit_two_reused=true", "every_direct_child_productive=true", "tail_bound=7", "walk_bound=8", "new_companion_stars=false", "closed_carrier=false", "global_BH=false")


def _dimensions(kind: Int,k: Int,t: Int) raises -> Tuple[Int,Int,Int]:
    _=d0_source(kind)
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,12)
    return(p[0],p[1],A)


def d0_child_allowed(kind: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var d=p[1]
    var A=p[2]
    if i<0 or i>A+1 or j<0 or j>A+1:raise Error("nonexistent D0 occurrence")
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if a>=1 and a<=A:
        if b==0:return a>=d+2 and a<=d+5
        return b>=1 and b<=A and (a-b==d+4 or a-b==d+5)
    if a==A+1:
        return n<=4 if b==0 else b>=max(1,n-4) and b<=n-1
    return False


def d0_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for r in range(-1,3):base.append(BoundaryLabel(2,0,0,-1,r))
    for r in [-2,-1]:base.append(BoundaryLabel(2,2,1,-1,r))
    for r in [-1,0]:base.append(BoundaryLabel(0,0,0,-1,r))
    for r in range(-2,2):base.append(BoundaryLabel(0,2,1,-1,r))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def in_d0_image(w: BoundaryLabel) raises -> Bool:
    var z=w if w.c<0 else reverse_label(w)
    if z.c != -1:return False
    if z.top==2 and z.bottom==0:return z.x==0 and z.y>=-1 and z.y<=2
    if z.top==2 and z.bottom==2:return z.x==1 and (z.y==-2 or z.y==-1)
    if z.top==0 and z.bottom==0:return z.x==0 and (z.y==-1 or z.y==0)
    return z.top==0 and z.bottom==2 and z.x==1 and z.y>=-2 and z.y<=1


def _append(mut out: List[BoundaryEdge],kind: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(kind,k,t)
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if not d0_child_allowed(kind,k,t,a,b):raise Error("synthesized D0 guard failed")
    var target=member_transport(-1,k,p[0],p[1],d0_source(kind),a,b)
    if not in_d0_image(target):raise Error("D0 target escaped image")
    out.append(BoundaryEdge(a,b,target))


def d0_child_star(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var d=p[1]
    var A=p[2]
    var out=List[BoundaryEdge]()
    for i in range(d+2,min(A,d+5)+1):_append(out,kind,k,t,i,0)
    for delta in [d+4,d+5]:
        for j in range(1,A-delta+1):_append(out,kind,k,t,j+delta,j)
    if n<=4:_append(out,kind,k,t,A+1,0)
    for j in range(max(1,n-4),n):_append(out,kind,k,t,A+1,j)
    return out^


def verify_d0_packet(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not d0_child_allowed(kind,k,t,edge.i,edge.j) or not in_d0_image(edge.target):raise Error("D0 packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],d0_source(kind),edge.i,edge.j,edge.target)


def verify_d0_star(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edges: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    if len(edges)!=2*p[0]-1:raise Error("incomplete D0 indexed star")
    var seen=Dict[Int,Bool]()
    var stride=checked_add(p[2],2)
    for edge in edges:
        verify_d0_packet(tables,kind,k,t,edge)
        var key=checked_add(checked_mul(edge.i,stride),edge.j)
        if key in seen:raise Error("duplicate D0 occurrence")
        seen[key]=True


def d0_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=_dimensions(kind,k,t)
    return e7_path(2+kind,k,t)


def d0_child_tail(w: BoundaryLabel,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=_dimensions(0,k,t)
    if not in_d0_image(w):raise Error("outside D0 image tail interface")
    return e7_uniform_b5_tail(w,k,t)


def d0_walk(kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    if not d0_child_allowed(kind,k,t,edge.i,edge.j) or member_transport(-1,k,p[0],p[1],d0_source(kind),edge.i,edge.j)!=edge.target:raise Error("D0 walk has wrong first indexed target")
    var out: List[BoundaryEdge]=[edge]
    var suffix=d0_child_tail(edge.target,k,t)
    for step in suffix:out.append(step)
    return out^


def verify_d0_path(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    verify_e7_steps(tables,d0_source(kind),k,t,steps,d0_path(kind,k,t))


def verify_d0_walk(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge,steps: List[BoundaryEdge]) raises:
    verify_d0_packet(tables,kind,k,t,edge)
    if len(steps)>8:raise Error("D0 first-choice walk exceeds eight edges")
    verify_e7_steps(tables,d0_source(kind),k,t,steps,d0_walk(kind,k,t,edge))
