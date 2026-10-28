"""Complete B5 stars and typed tails for every actual indexed child.

E7 tails are scoped to n=4, never registered as uniform companion exits.
"""
from finite_exact.checked_int import checked_add, checked_mul
from std.collections import Dict
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_y4_children import certify_y4_children, y4_source, y4_child_tail, in_y4_image, y4_star_interface, y4_exit_interface, _reverse_steps
from psc.class_a_boundary_r3_children import r3_source, r3_path
from psc.class_a_boundary_q3_children import q3_source, q3_path
from psc.class_a_boundary_r4_children import _image, _transition
from psc.class_a_boundary_e_children import eh_source, _offset
from psc.class_a_boundary_p3_children import p3_source
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, _child, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _cone_nonnegative
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def b5_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=6:
        raise Error("unknown B5/endpoint orientation")
    var w=BoundaryLabel(2,0,-1,-2,3)
    if kind//2>=1:
        w=BoundaryLabel(0,0,0,1,kind//2-1) # E6 then E7
    return reverse_label(w) if kind%2==1 else w


def b5_star_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=y4_star_interface(w,True)
    if old!=0:return old
    if include_new and (w==b5_source(0) or w==b5_source(1)):return 37
    return 0


def b5_exit_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=y4_exit_interface(w,True)
    if old!=0:return old
    if include_new:
        if w==b5_source(0) or w==b5_source(1):return 37
        if w==b5_source(2) or w==b5_source(3):return 38
    return 0 # E7 has n=4-only tails, not a uniform exit registration


def certify_b5_children(corrupt: Bool=False) raises:
    certify_y4_children()
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var t=p[3].copy()
    var A=qx_add(n,d)
    var N=qx_sub(n,qx_const(1))
    _cone_nonnegative(qx_sub(A,qx_add(d,qx_const(3))))
    _cone_nonnegative(qx_sub(A,qx_add(n,qx_const(2))))
    var beta=_linear(qx_const(0),qx_const(1))
    var beta2=tp_mul(beta,beta)
    var f=_cubic(-1,n,d)
    var ba=tp_sub(tp_sub(beta2,tp_scale(beta,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    for flip in range(2):
        var w=b5_source(flip)
        var base=_image(w,n,d)
        var expected: List[QX]=[qx_const(-1),qx_const(1),qx_neg(qx_add(d,qx_const(3)))]
        if flip==1:
            for z in range(3):expected[z]=qx_neg(expected[z])
        _equal3(base,expected)
        var field=tp_add(tp_add(tp_scale(ba,qx_const(w.x)),tp_scale(bb,qx_const(w.c))),tp_scale(beta,qx_const(w.y)))
        var image=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(beta,base[2]))
        if corrupt:image=tp_add(image,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(tp_mul(beta,field),f),tp_mod_monic(image,f))
        var betaG=_linear(qx_const(2),qx_neg(qx_add(d,qx_const(4))))
        # G=-(d+4+zeta), beta*zeta=beta*alpha-2.
        var alpha_beta=tp_sub(beta2,tp_scale(beta,qx_add(n,qx_const(2))))
        betaG=tp_sub(betaG,alpha_beta)
        if flip==1:betaG=tp_scale(betaG,qx_const(-1))
        _equal(tp_mod_monic(image,f),tp_mod_monic(betaG,f))
        var R=N.copy() if flip==0 else A.copy()
        var B=A.copy() if flip==0 else N.copy()
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
                        for z in range(3):want.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
                        _equal3(got,want)
        # Ancestry relies only on #379's already defined R5 source, not its full star.
        _transition(n,d,y4_source(2+flip),RUN if flip==0 else FIRST,qx_add(t,qx_const(1)) if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_add(t,qx_const(1)),w)
        _transition(n,d,w,FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_add(d,qx_const(3)),RUN if flip==0 else FIRST,qx_add(d,qx_const(3)) if flip==0 else qx_const(0),p3_source(3-flip))
        _transition(n,d,b5_source(2+flip),RUN if flip==0 else FIRST,qx_add(n,qx_const(2)) if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_add(n,qx_const(2)),eh_source(3-flip))
        _transition(n,d,eh_source(3-flip),RUN,qx_const(2 if flip==0 else 1),RUN,qx_const(1 if flip==0 else 2),BoundaryLabel(2,2,0,0,0))
        # Exact finite E7 cases: k=1,t=0 and k=0,t=1 only.
        for tt in [0,1]:
            var nn=qx_const(4)
            var dd=qx_const(6+tt)
            var middle=BoundaryLabel(0,0,1,2,-3-tt)
            _transition(nn,dd,b5_source(4+flip),LAST if flip==0 else FIRST,qx_const(11+tt) if flip==0 else qx_const(0),FIRST if flip==0 else LAST,qx_const(0) if flip==0 else qx_const(11+tt),reverse_label(middle) if flip==1 else middle)
            var next=p3_source(2+flip) if tt==0 else BoundaryLabel(2,2,0,-2,2)
            if tt==1 and flip==1:next=reverse_label(next)
            _transition(nn,dd,reverse_label(middle) if flip==1 else middle,RUN if flip==0 or tt==1 else FIRST,qx_const(9 if tt==0 else 6) if flip==0 else qx_const(0 if tt==0 else 1),FIRST if tt==0 and flip==0 else RUN,qx_const(0 if tt==0 else 1) if flip==0 else qx_const(9 if tt==0 else 6),next)
            _transition(nn,dd,next,RUN,qx_const(1 if flip==0 else (2 if tt==0 else 3)),RUN,qx_const((2 if tt==0 else 3) if flip==0 else 1),BoundaryLabel(2,2,0,0,0))
    print("CLASS_A_BOUNDARY_B5 two_complete_oriented_stars=true", "count=2n-1", "union_labels=24", "source_exit_two=true", "every_direct_child_productive=true", "tail_bound=7", "walk_bound=8", "E7_tail_n4_only=true", "closed_carrier=false", "global_BH=false")


def _dimensions(kind: Int,k: Int,t: Int) raises -> Tuple[Int,Int,Int,Int]:
    _=b5_source(kind)
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,12)
    return(p[0],p[1],A,p[0]-1)


def b5_child_allowed(kind: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    if kind<0 or kind>=2:raise Error("only B5 has a new complete-star interface")
    var p=_dimensions(kind,k,t)
    var R=p[3] if kind==0 else p[2]
    var B=p[2] if kind==0 else p[3]
    if i<0 or i>R+1 or j<0 or j>B+1:raise Error("nonexistent B5 occurrence")
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    var n=p[0]
    var d=p[1]
    var A=p[2]
    if a==0:return (b>=d+2 and b<=min(A,d+5)) or(b==A+1 and n<=4)
    if a>=1 and a<=p[3]:
        if b>=1 and b<=A:return b-a==d+4 or b-a==d+5
        return b==A+1 and a>=max(1,n-4)
    return False


def b5_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for r in range(-2,2):base.append(BoundaryLabel(0,2,0,1,r))
    for r in [0,1]:base.append(BoundaryLabel(0,0,0,1,r))
    for r in [1,2]:base.append(BoundaryLabel(2,2,-1,1,r))
    for r in range(-1,3):base.append(BoundaryLabel(2,0,-1,1,r))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def in_b5_image(w: BoundaryLabel) raises -> Bool:
    var z=w if w.c>0 else reverse_label(w)
    if z.c!=1:return False
    if z.top==0 and z.bottom==2:return z.x==0 and z.y>=-2 and z.y<=1
    if z.top==0 and z.bottom==0:return z.x==0 and z.y>=0 and z.y<=1
    if z.top==2 and z.bottom==2:return z.x==-1 and z.y>=1 and z.y<=2
    return z.top==2 and z.bottom==0 and z.x==-1 and z.y>=-1 and z.y<=2


def _append(mut out: List[BoundaryEdge],kind: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(kind,k,t)
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if not b5_child_allowed(kind,k,t,a,b):raise Error("synthesized B5 guard failed")
    var target=member_transport(-1,k,p[0],p[1],b5_source(kind),a,b)
    if not in_b5_image(target):raise Error("B5 target escaped image")
    out.append(BoundaryEdge(a,b,target))


def b5_child_star(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    if kind<0 or kind>=2:raise Error("no companion complete-star request")
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var d=p[1]
    var A=p[2]
    var out=List[BoundaryEdge]()
    for j in range(d+2,min(A,d+5)+1):_append(out,kind,k,t,0,j)
    if n<=4:_append(out,kind,k,t,0,A+1)
    for delta in [d+4,d+5]:
        for i in range(1,min(n-1,A-delta)+1):_append(out,kind,k,t,i,i+delta)
    for i in range(max(1,n-4),n):_append(out,kind,k,t,i,A+1)
    return out^


def verify_b5_packet(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not b5_child_allowed(kind,k,t,edge.i,edge.j) or not in_b5_image(edge.target):raise Error("B5 packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],b5_source(kind),edge.i,edge.j,edge.target)


def verify_b5_star(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edges: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    if len(edges)!=2*p[0]-1:raise Error("incomplete B5 indexed star")
    var stride=checked_add(p[2] if kind==0 else p[3],2)
    var seen=Dict[Int,Bool]()
    for edge in edges:
        verify_b5_packet(tables,kind,k,t,edge)
        var key=checked_add(checked_mul(edge.i,stride),edge.j)
        if key in seen:raise Error("duplicate B5 occurrence")
        seen[key]=True


def b5_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var out=List[BoundaryEdge]()
    var group=kind//2
    if group==0:
        out.append(BoundaryEdge(0,p[1]+3,p3_source(3)))
        out.append(BoundaryEdge(2,1,BoundaryLabel(2,2,0,0,0)))
    elif group==1:
        out.append(BoundaryEdge(p[0]+2,0,eh_source(3)))
        out.append(BoundaryEdge(2,1,BoundaryLabel(2,2,0,0,0)))
    else:
        if p[0]!=4:raise Error("E7 selected tail is scoped to n=4 only")
        out.append(BoundaryEdge(p[2]+1,0,BoundaryLabel(0,0,1,2,-3-t)))
        if t==0:
            out.append(BoundaryEdge(9,0,p3_source(2)))
            out.append(BoundaryEdge(1,2,BoundaryLabel(2,2,0,0,0)))
        else:
            out.append(BoundaryEdge(6,1,BoundaryLabel(2,2,0,-2,2)))
            out.append(BoundaryEdge(1,3,BoundaryLabel(2,2,0,0,0)))
    if kind%2==1:_reverse_steps(out)
    return out^


def b5_child_tail(w: BoundaryLabel,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=_dimensions(0,k,t)
    if not in_b5_image(w):raise Error("no B5-image tail interface")
    if in_y4_image(w):return y4_child_tail(w,k,t)
    for flip in range(2):
        if w==q3_source(flip):return q3_path(flip,k,t)
        if w==r3_source(flip):return r3_path(flip,k,t)
        for group in [1,2]:
            if w==b5_source(2*group+flip):return b5_path(2*group+flip,k,t)
    raise Error("B5 tail dispatch missed actual image label")


def b5_walk(kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    if not b5_child_allowed(kind,k,t,edge.i,edge.j) or member_transport(-1,k,p[0],p[1],b5_source(kind),edge.i,edge.j)!=edge.target:raise Error("B5 walk has wrong first indexed packet")
    var out: List[BoundaryEdge]=[edge]
    var suffix=b5_child_tail(edge.target,k,t)
    for step in suffix:out.append(step)
    return out^


def _verify(tables: SeedOverlapTables,w0: BoundaryLabel,k: Int,t: Int,steps: List[BoundaryEdge],want: List[BoundaryEdge]) raises:
    var p=_dimensions(0,k,t)
    if len(steps)!=len(want):raise Error("incomplete B5 typed path")
    var w=w0
    for z in range(len(steps)):
        var edge=steps[z]
        if edge.i!=want[z].i or edge.j!=want[z].j or edge.target!=want[z].target:raise Error("B5 intended intermediate/index mismatch")
        verify_member_edge(tables,-1,k,p[0],p[1],w,edge.i,edge.j,edge.target)
        w=edge.target
    if w!=BoundaryLabel(2,2,0,0,0):raise Error("B5 terminal is not typed coincidence")


def verify_b5_path(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    _verify(tables,b5_source(kind),k,t,steps,b5_path(kind,k,t))


def verify_b5_walk(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge,steps: List[BoundaryEdge]) raises:
    verify_b5_packet(tables,kind,k,t,edge)
    if len(steps)>8:raise Error("B5 first-choice walk exceeds eight edges")
    _verify(tables,b5_source(kind),k,t,steps,b5_walk(kind,k,t,edge))
