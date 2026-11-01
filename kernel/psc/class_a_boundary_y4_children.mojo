"""Y4 complete stars, every direct child's <=7-edge tail, and a real T cycle.

No forward closure or global BH. Derivation: docs/class-a-boundary-y4-carrier-2026-10-28.md.
"""
from finite_exact.checked_int import checked_add, checked_mul
from std.collections import Dict
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_r4_children import certify_r4_children, r4_source, r4_path, r4_star_interface, r4_exit_interface, _image, _transition
from psc.class_a_boundary_b3_children import b3_source, b3_path
from psc.class_a_boundary_b4_children import b4_source, b4_path
from psc.class_a_boundary_p3_children import p3_source
from psc.class_a_boundary_p_children import p_source, p_path
from psc.class_a_boundary_w_children import minus_seed_path
from psc.class_a_boundary_e_children import _offset
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, _child, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _cone_positive, _cone_nonnegative
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def y4_source(kind: Int) raises -> BoundaryLabel:
    # Only Y4 0/1 gets new complete stars. T2's complete star is inherited.
    if kind<0 or kind>=14:
        raise Error("unknown Y4/companion orientation")
    var w=BoundaryLabel(0,2,1,0,-1)
    if kind//2==1:
        w=BoundaryLabel(0,2,1,-1,-1) # R5
    elif kind//2==2:
        w=BoundaryLabel(0,1,1,-1,0) # D5
    elif kind//2==3:
        w=BoundaryLabel(2,2,-1,1,2) # T2
    elif kind//2==4:
        w=BoundaryLabel(2,0,0,3,-3) # M5
    elif kind//2==5:
        w=BoundaryLabel(1,0,0,3,-3) # CM
    elif kind//2==6:
        w=BoundaryLabel(2,0,-1,0,2) # F0
    return reverse_label(w) if kind%2==1 else w


def y4_star_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=r4_star_interface(w,True)
    if old!=0:
        return old
    if include_new:
        for flip in range(2):
            if w==y4_source(flip):
                return 26 # existing Y4 exit ID now also binds its complete star
    return 0


def y4_exit_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=r4_exit_interface(w,True)
    if old!=0:
        return old
    if include_new:
        for flip in range(2):
            if w==y4_source(6+flip):
                return 7 # previously classified T2 now gets a uniform exit
            for group in [1,2,4,5,6]:
                if w==y4_source(2*group+flip):
                    return 28+group if group<=2 else 27+group
    return 0


def _expected_image(kind: Int,n: QX,d: QX,k: QX,t: QX) raises -> List[QX]:
    _=y4_source(kind)
    var out: List[QX]=[qx_const(1),qx_const(-1),qx_add(d,qx_const(1))]
    if kind//2==1:
        out=[qx_const(0),qx_const(-2),qx_add(t,qx_const(3))]
    elif kind//2==2:
        out=[qx_const(1),qx_const(-1),d.copy()]
    elif kind//2==3:
        out=[qx_const(1),qx_const(3),qx_sub(k,qx_const(1))]
    elif kind//2==4 or kind//2==5:
        out=[qx_const(0),qx_const(0),qx_const(3)]
    elif kind//2==6:
        out=[qx_const(0),qx_const(2),qx_neg(qx_add(t,qx_const(4)))]
    if kind%2==1:
        for z in range(3):
            out[z]=qx_neg(out[z])
    return out^


def certify_y4_children(corrupt: Bool=False) raises:
    certify_r4_children() # every inherited suffix, T2 full star and chamber bounds
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var k=p[2].copy()
    var t=p[3].copy()
    var A=qx_add(n,d)
    var N=qx_sub(n,qx_const(1))
    _cone_nonnegative(qx_sub(N,qx_const(2)))
    _cone_nonnegative(qx_sub(A,qx_add(d,qx_const(3))))
    _cone_nonnegative(qx_sub(A,qx_add(t,qx_const(1))))
    var beta=_linear(qx_const(0),qx_const(1))
    var beta2=tp_mul(beta,beta)
    var f=_cubic(-1,n,d)
    var ba=tp_sub(tp_sub(beta2,tp_scale(beta,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    for kind in range(14):
        var w=y4_source(kind)
        var base=_image(w,n,d)
        _equal3(base,_expected_image(kind,n,d,k,t))
        var field=tp_add(tp_add(tp_scale(ba,qx_const(w.x)),tp_scale(bb,qx_const(w.c))),tp_scale(beta,qx_const(w.y)))
        var image=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(beta,base[2]))
        if corrupt:
            image=tp_add(image,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(tp_mul(beta,field),f),tp_mod_monic(image,f))
        if kind//2==0:
            var betaG=tp_add(beta2,_linear(qx_const(-2),qx_sub(d,n)))
            if kind%2==1:
                betaG=tp_scale(betaG,qx_const(-1))
            _equal(tp_mod_monic(image,f),betaG)
            var R=A.copy() if kind==0 else N.copy()
            var B=N.copy() if kind==0 else A.copy()
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
    for flip in range(2):
        # A genuine uniform two-cycle: T(0,1)->Y4(d+1,0)->T.
        _transition(n,d,p3_source(2+flip),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_const(1),RUN if flip==0 else FIRST,qx_const(1) if flip==0 else qx_const(0),y4_source(flip))
        _transition(n,d,y4_source(flip),RUN if flip==0 else FIRST,qx_add(d,qx_const(1)) if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_add(d,qx_const(1)),p3_source(2+flip))
        _transition(n,d,y4_source(flip),LAST,qx_add(A if flip==0 else N,qx_const(1)),LAST,qx_add(N if flip==0 else A,qx_const(1)),y4_source(4+flip))
        # Uniform RF representatives and both LR targets retain actual types.
        for r in range(-1,3):
            var index=qx_add(d,qx_const(2-r))
            var target=BoundaryLabel(2,0,0,-1,r)
            _transition(n,d,y4_source(flip),RUN if flip==0 else FIRST,index.copy() if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else index.copy(),reverse_label(target) if flip==1 else target)
        for step in [0,1]:
            var index=qx_sub(N,qx_const(1-step))
            _transition(n,d,y4_source(flip),LAST if flip==0 else RUN,qx_add(A,qx_const(1)) if flip==0 else index.copy(),RUN if flip==0 else LAST,index.copy() if flip==0 else qx_add(A,qx_const(1)),r4_source(flip) if step==0 else y4_source(2+flip))
        var rt1=BoundaryLabel(2,2,1,-1,-1)
        _transition(n,d,y4_source(flip),RUN,qx_add(d,qx_const(3)) if flip==0 else qx_const(1),RUN,qx_const(1) if flip==0 else qx_add(d,qx_const(3)),reverse_label(rt1) if flip==1 else rt1)
        # The second RR strip exists only on the n>=4 shifted cones.
        for dk in [0,1]:
            var nr=qx_add(n,qx_const(1))
            var dr=qx_add(d,qx_const(2-dk))
            _transition(nr,dr,y4_source(flip),RUN,qx_add(dr,qx_const(4)) if flip==0 else qx_const(1),RUN,qx_const(1) if flip==0 else qx_add(dr,qx_const(4)),y4_source(7-flip))
        _transition(n,d,y4_source(2+flip),RUN,qx_add(t,qx_const(1)) if flip==0 else qx_const(1),RUN,qx_const(1) if flip==0 else qx_add(t,qx_const(1)),p_source(7-flip))
        _transition(n,d,y4_source(4+flip),RUN,qx_add(d,qx_const(1)) if flip==0 else qx_const(1),RUN,qx_const(1) if flip==0 else qx_add(d,qx_const(1)),BoundaryLabel(2,2,0,0,0))
        _transition(n,d,y4_source(8+flip),RUN if flip==0 else FIRST,qx_const(2) if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_const(2),y4_source(12+flip))
        var v=BoundaryLabel(2,0,0,-1,2)
        _transition(n,d,y4_source(10+flip),RUN if flip==0 else FIRST,qx_const(2) if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_const(2),reverse_label(v) if flip==1 else v)
        _transition(n,d,y4_source(12+flip),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_add(t,qx_const(1)),RUN if flip==0 else FIRST,qx_add(t,qx_const(1)) if flip==0 else qx_const(0),p_source(8+flip))
        # T2 RF(k+3,0) is a true RUN on shifted t>=1 only.
        var ns=qx_add(n,qx_const(1))
        var ds=qx_add(d,qx_const(2))
        _transition(ns,ds,y4_source(6+flip),RUN if flip==0 else FIRST,qx_add(k,qx_const(3)) if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_add(k,qx_const(3)),y4_source(8+flip))
        # At t=0 it is LAST c, producing the distinct c/x companion CM.
        var n0=qx_add(k,qx_const(3))
        var d0=qx_add(k,qx_const(5))
        _transition(n0,d0,y4_source(6+flip),LAST if flip==0 else FIRST,n0.copy() if flip==0 else qx_const(0),FIRST if flip==0 else LAST,qx_const(0) if flip==0 else n0.copy(),y4_source(10+flip))
    print("CLASS_A_BOUNDARY_Y4 two_complete_oriented_stars=true", "count=2n+2", "union_labels=18", "source_exit_two=true", "T2_uniform_exit_at_most_seven=true", "every_direct_child_tail_at_most_seven=true", "every_first_choice_walk_at_most_eight=true", "Y4_T_cycle=true", "S41_escape_via_D5=true", "closed_carrier=false", "global_BH=false")


def _dimensions(kind: Int,k: Int,t: Int) raises -> Tuple[Int,Int,Int,Int]:
    _=y4_source(kind)
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,12)
    return(p[0],p[1],A,p[0]-1)


def y4_child_allowed(kind: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    if kind<0 or kind>=2:
        raise Error("new complete-star interface is only for Y4 orientations")
    var p=_dimensions(kind,k,t)
    var R=p[2] if kind==0 else p[3]
    var B=p[3] if kind==0 else p[2]
    if i<0 or i>R+1 or j<0 or j>B+1:
        raise Error("nonexistent Y4 occurrence")
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    var n=p[0]
    var d=p[1]
    var A=p[2]
    if a>=1 and a<=A:
        return a>=d and a<=d+3 if b==0 else b>=1 and b<=n-1 and (a-b==d+2 or a-b==d+3)
    return a==A+1 and (b==n-2 or b==n-1 or b==n)


def y4_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for r in range(-1,3):
        base.append(BoundaryLabel(2,0,0,-1,r))
    for r in [-2,-1]:
        base.append(BoundaryLabel(2,2,1,-1,r))
        base.append(BoundaryLabel(0,2,1,-1,r))
    base.append(y4_source(4))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def in_y4_image(w: BoundaryLabel) raises -> Bool:
    var z=w if w.c<0 else reverse_label(w)
    if z.c!=-1:
        return False
    if z.top==2 and z.bottom==0 and z.x==0:
        return z.y>=-1 and z.y<=2
    if (z.top==2 and z.bottom==2) or (z.top==0 and z.bottom==2):
        return z.x==1 and (z.y==-2 or z.y==-1)
    return z==y4_source(4)


def _append(mut out: List[BoundaryEdge],kind: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(kind,k,t)
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if not y4_child_allowed(kind,k,t,a,b):
        raise Error("synthesized Y4 guard failed")
    var target=member_transport(-1,k,p[0],p[1],y4_source(kind),a,b)
    if not in_y4_image(target):
        raise Error("Y4 target escaped exact image")
    out.append(BoundaryEdge(a,b,target))


def y4_child_star(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    if kind<0 or kind>=2:
        raise Error("no new companion complete-star certificate here")
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var d=p[1]
    var A=p[2]
    var out=List[BoundaryEdge]()
    for i in range(d,d+4):
        _append(out,kind,k,t,i,0)
    for delta in [d+2,d+3]:
        for j in range(1,min(n-1,A-delta)+1):
            _append(out,kind,k,t,j+delta,j)
    for j in range(n-2,n+1):
        _append(out,kind,k,t,A+1,j)
    return out^


def verify_y4_packet(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not y4_child_allowed(kind,k,t,edge.i,edge.j) or not in_y4_image(edge.target):
        raise Error("Y4 packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],y4_source(kind),edge.i,edge.j,edge.target)


def verify_y4_star(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edges: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    if kind>=2 or len(edges)!=2*p[0]+2:
        raise Error("incomplete Y4 indexed star or unsupported companion star")
    var stride=checked_add(p[3] if kind==0 else p[2],2)
    var seen=Dict[Int,Bool]()
    for edge in edges:
        verify_y4_packet(tables,kind,k,t,edge)
        var key=checked_add(checked_mul(edge.i,stride),edge.j)
        if key in seen:
            raise Error("duplicate Y4 occurrence")
        seen[key]=True


def _reverse_steps(mut steps: List[BoundaryEdge]) raises:
    for z in range(len(steps)):
        var edge=steps[z]
        steps[z]=BoundaryEdge(edge.j,edge.i,reverse_label(edge.target))


def _seed_suffix(start: Int,flip: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    if (start!=1 and start!=3) or flip<0 or flip>1:
        raise Error("unknown inherited seed suffix")
    var seed=minus_seed_path(k,t)
    var out=List[BoundaryEdge]()
    for z in range(start,len(seed)):
        out.append(seed[z])
    if flip==1:
        _reverse_steps(out)
    return out^


def y4_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var d=p[1]
    var out=List[BoundaryEdge]()
    if kind//2==0:
        return r4_path(6+kind%2,k,t)
    elif kind//2==1:
        out.append(BoundaryEdge(t+1,1,p_source(7)))
        var suffix=p_path(7,k,t)
        for edge in suffix:
            out.append(edge)
    elif kind//2==2:
        out.append(BoundaryEdge(d+1,1,BoundaryLabel(2,2,0,0,0)))
    elif kind//2==3:
        if t==0:
            out.append(BoundaryEdge(n,0,y4_source(10)))
            var suffix=y4_path(10,k,t)
            for edge in suffix:
                out.append(edge)
        else:
            out.append(BoundaryEdge(k+3,0,y4_source(8)))
            var suffix=y4_path(8,k,t)
            for edge in suffix:
                out.append(edge)
    elif kind//2==4:
        out.append(BoundaryEdge(2,0,y4_source(12)))
        var suffix=y4_path(12,k,t)
        for edge in suffix:
            out.append(edge)
    elif kind//2==5:
        out.append(BoundaryEdge(2,0,BoundaryLabel(2,0,0,-1,2)))
        var suffix=_seed_suffix(3,0,k,t)
        for edge in suffix:
            out.append(edge)
    else:
        out.append(BoundaryEdge(0,t+1,p_source(8)))
        var suffix=p_path(8,k,t)
        for edge in suffix:
            out.append(edge)
    if kind%2==1:
        _reverse_steps(out)
    return out^


def y4_child_tail(w: BoundaryLabel,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=_dimensions(0,k,t)
    if not in_y4_image(w):
        raise Error("no Y4-image tail interface for this target")
    for flip in range(2):
        var v=BoundaryLabel(2,0,0,-1,2)
        if w==(reverse_label(v) if flip==1 else v):
            return _seed_suffix(3,flip,k,t)
        if w==p3_source(2+flip):
            return [BoundaryEdge(2 if flip==1 else 1,1 if flip==1 else 2,BoundaryLabel(2,2,0,0,0))]
        if w==b3_source(flip):
            return b3_path(flip,k,t)
        if w==b4_source(flip):
            return b4_path(flip,k,t)
        var t1=BoundaryLabel(2,2,-1,1,1)
        if w==(reverse_label(t1) if flip==1 else t1):
            return _seed_suffix(1,flip,k,t)
        if w==y4_source(6+flip):
            return y4_path(6+flip,k,t)
        if w==r4_source(flip):
            return r4_path(flip,k,t)
        if w==y4_source(2+flip):
            return y4_path(2+flip,k,t)
        if w==y4_source(4+flip):
            return y4_path(4+flip,k,t)
    raise Error("complete Y4 tail dispatch missed an image label")


def y4_walk(kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    if not y4_child_allowed(kind,k,t,edge.i,edge.j) or member_transport(-1,k,p[0],p[1],y4_source(kind),edge.i,edge.j)!=edge.target:
        raise Error("Y4 first-choice walk has wrong first packet")
    var out: List[BoundaryEdge]=[edge]
    var suffix=y4_child_tail(edge.target,k,t)
    for step in suffix:
        out.append(step)
    return out^


def _verify_steps(tables: SeedOverlapTables,w0: BoundaryLabel,k: Int,t: Int,steps: List[BoundaryEdge],want: List[BoundaryEdge]) raises:
    var p=_dimensions(0,k,t)
    if len(steps)!=len(want):
        raise Error("incomplete Y4/companion typed path")
    var w=w0
    for z in range(len(steps)):
        var edge=steps[z]
        if edge.i!=want[z].i or edge.j!=want[z].j or edge.target!=want[z].target:
            raise Error("Y4 intended typed intermediate or index mismatch")
        verify_member_edge(tables,-1,k,p[0],p[1],w,edge.i,edge.j,edge.target)
        w=edge.target
    if w!=BoundaryLabel(2,2,0,0,0):
        raise Error("Y4 path terminal is not typed coincidence")


def verify_y4_path(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    _=_dimensions(kind,k,t)
    _verify_steps(tables,y4_source(kind),k,t,steps,y4_path(kind,k,t))


def verify_y4_walk(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge,steps: List[BoundaryEdge]) raises:
    verify_y4_packet(tables,kind,k,t,edge)
    if len(steps)>8:
        raise Error("Y4 first-choice walk exceeded its eight-edge bound")
    _verify_steps(tables,y4_source(kind),k,t,steps,y4_walk(kind,k,t,edge))
