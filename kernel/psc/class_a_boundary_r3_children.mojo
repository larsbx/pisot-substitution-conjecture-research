"""Four R3/D3 oriented stars and an explicit reconciliation of the 39 labels.

Selected typed exits only; both the 39- and 41-label candidates escape.
Full guard derivation: docs/class-a-boundary-r3-carrier-2026-10-28.md.
"""
from finite_exact.checked_int import checked_add
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_q3_children import certify_q3_children, q3_source, q3_target
from psc.class_a_boundary_p3_children import p3_source, p3_image
from psc.class_a_boundary_p_children import p_source, p_path, certify_p_children
from psc.class_a_boundary_h3_children import chain_source
from psc.class_a_boundary_e_children import eh_source, _offset
from psc.class_a_boundary_tm_children import certify_tm_children
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, _child, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _cone_positive, _cone_nonnegative
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def r3_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=4:
        raise Error("unknown R3/D3 orientation")
    var w=BoundaryLabel(0,2,1,-1,0) if kind//2==0 else BoundaryLabel(0,1,1,-1,-1)
    return reverse_label(w) if kind%2==1 else w


def enlarged_candidate(include_d3: Bool=False) raises -> List[BoundaryLabel]:
    var out=p3_image()
    for flip in range(2):
        out.append(q3_target(flip))
    if include_d3:
        for flip in range(2):
            out.append(r3_source(2+flip))
    return out^


def star_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    """Registry of explicit complete-star interfaces; zero means unregistered.

    IDs: 1 terminal, 2 T, 3 U, 4 V, 5 E, 6 T1, 7 T2, 8 Q3, 9 X,
    10 R3, 11 D3, 12 P0, 13 P1, 14 H3. This is not a proof that no other mechanism can apply.
    """
    if w==BoundaryLabel(2,2,0,0,0):
        return 1
    for flip in range(2):
        if w==p3_source(2+flip):
            return 2
        if w==p3_source(4+flip):
            return 3
        var v=BoundaryLabel(2,0,0,-1,2)
        if w==(reverse_label(v) if flip==1 else v):
            return 4
        if w==eh_source(flip):
            return 5
        for m in [1,2]:
            var tm=BoundaryLabel(2,2,-1,1,m)
            if w==(reverse_label(tm) if flip==1 else tm):
                return 5+m
        if w==q3_source(flip):
            return 8
        if w==q3_target(flip):
            return 9
        for group in [0,1]:
            if w==p_source(2*group+flip):
                return 12+group
        if w==chain_source(flip):
            return 14
        if include_new:
            if w==r3_source(flip):
                return 10
            if w==r3_source(2+flip):
                return 11
    return 0


def has_registered_exit(w: BoundaryLabel,include_new: Bool=False) raises -> Bool:
    var route=star_interface(w,include_new)
    return route!=0 and route!=7 # no uniform T2 exit is registered here


def _inflated(kind: Int,n: QX,d: QX,k: QX) raises -> List[QX]:
    _=r3_source(kind)
    var out: List[QX]=[qx_const(1),qx_const(-1),d.copy()]
    if kind//2==1:
        out=[qx_const(0),qx_const(-2),qx_sub(n,k)]
    if kind%2==1:
        for z in range(3):
            out[z]=qx_neg(out[z])
    return out^


def _transition(n: QX,d: QX,k: QX,kind: Int,tk: Int,i: QX,bk: Int,j: QX,target: BoundaryLabel) raises:
    var w=r3_source(kind)
    if _child(w.top,tk)!=target.top or _child(w.bottom,bk)!=target.bottom:
        raise Error("R3/D3 symbolic actual types refused")
    var pt=_prefix(w.top,tk,i,-1,n,d)
    var pb=_prefix(w.bottom,bk,j,-1,n,d)
    var base=_inflated(kind,n,d,k)
    var got=List[QX]()
    for z in range(3):
        got.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
    _equal3(got,_offset(target))


def certify_r3_children(corrupt: Bool=False) raises:
    certify_q3_children()
    certify_p_children() # selected P0/P1 exits, including k=0 cone
    certify_tm_children() # full T1/T2 stars, not a T2 exit claim
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var k=p[2].copy()
    var t=p[3].copy()
    var A=qx_add(n,d)
    var N=qx_sub(n,qx_const(1))
    _cone_positive(qx_sub(d,qx_const(2)))
    _cone_positive(qx_sub(n,qx_const(2)))
    _cone_positive(qx_sub(A,qx_add(t,qx_const(1))))
    _cone_positive(qx_sub(A,qx_add(qx_add(n,t),qx_const(2))))
    var beta=_linear(qx_const(0),qx_const(1))
    var beta2=tp_mul(beta,beta)
    var f=_cubic(-1,n,d)
    var ba=tp_sub(tp_sub(beta2,tp_scale(beta,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    for kind in range(4):
        var w=r3_source(kind)
        var base=_inflated(kind,n,d,k)
        var field=tp_add(tp_add(tp_scale(ba,qx_const(w.x)),tp_scale(bb,qx_const(w.c))),tp_scale(beta,qx_const(w.y)))
        var image=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(beta,base[2]))
        if corrupt:
            image=tp_add(image,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(tp_mul(beta,field),f),tp_mod_monic(image,f))
        var betaG=tp_add(beta2,_linear(qx_const(-2),qx_sub(qx_sub(d,n),qx_const(1))))
        if kind//2==1:
            betaG=_linear(qx_const(-2),qx_add(t,qx_const(1)))
        if kind%2==1:
            betaG=tp_scale(betaG,qx_const(-1))
        _equal(tp_mod_monic(image,f),tp_mod_monic(betaG,f))
        var R=A.copy() if kind%2==0 else (N.copy() if kind//2==0 else n.copy())
        var B=A.copy() if kind%2==1 else (N.copy() if kind//2==0 else n.copy())
        for ri in [1,2]:
            for rj in [1,2]:
                var top: List[QX]=[qx_const(0),qx_const(ri),qx_add(R,qx_const(1))]
                var bottom: List[QX]=[qx_const(0),qx_const(rj),qx_add(B,qx_const(1))]
                for tk in range(3):
                    for bk in range(3):
                        var ct=_child(w.top,tk)
                        var cb=_child(w.bottom,bk)
                        var got=symbolic_child(-1,w.top,w.bottom,_offset(w),tk,top[tk],bk,bottom[bk],ct,cb)
                        var pt=_prefix(w.top,tk,top[tk],-1,n,d)
                        var pb=_prefix(w.bottom,bk,bottom[bk],-1,n,d)
                        var want=List[QX]()
                        for z in range(3):
                            want.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
                        _equal3(got,want)
    # Uniform X ancestry and genuine R3 LAST/LAST escape to D3.
    for flip in range(2):
        var xs=q3_target(flip)
        var source=r3_source(flip)
        var ai=qx_add(A,qx_const(1)) if flip==0 else n.copy()
        var aj=n.copy() if flip==0 else qx_add(A,qx_const(1))
        _equal3(symbolic_child(-1,xs.top,xs.bottom,_offset(xs),LAST if flip==0 else RUN,ai,RUN if flip==0 else LAST,aj,source.top,source.bottom),_offset(source))
        _transition(n,d,k,flip,LAST,qx_add(A if flip==0 else N,qx_const(1)),LAST,qx_add(N if flip==0 else A,qx_const(1)),r3_source(2+flip))
        # R3(d,0)->T followed by its existing (1,2)->C.
        _transition(n,d,k,flip,RUN if flip==0 else FIRST,d.copy() if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else d.copy(),p3_source(2+flip))
        # D3(t+1,1)->P0 and inherited P0 exit.
        _transition(n,d,k,2+flip,RUN,qx_add(t,qx_const(1)) if flip==0 else qx_const(1),RUN,qx_const(1) if flip==0 else qx_add(t,qx_const(1)),p_source(flip))
    # Representatives of both full affine RUN/RUN diagonals, with actual
    # indices legal even at the smallest chamber member.
    for m in [1,2]:
        _transition(n,d,k,0,RUN,qx_add(d,qx_const(m+1)),RUN,qx_const(1),BoundaryLabel(2,2,1,-1,-m))
    _transition(n,d,k,0,LAST,qx_add(A,qx_const(1)),RUN,N,BoundaryLabel(0,2,1,-1,-2))
    _transition(n,d,k,0,RUN,qx_add(d,qx_const(1)),FIRST,qx_const(0),BoundaryLabel(2,0,0,-1,0))
    _transition(n,d,k,2,RUN,qx_add(t,qx_const(1)),RUN,qx_const(2),p_source(2))
    for r in [2,3,4]:
        _transition(n,d,k,2,RUN,qx_sub(qx_add(qx_add(n,t),qx_const(4)),qx_const(r)),LAST,qx_add(n,qx_const(1)),BoundaryLabel(2,0,-1,-1,r))
    # D3's t=0/1 first/first endpoints and sole first/run edge.
    for tt in [0,1]:
        var ns=qx_add(k,qx_const(3+tt))
        var ds=qx_add(k,qx_const(5+2*tt))
        _transition(ns,ds,k,2,FIRST,qx_const(0),FIRST,qx_const(0),BoundaryLabel(0,1,0,-2,3+tt))
        if tt==0:
            _transition(ns,ds,k,2,FIRST,qx_const(0),RUN,qx_const(1),chain_source(0))
    # RF(t,0) exists only at t>=1; RF(t-1,0) only at t>=2.
    for dt in [1,2]:
        var ns=qx_add(n,qx_const(dt))
        var ds=qx_add(d,qx_const(2*dt))
        _transition(ns,ds,k,2,RUN,qx_add(t,qx_const(1)),FIRST,qx_const(0),BoundaryLabel(2,1,-1,-2,3+dt))
    # P3 ancestry requires n>=4: union of shifted k or t cones.
    for dk in [0,1]:
        var ns=qx_add(n,qx_const(1))
        var ds=qx_add(d,qx_const(2-dk))
        var As=qx_add(ns,ds)
        var parent=p3_source(0)
        var pt=_prefix(0,LAST,qx_add(As,qx_const(1)),-1,ns,ds)
        var pb=_prefix(2,RUN,qx_sub(ns,qx_const(3)),-1,ns,ds)
        var want=List[QX]()
        var base: List[QX]=[qx_const(1),qx_const(-1),qx_add(ds,qx_const(4))]
        for z in range(3):
            want.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
        _equal3(want,_offset(r3_source(0)))
    print("CLASS_A_BOUNDARY_R3 four_complete_oriented_stars=true", "R3_count=2n+3", "D3_count=2n+4_at_t0_else_2n+5", "R3_exit_at_most_two=true", "D3_exit_at_most_six=true", "candidate39_not_closed=true", "candidate41_not_closed=true", "all_direct_child_productivity_proved=false", "BH=false")


def _dimensions(kind: Int,k: Int,t: Int) raises -> Tuple[Int,Int,Int,Int]:
    _=r3_source(kind)
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,8)
    return(p[0],p[1],A,p[0]-1)


def r3_child_allowed(kind: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    var p=_dimensions(kind,k,t)
    var run=p[3] if kind//2==0 else p[0]
    var R=p[2] if kind%2==0 else run
    var B=run if kind%2==0 else p[2]
    if i<0 or i>R+1 or j<0 or j>B+1:
        raise Error("nonexistent R3/D3 occurrence")
    var a=j if kind%2==1 else i
    var b=i if kind%2==1 else j
    var n=p[0]
    var d=p[1]
    var A=p[2]
    if kind//2==0:
        if a>=1 and a<=A:
            return a>=d-1 and a<=d+2 if b==0 else b>=1 and b<=n-1 and (a-b==d+1 or a-b==d+2)
        return a==A+1 and (b==n-1 or b==n)
    if a==0:
        return t<=1 if b==0 else t==0 and b==1
    if a>=1 and a<=A:
        if b==0:
            return a>=t-1 and a<=t
        if b<=n:
            return a-b==t-1 or a-b==t
        return a>=n+t and a<=n+t+2
    return False


def r3_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for r in range(-1,3):
        base.append(BoundaryLabel(2,0,0,-1,r))
    for r in [-2,-1]:
        base.append(BoundaryLabel(2,2,1,-1,r))
    base.append(BoundaryLabel(0,2,1,-1,-2))
    base.append(r3_source(2))
    for r in [3,4]:
        base.append(BoundaryLabel(0,1,0,-2,r))
        base.append(BoundaryLabel(2,2,-1,-1,r))
    base.append(BoundaryLabel(0,2,0,-1,3))
    for r in [4,5]:
        base.append(BoundaryLabel(2,1,-1,-2,r))
    for r in [2,3,4]:
        base.append(BoundaryLabel(2,0,-1,-1,r))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def in_r3_image(w: BoundaryLabel) raises -> Bool:
    var z=w if w.c<0 else reverse_label(w)
    if z.c==-1:
        if z==r3_source(2) or z==BoundaryLabel(0,2,1,-1,-2) or z==BoundaryLabel(0,2,0,-1,3):
            return True
        if z.top==2 and z.bottom==0:
            return (z.x==0 and z.y>=-1 and z.y<=2) or(z.x==-1 and z.y>=2 and z.y<=4)
        return z.top==2 and z.bottom==2 and ((z.x==1 and z.y>=-2 and z.y<=-1) or(z.x==-1 and z.y>=3 and z.y<=4))
    if z.c==-2:
        return (z.top==0 and z.bottom==1 and z.x==0 and z.y>=3 and z.y<=4) or(z.top==2 and z.bottom==1 and z.x==-1 and z.y>=4 and z.y<=5)
    return False


def _append(mut out: List[BoundaryEdge],kind: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(kind,k,t)
    var a=j if kind%2==1 else i
    var b=i if kind%2==1 else j
    if not r3_child_allowed(kind,k,t,a,b):
        raise Error("synthesized R3/D3 guard failed")
    var target=member_transport(-1,k,p[0],p[1],r3_source(kind),a,b)
    if not in_r3_image(target):
        raise Error("R3/D3 target escaped exact image")
    out.append(BoundaryEdge(a,b,target))


def r3_child_star(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var d=p[1]
    var A=p[2]
    var out=List[BoundaryEdge]()
    if kind//2==0:
        for i in range(d-1,d+3):
            _append(out,kind,k,t,i,0)
        for delta in [d+1,d+2]:
            for j in range(1,min(n-1,A-delta)+1):
                _append(out,kind,k,t,j+delta,j)
        _append(out,kind,k,t,A+1,n-1)
        _append(out,kind,k,t,A+1,n)
    else:
        if t<=1:
            _append(out,kind,k,t,0,0)
        if t==0:
            _append(out,kind,k,t,0,1)
        for i in range(max(1,t-1),t+1):
            _append(out,kind,k,t,i,0)
        for delta in [t-1,t]:
            for j in range(max(1,1-delta),n+1):
                _append(out,kind,k,t,j+delta,j)
        for i in range(n+t,n+t+3):
            _append(out,kind,k,t,i,n+1)
    return out^


def verify_r3_packet(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not r3_child_allowed(kind,k,t,edge.i,edge.j) or not in_r3_image(edge.target):
        raise Error("R3/D3 packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],r3_source(kind),edge.i,edge.j,edge.target)


def r3_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var flip=kind%2
    var out=List[BoundaryEdge]()
    if kind//2==0:
        out.append(BoundaryEdge(0 if flip==1 else p[1],p[1] if flip==1 else 0,p3_source(2+flip)))
        out.append(BoundaryEdge(2 if flip==1 else 1,1 if flip==1 else 2,BoundaryLabel(2,2,0,0,0)))
    else:
        out.append(BoundaryEdge(1 if flip==1 else t+1,t+1 if flip==1 else 1,p_source(flip)))
        var suffix=p_path(flip,k,t)
        for edge in suffix:
            out.append(edge)
    return out^


def verify_r3_path(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    var want=r3_path(kind,k,t)
    if len(steps)!=len(want):
        raise Error("incomplete R3/D3 path")
    var w=r3_source(kind)
    for z in range(len(steps)):
        var edge=steps[z]
        if edge.i!=want[z].i or edge.j!=want[z].j or edge.target!=want[z].target:
            raise Error("R3/D3 intended typed intermediate or index mismatch")
        verify_member_edge(tables,-1,k,p[0],p[1],w,edge.i,edge.j,edge.target)
        w=edge.target
    if w!=BoundaryLabel(2,2,0,0,0):
        raise Error("R3/D3 terminal is not typed coincidence")
