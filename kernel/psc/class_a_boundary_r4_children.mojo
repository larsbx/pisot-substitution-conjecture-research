"""R4 complete stars and <=4-edge exits; five companions have selected exits.

Universal guards and the n=3 companion exception: docs/class-a-boundary-r4-carrier-2026-10-28.md.
"""
from finite_exact.checked_int import checked_add, checked_mul
from std.collections import Dict
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_r3_children import r3_source
from psc.class_a_boundary_b4_children import certify_b4_children, b4_star_interface, b4_exit_interface
from psc.class_a_boundary_p3_children import p3_source
from psc.class_a_boundary_p_children import p_source, p_path
from psc.class_a_boundary_h3_children import chain_source, chain_path
from psc.class_a_boundary_e_children import _offset
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, _child, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _cone_positive, _cone_nonnegative
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_mul, qx_neg, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def r4_source(kind: Int) raises -> BoundaryLabel:
    # Only 0/1 has complete stars. Other kinds have uniform selected exits.
    if kind<0 or kind>=12:
        raise Error("unknown R4/companion orientation")
    var w=BoundaryLabel(0,2,1,-1,-2)
    if kind//2==1:
        w=BoundaryLabel(0,1,0,-3,3) # E4
    elif kind//2==2:
        w=BoundaryLabel(0,2,0,-3,3) # D4
    elif kind//2==3:
        w=BoundaryLabel(0,2,1,0,-1) # Y4
    elif kind//2==4:
        w=BoundaryLabel(0,1,0,-3,4) # E5
    elif kind//2==5:
        w=BoundaryLabel(0,2,0,-3,5) # G5
    return reverse_label(w) if kind%2==1 else w


def r4_star_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=b4_star_interface(w,True)
    if old!=0:
        return old
    for flip in range(2):
        if w==chain_source(6+flip):
            return 22 # existing complete L star, now bound for image coverage
        if include_new and w==r4_source(flip):
            return 23
    return 0


def r4_exit_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=b4_exit_interface(w,True)
    if old!=0:
        return old
    var star=r4_star_interface(w,include_new)
    if star!=0 and star!=7:
        return star
    if include_new:
        for group in range(1,6):
            for flip in range(2):
                if w==r4_source(2*group+flip):
                    return 23+group
    return 0


def _image(w: BoundaryLabel,n: QX,d: QX) raises -> List[QX]:
    var A=qx_add(n,d)
    var N=qx_sub(n,qx_const(1))
    return [qx_const(checked_add(checked_add(checked_mul(2,w.x),w.c),w.y)),qx_const(checked_add(w.c,w.y)),
            qx_add(qx_add(qx_mul(qx_const(w.x),A),qx_mul(qx_const(w.c),n)),qx_mul(qx_const(w.y),N))]


def _expected_image(kind: Int,n: QX,d: QX,k: QX,t: QX) raises -> List[QX]:
    _=r4_source(kind)
    var out: List[QX]=[qx_const(-1),qx_const(-3),qx_sub(qx_const(1),k)]
    if kind//2==1 or kind//2==2:
        out=[qx_const(0),qx_const(0),qx_const(-3)]
    elif kind//2==3:
        out=[qx_const(1),qx_const(-1),qx_add(d,qx_const(1))]
    elif kind//2==4:
        out=[qx_const(1),qx_const(1),qx_sub(n,qx_const(4))]
    elif kind//2==5:
        out=[qx_const(2),qx_const(2),qx_sub(qx_add(n,n),qx_const(5))]
    if kind%2==1:
        for z in range(3):
            out[z]=qx_neg(out[z])
    return out^


def _transition(n: QX,d: QX,w: BoundaryLabel,tk: Int,i: QX,bk: Int,j: QX,target: BoundaryLabel) raises:
    if _child(w.top,tk)!=target.top or _child(w.bottom,bk)!=target.bottom:
        raise Error("R4 symbolic actual types refused")
    var pt=_prefix(w.top,tk,i,-1,n,d)
    var pb=_prefix(w.bottom,bk,j,-1,n,d)
    var base=_image(w,n,d)
    var got=List[QX]()
    for z in range(3):
        got.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
    _equal3(got,_offset(target))


def certify_r4_children(corrupt: Bool=False) raises:
    certify_b4_children() # includes exact 0<alpha+2h<1 and every reused suffix
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var k=p[2].copy()
    var t=p[3].copy()
    var A=qx_add(n,d)
    var N=qx_sub(n,qx_const(1))
    _cone_positive(qx_sub(n,qx_const(2)))
    _cone_positive(qx_sub(A,qx_add(d,qx_const(1))))
    _cone_nonnegative(qx_sub(A,qx_add(n,n)))
    var beta=_linear(qx_const(0),qx_const(1))
    var beta2=tp_mul(beta,beta)
    var f=_cubic(-1,n,d)
    var ba=tp_sub(tp_sub(beta2,tp_scale(beta,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    for kind in range(12):
        var w=r4_source(kind)
        var base=_image(w,n,d)
        _equal3(base,_expected_image(kind,n,d,k,t))
        var field=tp_add(tp_add(tp_scale(ba,qx_const(w.x)),tp_scale(bb,qx_const(w.c))),tp_scale(beta,qx_const(w.y)))
        var image=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(beta,base[2]))
        if corrupt:
            image=tp_add(image,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(tp_mul(beta,field),f),tp_mod_monic(image,f))
        if kind//2==0:
            var betaG=tp_add(tp_scale(beta2,qx_const(-1)),_linear(qx_const(-2),qx_sub(qx_sub(n,k),qx_const(2))))
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
        var parent=r3_source(flip)
        var w=r4_source(flip)
        _equal3(symbolic_child(-1,parent.top,parent.bottom,_offset(parent),LAST if flip==0 else RUN,qx_add(A,qx_const(1)) if flip==0 else N.copy(),RUN if flip==0 else LAST,N.copy() if flip==0 else qx_add(A,qx_const(1)),w.top,w.bottom),_offset(w))
        # E4 -> R(T); Y4 -> T; E5 -> B2h; G5 -> J, all uniform.
        _transition(n,d,r4_source(2+flip),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_const(3),RUN if flip==0 else FIRST,qx_const(3) if flip==0 else qx_const(0),p3_source(3-flip))
        _transition(n,d,r4_source(6+flip),RUN if flip==0 else FIRST,qx_add(d,qx_const(1)) if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_add(d,qx_const(1)),p3_source(2+flip))
        _transition(n,d,r4_source(8+flip),RUN,n.copy() if flip==0 else qx_const(1),RUN,qx_const(1) if flip==0 else n.copy(),p_source(6+flip))
        _transition(n,d,r4_source(10+flip),RUN if flip==0 else FIRST,qx_add(n,n) if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_add(n,n),chain_source(2+flip))
        # D4(0,3)->Y4 on the union of shifted cones n>=4.
        for dk in [0,1]:
            var ns=qx_add(n,qx_const(1))
            var ds=qx_add(d,qx_const(2-dk))
            _transition(ns,ds,r4_source(4+flip),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_const(3),RUN if flip==0 else FIRST,qx_const(3) if flip==0 else qx_const(0),r4_source(6+flip))
        # R4 first edges on t=0/1 faces and shifted t>=2 cone.
        for tt in [0,1,2]:
            var ns=qx_add(k,qx_const(3+tt)) if tt<2 else qx_add(n,qx_const(2))
            var ds=qx_add(k,qx_const(5+2*tt)) if tt<2 else qx_add(d,qx_const(4))
            var j=ns.copy() if tt==0 else qx_add(k,qx_const(3 if tt==1 else 4))
            var target=r4_source(2+flip) if tt==0 else (r4_source(4+flip) if tt==1 else chain_source(7-flip))
            _transition(ns,ds,w,FIRST if flip==0 else (LAST if tt==0 else RUN),qx_const(0) if flip==0 else j.copy(),LAST if tt==0 and flip==0 else (RUN if flip==0 else FIRST),j.copy() if flip==0 else qx_const(0),target)
    # The unique n=3 member uses two extra true typed transitions.
    var z=BoundaryLabel(0,2,1,0,-2)
    var xx=BoundaryLabel(0,0,0,-2,4)
    _transition(qx_const(3),qx_const(5),r4_source(4),FIRST,qx_const(0),RUN,qx_const(2),z)
    _transition(qx_const(3),qx_const(5),z,FIRST,qx_const(0),FIRST,qx_const(0),xx)
    _transition(n,d,xx,RUN,qx_add(qx_add(n,n),qx_const(1)),FIRST,qx_const(0),chain_source(2))
    print("CLASS_A_BOUNDARY_R4 two_complete_oriented_stars=true", "count=max(1,2t)", "union_labels=20", "R4_typed_exit_at_most_four=true", "five_companions_uniform_exits_only=true", "all_direct_children_productivity_proved_on_t_le_1=true", "all_t_all_child_productivity_proved=false", "global_BH=false")


def _dimensions(kind: Int,k: Int,t: Int) raises -> Tuple[Int,Int,Int,Int]:
    _=r4_source(kind)
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,12)
    return(p[0],p[1],A,p[0]-1)


def r4_child_allowed(kind: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    if kind<0 or kind>=2:
        raise Error("complete-star interface is only for R4 orientations")
    var p=_dimensions(kind,k,t)
    var R=p[2] if kind==0 else p[3]
    var B=p[3] if kind==0 else p[2]
    if i<0 or i>R+1 or j<0 or j>B+1:
        raise Error("nonexistent R4 occurrence")
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    var n=p[0]
    var A=p[2]
    if a==0:
        return t<=2 if b==n else b>=k+3 and b<=k+5
    if a<=A:
        if b==n:
            return a>=max(1,t-2) and a<=t-1
        return b>=1 and b<=n-1 and (b-a==k+4 or b-a==k+5)
    return False


def r4_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for r in [3,4,5]:
        base.append(BoundaryLabel(0,2,0,-3,r))
        base.append(BoundaryLabel(0,1,0,-3,r))
    for r in [5,6]:
        base.append(BoundaryLabel(2,2,-1,-3,r))
        base.append(BoundaryLabel(2,1,-1,-3,r))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def in_r4_image(w: BoundaryLabel) raises -> Bool:
    var z=w if w.c<0 else reverse_label(w)
    if z.c!=-3:
        return False
    if z.x==0 and z.top==0 and (z.bottom==1 or z.bottom==2):
        return z.y>=3 and z.y<=5
    return z.x==-1 and z.top==2 and (z.bottom==1 or z.bottom==2) and (z.y==5 or z.y==6)


def _append(mut out: List[BoundaryEdge],kind: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(kind,k,t)
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if not r4_child_allowed(kind,k,t,a,b):
        raise Error("synthesized R4 guard failed")
    var target=member_transport(-1,k,p[0],p[1],r4_source(kind),a,b)
    if not in_r4_image(target):
        raise Error("R4 target escaped exact image")
    out.append(BoundaryEdge(a,b,target))


def r4_child_star(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    if kind<0 or kind>=2:
        raise Error("companions have no complete-star certificate here")
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var out=List[BoundaryEdge]()
    for j in range(k+3,min(n-1,k+5)+1):
        _append(out,kind,k,t,0,j)
    if t<=2:
        _append(out,kind,k,t,0,n)
    for delta in [k+4,k+5]:
        for i in range(1,max(0,n-1-delta)+1):
            _append(out,kind,k,t,i,i+delta)
    for i in range(max(1,t-2),t):
        _append(out,kind,k,t,i,n)
    return out^


def verify_r4_packet(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not r4_child_allowed(kind,k,t,edge.i,edge.j) or not in_r4_image(edge.target):
        raise Error("R4 packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],r4_source(kind),edge.i,edge.j,edge.target)


def verify_r4_star(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edges: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    if kind>=2 or len(edges)!=max(1,2*t):
        raise Error("incomplete R4 indexed star or unsupported companion star")
    var stride=checked_add(p[3] if kind==0 else p[2],2)
    var seen=Dict[Int,Bool]()
    for edge in edges:
        verify_r4_packet(tables,kind,k,t,edge)
        var key=checked_add(checked_mul(edge.i,stride),edge.j)
        if key in seen:
            raise Error("duplicate R4 occurrence")
        seen[key]=True


def r4_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var d=p[1]
    var out=List[BoundaryEdge]()
    if kind//2==0:
        if t==0:
            out.append(BoundaryEdge(0,n,r4_source(2)))
            var suffix=r4_path(2,k,t)
            for edge in suffix:
                out.append(edge)
        elif t==1:
            out.append(BoundaryEdge(0,k+3,r4_source(4)))
            var suffix=r4_path(4,k,t)
            for edge in suffix:
                out.append(edge)
        else:
            out.append(BoundaryEdge(0,k+4,chain_source(7)))
            var suffix=chain_path(7,k,t)
            for edge in suffix:
                out.append(edge)
    elif kind//2==1:
        out.append(BoundaryEdge(0,3,p3_source(3)))
        out.append(BoundaryEdge(2,1,BoundaryLabel(2,2,0,0,0)))
    elif kind//2==2:
        if n==3:
            out.append(BoundaryEdge(0,2,BoundaryLabel(0,2,1,0,-2)))
            out.append(BoundaryEdge(0,0,BoundaryLabel(0,0,0,-2,4)))
            out.append(BoundaryEdge(2*n+1,0,chain_source(2)))
            var suffix=chain_path(2,k,t)
            for edge in suffix:
                out.append(edge)
        else:
            out.append(BoundaryEdge(0,3,r4_source(6)))
            var suffix=r4_path(6,k,t)
            for edge in suffix:
                out.append(edge)
    elif kind//2==3:
        out.append(BoundaryEdge(d+1,0,p3_source(2)))
        out.append(BoundaryEdge(1,2,BoundaryLabel(2,2,0,0,0)))
    elif kind//2==4:
        out.append(BoundaryEdge(n,1,p_source(6)))
        var suffix=p_path(6,k,t)
        for edge in suffix:
            out.append(edge)
    else:
        out.append(BoundaryEdge(2*n,0,chain_source(2)))
        var suffix=chain_path(2,k,t)
        for edge in suffix:
            out.append(edge)
    if kind%2==1:
        for z in range(len(out)):
            var edge=out[z]
            out[z]=BoundaryEdge(edge.j,edge.i,reverse_label(edge.target))
    return out^


def verify_r4_path(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    var want=r4_path(kind,k,t)
    if len(steps)!=len(want):
        raise Error("incomplete R4/companion path")
    var w=r4_source(kind)
    for z in range(len(steps)):
        var edge=steps[z]
        if edge.i!=want[z].i or edge.j!=want[z].j or edge.target!=want[z].target:
            raise Error("R4 intended typed intermediate or index mismatch")
        verify_member_edge(tables,-1,k,p[0],p[1],w,edge.i,edge.j,edge.target)
        w=edge.target
    if w!=BoundaryLabel(2,2,0,0,0):
        raise Error("R4 terminal is not typed coincidence")
