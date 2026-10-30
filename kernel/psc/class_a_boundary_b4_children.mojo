"""B4 complete stars and <=5-edge typed exits; two companions have exits only.

Exact guards and scope: docs/class-a-boundary-b4-carrier-2026-10-28.md.
"""
from finite_exact.checked_int import checked_add, checked_mul
from std.collections import Dict
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_r3_children import r3_source
from psc.class_a_boundary_b3_children import certify_b3_children, b3_star_interface
from psc.class_a_boundary_p3_children import p3_source
from psc.class_a_boundary_e2_children import certify_e2_children, e2_source, e2_path
from psc.class_a_boundary_h3_children import alpha_high, chain_source, chain_path
from psc.class_a_boundary_e_children import _offset
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, _child, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _cone_positive, _cone_nonnegative
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def b4_source(kind: Int) raises -> BoundaryLabel:
    # B4 0/1 has full stars. D0 2/3 and F4 4/5 have selected exits only.
    if kind<0 or kind>=6:
        raise Error("unknown B4/companion orientation")
    var w=BoundaryLabel(2,0,0,-1,-1)
    if kind//2==1:
        w=BoundaryLabel(0,0,-1,-2,3)
    elif kind//2==2:
        w=BoundaryLabel(0,2,-1,-2,4)
    return reverse_label(w) if kind%2==1 else w


def b4_star_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=b3_star_interface(w,True)
    if old!=0:
        return old
    for flip in range(2):
        if w==e2_source(2+flip):
            return 18 # previously classified Dxx, now bound for B4 image coverage
        if include_new and w==b4_source(flip):
            return 19
    return 0


def b4_exit_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var star=b4_star_interface(w,include_new)
    if star!=0 and star!=7:
        return star
    if include_new:
        for flip in range(2):
            if w==b4_source(2+flip):
                return 20 # uniform exit, no complete-star interface
            if w==b4_source(4+flip):
                return 21 # uniform exit, no complete-star interface
    return 0


def _inflated(kind: Int,n: QX,d: QX,t: QX) raises -> List[QX]:
    _=b4_source(kind)
    var out: List[QX]=[qx_const(-2),qx_const(-2),qx_sub(qx_const(1),qx_add(n,n))]
    if kind//2==1:
        out=[qx_const(-1),qx_const(1),qx_neg(qx_add(d,qx_const(3)))]
    elif kind//2==2:
        out=[qx_const(0),qx_const(2),qx_neg(qx_add(t,qx_const(6)))]
    if kind%2==1:
        for z in range(3):
            out[z]=qx_neg(out[z])
    return out^


def _transition(n: QX,d: QX,t: QX,kind: Int,tk: Int,i: QX,bk: Int,j: QX,target: BoundaryLabel) raises:
    var w=b4_source(kind)
    if _child(w.top,tk)!=target.top or _child(w.bottom,bk)!=target.bottom:
        raise Error("B4 symbolic actual types refused")
    var pt=_prefix(w.top,tk,i,-1,n,d)
    var pb=_prefix(w.bottom,bk,j,-1,n,d)
    var base=_inflated(kind,n,d,t)
    var got=List[QX]()
    for z in range(3):
        got.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
    _equal3(got,_offset(target))


def certify_b4_children(corrupt: Bool=False) raises:
    certify_b3_children()
    certify_e2_children() # exact half separator and existing Dxx/K suffixes
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var k=p[2].copy()
    var t=p[3].copy()
    var A=qx_add(n,d)
    var N=qx_sub(n,qx_const(1))
    _cone_positive(qx_sub(n,qx_const(2)))
    _cone_nonnegative(qx_sub(A,qx_add(d,qx_const(3)))) # D0's actual bottom RUN
    _cone_nonnegative(qx_sub(N,qx_add(t,qx_const(2)))) # F4's actual bottom RUN
    var beta=_linear(qx_const(0),qx_const(1))
    var beta2=tp_mul(beta,beta)
    var f=_cubic(-1,n,d)
    var ba=tp_sub(tp_sub(beta2,tp_scale(beta,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    for kind in range(6):
        var w=b4_source(kind)
        var base=_inflated(kind,n,d,t)
        var field=tp_add(tp_add(tp_scale(ba,qx_const(w.x)),tp_scale(bb,qx_const(w.c))),tp_scale(beta,qx_const(w.y)))
        var image=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(beta,base[2]))
        if corrupt:
            image=tp_add(image,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(tp_mul(beta,field),f),tp_mod_monic(image,f))
        if kind//2==0:
            var betaG=tp_add(tp_scale(beta2,qx_const(-2)),tp_scale(beta,qx_const(-1)))
            if kind%2==1:
                betaG=tp_scale(betaG,qx_const(-1))
            _equal(tp_mod_monic(image,f),betaG)
            var R=N.copy() if kind==0 else A.copy()
            var B=A.copy() if kind==0 else N.copy()
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
        var w=b4_source(flip)
        _equal3(symbolic_child(-1,parent.top,parent.bottom,_offset(parent),RUN if flip==0 else FIRST,qx_add(d,qx_const(2)) if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_add(d,qx_const(2)),w.top,w.bottom),_offset(w))
        # Uniform selected exits for D0 and F4, without complete-star claims.
        _transition(n,d,t,2+flip,FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_add(d,qx_const(3)),RUN if flip==0 else FIRST,qx_add(d,qx_const(3)) if flip==0 else qx_const(0),p3_source(3-flip))
        _transition(n,d,t,4+flip,FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_add(t,qx_const(2)),RUN if flip==0 else FIRST,qx_add(t,qx_const(2)) if flip==0 else qx_const(0),chain_source(5-flip))
        # B4 first edges: separate t=0/1 faces, and shifted t>=2 cone.
        for tt in [0,1,2]:
            var ns=qx_add(k,qx_const(3+tt)) if tt<2 else qx_add(n,qx_const(2))
            var ds=qx_add(k,qx_const(5+2*tt)) if tt<2 else qx_add(d,qx_const(4))
            var ts=qx_const(tt) if tt<2 else qx_add(t,qx_const(2))
            var As=qx_add(ns,ds)
            var j=qx_add(As,qx_const(1)) if tt<2 else qx_add(qx_add(ns,ns),qx_const(4))
            var target=b4_source(2+flip) if tt==0 else (e2_source(3-flip) if tt==1 else b4_source(4+flip))
            _transition(ns,ds,ts,flip,FIRST if flip==0 else (LAST if tt<2 else RUN),qx_const(0) if flip==0 else j.copy(),LAST if tt<2 and flip==0 else (RUN if flip==0 else FIRST),j.copy() if flip==0 else qx_const(0),target)
    print("CLASS_A_BOUNDARY_B4 two_complete_oriented_stars=true", "count=max(1,2t-1)", "union_labels=32", "typed_exit_at_most_five=true", "D0_F4_uniform_exits_only=true", "all_direct_children_productivity_proved_on_t_le_1=true", "all_t_all_child_productivity_proved=false", "global_BH=false")


def _dimensions(kind: Int,k: Int,t: Int) raises -> Tuple[Int,Int,Int,Int]:
    _=b4_source(kind)
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,12)
    return(p[0],p[1],A,p[0]-1)


def b4_child_allowed(kind: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    if kind<0 or kind>=2:
        raise Error("complete-star interface is only for B4 orientations")
    var p=_dimensions(kind,k,t)
    var R=p[3] if kind==0 else p[2]
    var B=p[2] if kind==0 else p[3]
    if i<0 or i>R+1 or j<0 or j>B+1:
        raise Error("nonexistent B4 occurrence")
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    var n=p[0]
    var A=p[2]
    var high=1 if alpha_high(k,t) else 0
    if a==0:
        if b==A+1:
            return t<=3+high
        return b>=2*n+4 and b<=2*n+6+high
    if a<=n-1:
        if b==A+1:
            return a>=max(1,t-3-high) and a<=t-1
        return b>=1 and b<=A and (b-a==2*n+5+high or b-a==2*n+6+high)
    return False


def b4_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for r in range(4,8):
        base.append(BoundaryLabel(0,2,-1,-2,r))
    for r in range(3,8):
        base.append(BoundaryLabel(0,0,-1,-2,r))
    for r in range(6,9):
        base.append(BoundaryLabel(2,2,-2,-2,r))
    for r in range(5,9):
        base.append(BoundaryLabel(2,0,-2,-2,r))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def in_b4_image(w: BoundaryLabel) raises -> Bool:
    var z=w if w.c<0 else reverse_label(w)
    if z.c!=-2:
        return False
    if z.x==-1 and z.top==0:
        return (z.bottom==2 and z.y>=4 and z.y<=7) or (z.bottom==0 and z.y>=3 and z.y<=7)
    if z.x==-2 and z.top==2:
        return (z.bottom==2 and z.y>=6 and z.y<=8) or (z.bottom==0 and z.y>=5 and z.y<=8)
    return False


def _append(mut out: List[BoundaryEdge],kind: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(kind,k,t)
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if not b4_child_allowed(kind,k,t,a,b):
        raise Error("synthesized B4 guard failed")
    var target=member_transport(-1,k,p[0],p[1],b4_source(kind),a,b)
    if not in_b4_image(target):
        raise Error("B4 target escaped exact image")
    out.append(BoundaryEdge(a,b,target))


def b4_child_star(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    if kind<0 or kind>=2:
        raise Error("companions have no complete-star certificate here")
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var A=p[2]
    var high=1 if alpha_high(k,t) else 0
    var out=List[BoundaryEdge]()
    for j in range(2*n+4,min(A,2*n+6+high)+1):
        _append(out,kind,k,t,0,j)
    if t<=3+high:
        _append(out,kind,k,t,0,A+1)
    for delta in [2*n+5+high,2*n+6+high]:
        for i in range(1,max(0,A-delta)+1):
            _append(out,kind,k,t,i,i+delta)
    for i in range(max(1,t-3-high),t):
        _append(out,kind,k,t,i,A+1)
    return out^


def verify_b4_packet(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not b4_child_allowed(kind,k,t,edge.i,edge.j) or not in_b4_image(edge.target):
        raise Error("B4 packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],b4_source(kind),edge.i,edge.j,edge.target)


def verify_b4_star(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edges: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    if kind>=2 or len(edges)!=max(1,2*t-1):
        raise Error("incomplete B4 indexed star or unsupported companion star")
    var stride=checked_add(p[2] if kind==0 else p[3],2)
    var seen=Dict[Int,Bool]()
    for edge in edges:
        verify_b4_packet(tables,kind,k,t,edge)
        var key=checked_add(checked_mul(edge.i,stride),edge.j)
        if key in seen:
            raise Error("duplicate B4 occurrence")
        seen[key]=True


def b4_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var d=p[1]
    var A=p[2]
    var out=List[BoundaryEdge]()
    if kind//2==0:
        if t==0:
            out.append(BoundaryEdge(0,A+1,b4_source(2)))
            var suffix=b4_path(2,k,t)
            for edge in suffix:
                out.append(edge)
        elif t==1:
            out.append(BoundaryEdge(0,A+1,e2_source(3)))
            var suffix=e2_path(3,k,t)
            for edge in suffix:
                out.append(edge)
        else:
            out.append(BoundaryEdge(0,2*n+4,b4_source(4)))
            var suffix=b4_path(4,k,t)
            for edge in suffix:
                out.append(edge)
    elif kind//2==1:
        out.append(BoundaryEdge(0,d+3,p3_source(3)))
        out.append(BoundaryEdge(2,1,BoundaryLabel(2,2,0,0,0)))
    else:
        out.append(BoundaryEdge(0,t+2,chain_source(5)))
        var suffix=chain_path(5,k,t)
        for edge in suffix:
            out.append(edge)
    if kind%2==1:
        for z in range(len(out)):
            var edge=out[z]
            out[z]=BoundaryEdge(edge.j,edge.i,reverse_label(edge.target))
    return out^


def verify_b4_path(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    var want=b4_path(kind,k,t)
    if len(steps)!=len(want):
        raise Error("incomplete B4/companion path")
    var w=b4_source(kind)
    for z in range(len(steps)):
        var edge=steps[z]
        if edge.i!=want[z].i or edge.j!=want[z].j or edge.target!=want[z].target:
            raise Error("B4 intended typed intermediate or index mismatch")
        verify_member_edge(tables,-1,k,p[0],p[1],w,edge.i,edge.j,edge.target)
        w=edge.target
    if w!=BoundaryLabel(2,2,0,0,0):
        raise Error("B4 terminal is not typed coincidence")
