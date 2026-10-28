"""Eight F/Z/E3/G2 stars; every direct F child has a short typed tail."""
from finite_exact.checked_int import checked_add, checked_sub
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_h5_children import certify_h5_children
from psc.class_a_boundary_p_children import p_source, p_path
from psc.class_a_boundary_h3_children import chain_source, chain_path
from psc.class_a_boundary_e_children import eh_source, _offset
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _poly, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _cone_positive
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def f_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=8:
        raise Error("unknown oriented F-family packet")
    var group=kind//2
    var w=BoundaryLabel(0,2,1,-3,3)
    if group==1:
        w=BoundaryLabel(2,0,1,0,-2)
    elif group==2:
        w=BoundaryLabel(0,0,-1,0,3)
    elif group==3:
        w=BoundaryLabel(0,2,2,0,-3)
    return reverse_label(w) if kind%2==1 else w


def _inflated(kind: Int,n: QX,d: QX,k: QX,t: QX) -> List[QX]:
    var A=qx_add(n,d)
    var out: List[QX]=[qx_const(2),qx_const(0),qx_sub(A,qx_const(3))]
    if kind//2==1:
        out=[qx_const(0),qx_const(-2),qx_add(t,qx_const(4))]
    elif kind//2==2:
        out=[qx_const(1),qx_const(3),qx_sub(k,qx_const(2))]
    elif kind//2==3:
        out=[qx_const(1),qx_const(-3),qx_add(qx_sub(A,k),qx_const(2))]
    if kind%2==1:
        for z in range(3):
            out[z]=qx_neg(out[z])
    return out^


def certify_f_children(corrupt: Bool=False) raises:
    certify_h5_children() # includes eta t split, v<1, w<1 and h<alpha
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var k=p[2].copy()
    var t=p[3].copy()
    var A=qx_add(n,d)
    var N=qx_sub(n,qx_const(1))
    var X=_linear(qx_const(0),qx_const(1))
    var X2=tp_mul(X,X)
    var f=_cubic(-1,n,d)
    var ba=tp_sub(tp_sub(X2,tp_scale(X,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    for kind in range(8):
        var source=f_source(kind)
        var base=_inflated(kind,n,d,k,t)
        var field=tp_add(tp_add(tp_scale(ba,qx_const(source.x)),tp_scale(bb,qx_const(source.c))),tp_scale(X,qx_const(source.y)))
        var target=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(X,base[2]))
        if corrupt:
            target=tp_add(target,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(tp_mul(X,field),f),tp_mod_monic(target,f))
        var betaB=_poly(qx_const(-2),qx_sub(t,qx_const(1)),qx_const(2),qx_const(0))
        if kind//2==1:
            betaB=_linear(qx_const(-2),qx_add(t,qx_const(2)))
        elif kind//2==2:
            betaB=tp_add(X2,_linear(qx_const(2),qx_add(qx_sub(k,n),qx_const(1))))
        elif kind//2==3:
            betaB=tp_add(X2,_linear(qx_const(-4),qx_add(qx_add(t,t),qx_const(4))))
        if kind%2==1:
            betaB=tp_scale(betaB,qx_const(-1))
        _equal(tp_mod_monic(target,f),tp_mod_monic(betaB,f))
        var R=A.copy() if source.top==0 else N.copy()
        var B=A.copy() if source.bottom==0 else N.copy()
        for ri in [1,2]:
            for rj in [1,2]:
                var top: List[QX]=[qx_const(0),qx_const(ri),qx_add(R,qx_const(1))]
                var bottom: List[QX]=[qx_const(0),qx_const(rj),qx_add(B,qx_const(1))]
                for tk in range(3):
                    for bk in range(3):
                        var ct=2 if tk==RUN else (1 if tk==LAST and source.top==2 else 0)
                        var cb=2 if bk==RUN else (1 if bk==LAST and source.bottom==2 else 0)
                        var got=symbolic_child(-1,source.top,source.bottom,_offset(source),tk,top[tk],bk,bottom[bk],ct,cb)
                        var pt=_prefix(source.top,tk,top[tk],-1,n,d)
                        var pb=_prefix(source.bottom,bk,bottom[bk],-1,n,d)
                        var want=List[QX]()
                        for z in range(3):
                            want.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
                        _equal3(got,want)
        var i=qx_add(A,qx_const(1))
        var j=qx_const(1)
        var tk=LAST
        var bk=RUN
        var next=f_source(6)
        if kind//2==1:
            i=qx_add(t,qx_const(2))
            j=qx_const(1)
            tk=RUN
            bk=RUN
            next=p_source(7)
        elif kind//2==2:
            i=qx_add(k,qx_const(3))
            j=qx_const(0)
            tk=RUN
            bk=FIRST
            next=chain_source(6)
        elif kind//2==3:
            i=qx_sub(A,k)
            j=qx_const(0)
            tk=RUN
            bk=FIRST
            next=BoundaryLabel(2,0,0,-3,3)
        if kind%2==1:
            var old=i.copy()
            i=j.copy()
            j=old.copy()
            var old_kind=tk
            tk=bk
            bk=old_kind
            next=reverse_label(next)
        _equal3(symbolic_child(-1,source.top,source.bottom,_offset(source),tk,i,bk,j,next.top,next.bottom),_offset(next))
    _cone_positive(qx_sub(A,k))
    _cone_positive(qx_sub(A,qx_add(k,qx_const(4))))
    _cone_positive(qx_sub(N,k))
    # Conditional H5 LAST/RUN ancestry: shift k by +1, n,d by +1.
    var ns=qx_add(n,qx_const(1))
    var ds=qx_add(d,qx_const(1))
    var ks=qx_add(k,qx_const(1))
    var As=qx_add(ns,ds)
    var q=qx_add(qx_sub(As,ks),qx_const(2))
    var top=_prefix(0,LAST,qx_add(As,qx_const(1)),-1,ns,ds)
    var bottom=_prefix(2,RUN,ks,-1,ns,ds)
    var base: List[QX]=[qx_const(1),qx_const(-3),qx_add(q,qx_const(2))]
    var child=List[QX]()
    for z in range(3):
        child.append(qx_add(base[z],qx_sub(bottom[z],top[z])))
    _equal3(child,_offset(f_source(0)))
    for flip in range(2):
        var i=qx_add(A,qx_const(1)) if flip==0 else qx_add(k,qx_const(2))
        var j=qx_add(k,qx_const(2)) if flip==0 else qx_add(A,qx_const(1))
        var source=f_source(6+flip)
        var target=f_source(flip)
        _equal3(symbolic_child(-1,source.top,source.bottom,_offset(source),
                              LAST if flip==0 else RUN,i,RUN if flip==0 else LAST,j,
                              target.top,target.bottom),_offset(target))
    print("CLASS_A_BOUNDARY_F eight_complete_oriented_stars=true", "chamber_union_labels=64",
          "F_has_exactly_three_children=true", "each_direct_F_child_has_typed_tail_at_most_three=true",
          "global_closure=false", "BH=false")


def _dimensions(kind: Int,k: Int,t: Int) raises -> Tuple[Int,Int,Int,Int]:
    _=f_source(kind)
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,12)
    return(p[0],p[1],A,p[0]-1)


def f_child_allowed(kind: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    var p=_dimensions(kind,k,t)
    var w=f_source(kind)
    var R=p[2] if w.top==0 else p[3]
    var B=p[2] if w.bottom==0 else p[3]
    if i<0 or i>R+1 or j<0 or j>B+1:
        raise Error("nonexistent F-family occurrence")
    var a=j if kind%2==1 else i
    var b=i if kind%2==1 else j
    var A=p[2]
    var N=p[3]
    var group=kind//2
    if group==0:
        return (a==A and b==0) or(a==A+1 and (b==0 or b==1))
    if group==1:
        if a==0:
            return b==0 and t==0
        if a>=1 and a<=N:
            if b==0:
                return a>=max(1,t) and a<=t+2
            return b>=1 and b<=A and (a-b==t+1 or a-b==t+2)
        return a==p[0] and b>=k+1 and b<=k+2
    if group==2:
        if a>=1 and a<=A:
            if b==0:
                return a>=k+2 and a<=k+4
            return b>=1 and b<=A and (a-b==k+3 or a-b==k+4)
        return a==A+1 and b>=A-k-3 and b<=A-k-1
    var q=A-k
    var high=1 if t>=2 else 0
    if a>=1 and a<=A:
        if b==0:
            return a>=q-1 and a<=q+1+high
        return b>=1 and b<=N and (a-b==q+high or a-b==q+1+high)
    if a==A+1:
        return k==0 or(k==1 and high==1) if b==0 else b>=max(1,k-high) and b<=k+2
    return False


def f_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    base.append(f_source(2))
    base.append(f_source(5))
    base.append(f_source(6))
    base.append(BoundaryLabel(0,0,0,-2,4))
    for y in [3,4,5]:
        base.append(BoundaryLabel(2,0,-1,-2,y))
    for y in [2,3]:
        base.append(BoundaryLabel(2,2,0,-2,y))
        base.append(BoundaryLabel(1,2,0,-2,y))
    for y in [-5,-4,-3]:
        base.append(BoundaryLabel(2,0,0,3,y))
    for y in [-6,-5]:
        base.append(BoundaryLabel(2,2,1,3,y))
    for y in [-6,-5,-4]:
        base.append(BoundaryLabel(0,2,1,3,y))
    for y in range(1,5):
        base.append(BoundaryLabel(2,0,0,-3,y))
    for y in range(3):
        base.append(BoundaryLabel(2,2,1,-3,y))
    for y in [1,2]:
        base.append(BoundaryLabel(0,0,0,-3,y))
    for y in range(4):
        base.append(BoundaryLabel(0,2,1,-3,y))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def _in_base(w: BoundaryLabel) -> Bool:
    if w.top==2 and w.bottom==0:
        return ((w.x==1 and w.c==0 and w.y==-2) or(w.x==-1 and w.c==-2 and w.y>=3 and w.y<=5)
            or(w.x==0 and w.c==3 and w.y>=-5 and w.y<=-3) or(w.x==0 and w.c==-3 and w.y>=1 and w.y<=4))
    if w.top==0 and w.bottom==0:
        return ((w.x==1 and w.c==0 and w.y==-3) or(w.x==0 and w.c==-2 and w.y==4)
            or(w.x==0 and w.c==-3 and w.y>=1 and w.y<=2))
    if w.top==0 and w.bottom==2:
        return ((w.x==2 and w.c==0 and w.y==-3) or(w.x==1 and w.c==3 and w.y>=-6 and w.y<=-4)
            or(w.x==1 and w.c==-3 and w.y>=0 and w.y<=3))
    if w.top==2 and w.bottom==2:
        return ((w.x==0 and w.c==-2 and w.y>=2 and w.y<=3) or(w.x==1 and w.c==3 and w.y>=-6 and w.y<=-5)
            or(w.x==1 and w.c==-3 and w.y>=0 and w.y<=2))
    return w.top==1 and w.bottom==2 and w.x==0 and w.c==-2 and w.y>=2 and w.y<=3


def in_f_image(w: BoundaryLabel) raises -> Bool:
    return _in_base(w) or _in_base(reverse_label(w))


def _append(mut out: List[BoundaryEdge],kind: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(kind,k,t)
    var a=j if kind%2==1 else i
    var b=i if kind%2==1 else j
    if not f_child_allowed(kind,k,t,a,b):
        raise Error("synthesized F-family guard failed")
    var target=member_transport(-1,k,p[0],p[1],f_source(kind),a,b)
    if not in_f_image(target):
        raise Error("F-family target escaped envelope")
    out.append(BoundaryEdge(a,b,target))


def f_child_star(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var A=p[2]
    var N=p[3]
    var group=kind//2
    var out=List[BoundaryEdge]()
    if group==0:
        _append(out,kind,k,t,A,0)
        _append(out,kind,k,t,A+1,0)
        _append(out,kind,k,t,A+1,1)
    elif group==1:
        if t==0:
            _append(out,kind,k,t,0,0)
        for i in range(max(1,t),t+3):
            _append(out,kind,k,t,i,0)
        for delta in [t+1,t+2]:
            for j in range(1,min(A,N-delta)+1):
                _append(out,kind,k,t,j+delta,j)
        for j in [k+1,k+2]:
            _append(out,kind,k,t,p[0],j)
    elif group==2:
        for i in range(k+2,k+5):
            _append(out,kind,k,t,i,0)
        for delta in [k+3,k+4]:
            for j in range(1,A-delta+1):
                _append(out,kind,k,t,j+delta,j)
        for j in range(A-k-3,A-k):
            _append(out,kind,k,t,A+1,j)
    else:
        var high=1 if t>=2 else 0
        var q=A-k
        for i in range(q-1,min(A,q+1+high)+1):
            _append(out,kind,k,t,i,0)
        for delta in [q+high,q+1+high]:
            for j in range(1,min(N,A-delta)+1):
                _append(out,kind,k,t,j+delta,j)
        if k==0 or(k==1 and high==1):
            _append(out,kind,k,t,A+1,0)
        for j in range(max(1,k-high),k+3):
            _append(out,kind,k,t,A+1,j)
    return out^


def verify_f_packet(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not f_child_allowed(kind,k,t,edge.i,edge.j) or not in_f_image(edge.target):
        raise Error("F-family packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],f_source(kind),edge.i,edge.j,edge.target)


def _orient(mut out: List[BoundaryEdge],flip: Int,i: Int,j: Int,w: BoundaryLabel) raises:
    out.append(BoundaryEdge(j if flip==1 else i,i if flip==1 else j,reverse_label(w) if flip==1 else w))


def f_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var A=p[2]
    var group=kind//2
    var flip=kind%2
    var out=List[BoundaryEdge]()
    if group==0:
        _orient(out,flip,A+1,1,f_source(6))
    if group==0 or group==3:
        _orient(out,flip,A-k,0,BoundaryLabel(2,0,0,-3,3))
        _orient(out,flip,1,4,BoundaryLabel(2,2,0,0,0))
    elif group==1:
        _orient(out,flip,t+2,1,p_source(7))
        var rest=p_path(6 if flip==1 else 7,k,t)
        for edge in rest:
            out.append(edge)
    else:
        _orient(out,flip,k+3,0,chain_source(6))
        var rest=chain_path(6+flip,k,t)
        for edge in rest:
            out.append(edge)
    return out^


def f_rank(w: BoundaryLabel) raises -> Int:
    if w==BoundaryLabel(2,2,0,0,0):
        return 0
    for kind in range(8):
        if w==f_source(kind):
            return 4 if kind//2==0 else (2 if kind//2==3 else 3)
    if w==eh_source(2) or w==eh_source(3):
        return 1
    if w==p_source(6) or w==p_source(7) or w==chain_source(6) or w==chain_source(7):
        return 2
    var G=BoundaryLabel(2,0,0,-3,3)
    if w==G or w==reverse_label(G):
        return 1
    raise Error("rank undefined outside selected F-family packet")


def _verify_path(tables: SeedOverlapTables,source: BoundaryLabel,k: Int,t: Int,steps: List[BoundaryEdge],want: List[BoundaryEdge]) raises:
    var p=_parameters(-1,k,t)
    if len(steps)!=len(want):
        raise Error("incomplete F-family path")
    var w=source
    for z in range(len(steps)):
        var edge=steps[z]
        if edge.i!=want[z].i or edge.j!=want[z].j or edge.target!=want[z].target:
            raise Error("F-family intended path mismatch")
        verify_member_edge(tables,-1,k,p[0],p[1],w,edge.i,edge.j,edge.target)
        if f_rank(edge.target)>=f_rank(w):
            raise Error("selected F rank did not decrease")
        w=edge.target
    if w!=BoundaryLabel(2,2,0,0,0):
        raise Error("wrong F-family typed terminal")


def verify_f_path(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    _verify_path(tables,f_source(kind),k,t,steps,f_path(kind,k,t))


def f_child_exit(flip: Int,branch: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    if flip<0 or flip>1 or branch<0 or branch>2:
        raise Error("unknown direct F child")
    var p=_dimensions(flip,k,t)
    var A=p[2]
    var target_kind=2 if branch==0 else (5 if branch==1 else 6)
    var base=List[BoundaryEdge]()
    base.append(BoundaryEdge(A if branch==0 else A+1,1 if branch==2 else 0,f_source(target_kind)))
    var rest=f_path(target_kind,k,t)
    for edge in rest:
        base.append(edge)
    if flip==0:
        return base^
    var out=List[BoundaryEdge]()
    for edge in base:
        out.append(BoundaryEdge(edge.j,edge.i,reverse_label(edge.target)))
    return out^


def verify_f_child_exit(tables: SeedOverlapTables,flip: Int,branch: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    _verify_path(tables,f_source(flip),k,t,steps,f_child_exit(flip,branch,k,t))
