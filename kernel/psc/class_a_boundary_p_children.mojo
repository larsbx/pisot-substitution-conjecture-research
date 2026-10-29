"""Ten complete oriented P packets; selected physical exits, not global BH."""
from finite_exact.checked_int import checked_add
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_e_children import eh_source, _offset
from psc.class_a_boundary_h3_children import certify_h3_children, chain_source, chain_path
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _poly, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, _child, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _same, _cone_positive, _cone_nonnegative
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def p_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=10:
        raise Error("unknown oriented P packet")
    var group=kind//2
    var w=BoundaryLabel(2,2,-1,-1,3)
    if group==1:
        w=BoundaryLabel(2,2,-1,-1,4)
    elif group==2:
        w=BoundaryLabel(2,2,0,2,-2)
    elif group==3:
        w=BoundaryLabel(2,2,0,2,-3)
    elif group==4:
        w=BoundaryLabel(0,2,1,2,-4)
    return reverse_label(w) if kind%2==1 else w


def _inflated(kind: Int, n: QX, k: QX, t: QX) -> List[QX]:
    var group=kind//2
    var out: List[QX]=[qx_const(0),qx_const(2),qx_neg(qx_add(t,qx_const(5)))]
    if group==1:
        out=[qx_const(1),qx_const(3),qx_sub(k,qx_const(3))]
    elif group==2:
        out=[qx_const(0),qx_const(0),qx_const(2)]
    elif group==3:
        out=[qx_const(-1),qx_const(-1),qx_sub(qx_const(3),n)]
    elif group==4:
        out=[qx_const(0),qx_const(-2),qx_add(t,qx_const(6))]
    if kind%2==1:
        for z in range(3):
            out[z]=qx_neg(out[z])
    return out^


def _selected_cone(kind: Int, n: QX, d: QX, k: QX, t: QX,
                   i: QX, j: QX, tk: Int, bk: Int, target: BoundaryLabel) raises:
    # Reuse the existing prefix kernel with explicitly shifted cone parameters.
    # Its run-index bounds still have to certify on the ENTIRE supplied cone.
    var source=p_source(kind)
    if _child(source.top,tk)!=target.top or _child(source.bottom,bk)!=target.bottom:
        raise Error("conditional selected types do not match actual words")
    var top=_prefix(source.top,tk,i,-1,n,d)
    var bottom=_prefix(source.bottom,bk,j,-1,n,d)
    var base=_inflated(kind,n,k,t)
    var got=List[QX]()
    for z in range(3):
        got.append(qx_add(base[z],qx_sub(bottom[z],top[z])))
    _equal3(got,_offset(target))


def certify_p_children(corrupt: Bool=False) raises:
    certify_h3_children() # includes v<1 and w<1, not just alpha<1
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
    # beta*alpha=t+3-2/beta. Thus alpha>h: t+3-2h>1.
    _same(qx_sub(qx_sub(n,d),qx_const(1)),qx_neg(qx_add(t,qx_const(3))))
    var Xalpha=tp_sub(X2,tp_scale(X,qx_add(n,qx_const(2))))
    var alpha_identity=tp_add(tp_sub(tp_mul(X,Xalpha),tp_scale(X,qx_add(t,qx_const(3)))),
                              _linear(qx_const(2),qx_const(0)))
    _equal(alpha_identity,f)
    _cone_positive(qx_add(t,qx_const(2)))
    # beta*a=beta^2-n*beta-1, beta*b=beta+1.
    var ba=tp_sub(tp_sub(X2,tp_scale(X,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    for kind in range(10):
        var source=p_source(kind)
        var base=_inflated(kind,n,k,t)
        var field=tp_add(tp_add(tp_scale(ba,qx_const(source.x)),
                              tp_scale(bb,qx_const(source.c))),tp_scale(X,qx_const(source.y)))
        var want=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(X,base[2]))
        if corrupt:
            want=tp_add(want,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(tp_mul(X,field),f),tp_mod_monic(want,f))
        var betaB=_linear(qx_const(2),qx_neg(qx_add(t,qx_const(3))))
        if kind//2==1:
            betaB=tp_add(X2,_linear(qx_const(2),qx_sub(k,n)))
        elif kind//2==2:
            betaB=tp_scale(X,qx_const(2))
        elif kind//2==3:
            betaB=tp_sub(tp_scale(X,qx_const(2)),X2)
        elif kind//2==4:
            betaB=_linear(qx_const(-2),qx_add(t,qx_const(4)))
        if kind%2==1:
            betaB=tp_scale(betaB,qx_const(-1))
        _equal(tp_mod_monic(want,f),tp_mod_monic(betaB,f))
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
                        var got=symbolic_child(-1,source.top,source.bottom,_offset(source),
                                             tk,top[tk],bk,bottom[bk],ct,cb)
                        var ty=qx_const(0) if tk==FIRST else qx_sub(top[tk],qx_const(1))
                        var by=qx_const(0) if bk==FIRST else qx_sub(bottom[bk],qx_const(1))
                        var expected: List[QX]=[qx_add(base[0],qx_const((0 if bk==FIRST else 1)-(0 if tk==FIRST else 1))),
                                               base[1].copy(),qx_add(base[2],qx_sub(by,ty))]
                        _equal3(got,expected)
    # All selected ordinals, including k=0's alternate D exit, are word-legal.
    _cone_nonnegative(qx_sub(N,qx_add(t,qx_const(2))))
    _cone_nonnegative(qx_sub(N,qx_add(k,qx_const(2))))
    _cone_positive(qx_sub(A,qx_add(t,qx_const(2))))
    _cone_positive(qx_sub(A,qx_add(qx_add(n,t),qx_const(4))))
    for flip in range(2):
        for group in range(5):
            if group==2:
                continue # handled on n>=4's two shifted cones below
            var source=p_source(2*group)
            var i=qx_const(0)
            var j=qx_add(t,qx_const(2))
            var tk=FIRST
            var bk=RUN
            var target=p_source(8)
            if group==1:
                i=qx_add(k,qx_const(2))
                j=qx_const(0)
                tk=RUN
                bk=FIRST
                target=chain_source(6)
            elif group==2:
                i=qx_const(3)
                j=qx_const(1)
                tk=RUN
                bk=RUN
                target=BoundaryLabel(2,2,0,0,0)
            elif group==3:
                j=N.copy()
                target=eh_source(2)
            elif group==4:
                i=qx_add(t,qx_const(2))
                j=qx_const(0)
                tk=RUN
                bk=FIRST
                target=chain_source(4)
            if flip==1:
                source=reverse_label(source)
                target=reverse_label(target)
                var old=i.copy()
                i=j.copy()
                j=old.copy()
                var old_kind=tk
                tk=bk
                bk=old_kind
            _equal3(symbolic_child(-1,source.top,source.bottom,_offset(source),
                                  tk,i,bk,j,target.top,target.bottom),_offset(target))
        # Optional shorter P exit: certify with k replaced by k+1.
        var target=p_source(6+flip)
        var i=qx_const(1) if flip==0 else qx_add(t,qx_const(3))
        var j=qx_add(t,qx_const(3)) if flip==0 else qx_const(1)
        _selected_cone(flip,qx_add(n,qx_const(1)),qx_add(d,qx_const(1)),
                       qx_add(k,qx_const(1)),t,i,j,RUN,RUN,target)
        # A's typed (3,1) terminal: k>=1 or t>=1 is exactly n>=4.
        i=qx_const(3 if flip==0 else 1)
        j=qx_const(1 if flip==0 else 3)
        target=BoundaryLabel(2,2,0,0,0)
        _selected_cone(4+flip,qx_add(n,qx_const(1)),qx_add(d,qx_const(1)),
                       qx_add(k,qx_const(1)),t,i,j,RUN,RUN,target)
        _selected_cone(4+flip,qx_add(n,qx_const(1)),qx_add(d,qx_const(2)),
                       k,qx_add(t,qx_const(1)),i,j,RUN,RUN,target)
    print("CLASS_A_BOUNDARY_P ten_complete_oriented_stars=true", "selected_typed_exits_at_most_five=true",
          "small_k_alternative=true", "n3_half_coincidence_not_typed=true", "global_BH=false")


def _dimensions(kind: Int, k: Int, t: Int) raises -> Tuple[Int,Int,Int,Int]:
    var p=_parameters(-1,k,t)
    var w=p_source(kind)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,2) # all formulas/endpoints below fit this bound
    return (p[0],p[1],A if w.top==0 else p[0]-1,A if w.bottom==0 else p[0]-1)


def p_child_allowed(kind: Int, k: Int, t: Int, i: Int, j: Int) raises -> Bool:
    var p=_dimensions(kind,k,t)
    if i<0 or i>p[2]+1 or j<0 or j>p[3]+1:
        raise Error("nonexistent P-packet occurrence")
    var a=j if kind%2==1 else i
    var b=i if kind%2==1 else j
    var n=p[0]
    var N=n-1
    var group=kind//2
    if group==0:
        if a==0:
            return k==0 if b==n else b>=t+1 and b<=t+3 and b<=N
        if a>=1 and a<=N:
            if b>=1 and b<=N:
                return b-a==t+2 or b-a==t+3
            return b==n and a>=max(1,k) and a<=k+1
        return False
    if group==1:
        if a>=1 and a<=N:
            if b==0:
                return a>=k+1 and a<=k+3
            return b>=1 and b<=N and (a-b==k+2 or a-b==k+3)
        if a==n:
            return t==0 if b==0 else b>=max(1,t) and b<=t+1 and b<=N
        return False
    if group==2:
        if a==0:
            return b==0
        if a>=1 and a<=N:
            return a<=2 if b==0 else b>=1 and b<=N and a-b==2
        return a==n and (b==n-2 or b==n-1)
    if group==3:
        return a==0 and (b==n-1 or b==n)
    if a>=1 and a<=p[0]+p[1]:
        if b==0:
            return a>=t+2 and a<=t+4
        if b>=1 and b<=N:
            return a-b==t+3 or a-b==t+4
        return b==n and (a==n+t+3 or a==n+t+4)
    return False


def p_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for y in [-5,-4,-3]:
        base.append(BoundaryLabel(0,2,1,2,y))
        base.append(BoundaryLabel(2,0,0,3,y))
    base.append(BoundaryLabel(0,1,1,2,-3))
    base.append(BoundaryLabel(1,0,0,3,-5))
    for y in [-3,-2]:
        base.append(BoundaryLabel(2,2,0,2,y))
        base.append(BoundaryLabel(2,1,0,2,y))
    for y in [-6,-5]:
        base.append(BoundaryLabel(2,2,1,3,y))
        base.append(BoundaryLabel(1,2,1,3,y))
    base.append(BoundaryLabel(0,0,0,0,2))
    for y in [1,2]:
        base.append(BoundaryLabel(2,0,-1,0,y))
    base.append(BoundaryLabel(2,2,0,0,0))
    for y in [0,1]:
        base.append(BoundaryLabel(1,2,0,0,y))
    base.append(BoundaryLabel(0,2,0,-1,1))
    base.append(BoundaryLabel(0,1,0,-1,2))
    for y in [3,4,5]:
        base.append(BoundaryLabel(2,0,-1,-2,y))
    for y in [2,3]:
        base.append(BoundaryLabel(2,2,0,-2,y))
        base.append(BoundaryLabel(2,1,0,-2,y))
    var out=List[BoundaryLabel]()
    for w in base:
        for v in [w,reverse_label(w)]:
            var seen=False
            for old in out:
                if old==v:
                    seen=True
            if not seen:
                out.append(v)
    return out^


def _in_base(w: BoundaryLabel) -> Bool:
    if w.top==0 and w.bottom==2:
        return (w.x==1 and w.c==2 and w.y>=-5 and w.y<=-3) or (w.x==0 and w.c==-1 and w.y==1)
    if w.top==0 and w.bottom==1:
        return (w.x==1 and w.c==2 and w.y==-3) or (w.x==0 and w.c==-1 and w.y==2)
    if w.top==2 and w.bottom==2:
        return ((w.x==0 and w.c==2 and w.y>=-3 and w.y<=-2)
            or (w.x==1 and w.c==3 and w.y>=-6 and w.y<=-5)
            or (w.x==0 and w.c==0 and w.y==0)
            or (w.x==0 and w.c==-2 and w.y>=2 and w.y<=3))
    if w.top==2 and w.bottom==1:
        return (w.x==0 and w.c==2 and w.y>=-3 and w.y<=-2) or (w.x==0 and w.c==-2 and w.y>=2 and w.y<=3)
    if w.top==2 and w.bottom==0:
        return ((w.x==0 and w.c==3 and w.y>=-5 and w.y<=-3)
            or (w.x==-1 and w.c==0 and w.y>=1 and w.y<=2)
            or (w.x==-1 and w.c==-2 and w.y>=3 and w.y<=5))
    if w.top==1 and w.bottom==0:
        return w.x==0 and w.c==3 and w.y==-5
    if w.top==1 and w.bottom==2:
        return (w.x==1 and w.c==3 and w.y>=-6 and w.y<=-5) or (w.x==0 and w.c==0 and w.y>=0 and w.y<=1)
    return w.top==0 and w.bottom==0 and w.x==0 and w.c==0 and w.y==2


def in_p_image(w: BoundaryLabel) raises -> Bool:
    # Fixed scalar predicate: no packet allocation in the occurrence loop.
    return _in_base(w) or _in_base(reverse_label(w))


def _append(mut out: List[BoundaryEdge], kind: Int, k: Int, t: Int, i: Int, j: Int) raises:
    var p=_dimensions(kind,k,t)
    var a=j if kind%2==1 else i
    var b=i if kind%2==1 else j
    if not p_child_allowed(kind,k,t,a,b):
        raise Error("synthesized P child failed guard")
    var target=member_transport(-1,k,p[0],p[1],p_source(kind),a,b)
    if not in_p_image(target):
        raise Error("P child escaped typed target packet")
    out.append(BoundaryEdge(a,b,target))


def p_child_star(kind: Int, k: Int, t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var N=n-1
    var group=kind//2
    var out=List[BoundaryEdge]()
    if group==0:
        for j in range(t+1,min(N,t+3)+1):
            _append(out,kind,k,t,0,j)
        if k==0:
            _append(out,kind,k,t,0,n)
        for delta in [t+2,t+3]:
            for i in range(1,N-delta+1):
                _append(out,kind,k,t,i,i+delta)
        for i in range(max(1,k),k+2):
            _append(out,kind,k,t,i,n)
    elif group==1:
        for i in range(k+1,min(N,k+3)+1):
            _append(out,kind,k,t,i,0)
        for delta in [k+2,k+3]:
            for j in range(1,N-delta+1):
                _append(out,kind,k,t,j+delta,j)
        if t==0:
            _append(out,kind,k,t,n,0)
        for j in range(max(1,t),t+2):
            _append(out,kind,k,t,n,j)
    elif group==2:
        _append(out,kind,k,t,0,0)
        for i in [1,2]:
            _append(out,kind,k,t,i,0)
        for j in range(1,N-1):
            _append(out,kind,k,t,j+2,j)
        for j in [n-2,n-1]:
            _append(out,kind,k,t,n,j)
    elif group==3:
        for j in [n-1,n]:
            _append(out,kind,k,t,0,j)
    else:
        for i in range(t+2,t+5):
            _append(out,kind,k,t,i,0)
        for delta in [t+3,t+4]:
            for j in range(1,N+1):
                _append(out,kind,k,t,j+delta,j)
        for i in [n+t+3,n+t+4]:
            _append(out,kind,k,t,i,n)
    return out^


def verify_p_packet(tables: SeedOverlapTables, kind: Int, k: Int, t: Int, edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not p_child_allowed(kind,k,t,edge.i,edge.j) or not in_p_image(edge.target):
        raise Error("P occurrence/target packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],p_source(kind),edge.i,edge.j,edge.target)


def _path_append(mut out: List[BoundaryEdge], flip: Int, i: Int, j: Int, w: BoundaryLabel) raises:
    out.append(BoundaryEdge(j if flip==1 else i,i if flip==1 else j,reverse_label(w) if flip==1 else w))


def p_path(kind: Int, k: Int, t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var group=kind//2
    var flip=kind%2
    var out=List[BoundaryEdge]()
    var suffix=-1
    if group==0:
        if k==0:
            _path_append(out,flip,0,t+2,p_source(8))
            _path_append(out,flip,t+2,0,chain_source(4))
            suffix=4
        else:
            _path_append(out,flip,1,t+3,p_source(6))
    elif group==1:
        _path_append(out,flip,k+2,0,chain_source(6))
        suffix=6
    elif group==2:
        if n>=4:
            _path_append(out,flip,3,1,BoundaryLabel(2,2,0,0,0))
            return out^
        # Only k=t=0: the would-be (3,1) y/y terminal is actually c/y.
        _path_append(out,flip,1,0,BoundaryLabel(2,0,-1,0,2))
        _path_append(out,flip,1,2,p_source(6))
    elif group==4:
        _path_append(out,flip,t+2,0,chain_source(4))
        suffix=4
    if suffix>=0:
        var rest=chain_path(suffix+flip,k,t)
        for edge in rest:
            out.append(edge)
    else:
        _path_append(out,flip,0,n-1,eh_source(2))
        _path_append(out,flip,1,2,BoundaryLabel(2,2,0,0,0))
    return out^


def p_rank(w: BoundaryLabel, k: Int, t: Int) raises -> Int:
    var p=_parameters(-1,k,t)
    if w==BoundaryLabel(2,2,0,0,0):
        return 0
    if w==eh_source(2) or w==eh_source(3):
        return 1
    for kind in range(10):
        if w==p_source(kind):
            var group=kind//2
            if group==0:
                return 5
            if group==1:
                return 3
            if group==2:
                return 4 if p[0]==3 else 1
            return 2 if group==3 else 4
    for kind in [4,5,6,7]:
        if w==chain_source(kind):
            return 5-kind//2
    var F=BoundaryLabel(2,0,-1,0,2)
    if k==0 and t==0 and (w==F or w==reverse_label(F)):
        return 3
    raise Error("rank undefined outside selected P packet")


def verify_p_path(tables: SeedOverlapTables, kind: Int, k: Int, t: Int, packet: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    var want=p_path(kind,k,t)
    if len(packet)!=len(want):
        raise Error("incomplete P path")
    var w=p_source(kind)
    for step in range(len(packet)):
        var edge=packet[step]
        if edge.i!=want[step].i or edge.j!=want[step].j or edge.target!=want[step].target:
            raise Error("P path occurrence or typed target mismatch")
        verify_member_edge(tables,-1,k,p[0],p[1],w,edge.i,edge.j,edge.target)
        if p_rank(edge.target,k,t)>=p_rank(w,k,t):
            raise Error("selected P stage rank did not decrease")
        w=edge.target
    if w!=BoundaryLabel(2,2,0,0,0):
        raise Error("wrong typed P terminal")
