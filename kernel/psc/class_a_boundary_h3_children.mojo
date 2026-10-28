"""Eight oriented H3/J/K/L stars and selected <=5-step physical exits.

Minus boundary only; exact alpha=1/2 separator, not universal BH or closure.
"""
from finite_exact.checked_int import checked_add, checked_sub, checked_mul
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_e_children import certify_eh_children, eh_source, verify_eh_packet, _offset
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_tm_children import certify_tm_children
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _same, _cone_positive
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_mul, qx_neg
from psc.overlap_seed_patch import SeedOverlapTables


def alpha_high(k: Int, t: Int) raises -> Bool:
    if k<0 or t<0:
        raise Error("invalid half-chamber parameter")
    return t>k or (t==k and k>=2)


def _separator(k: QX, t: QX) -> QX:
    return qx_add(qx_sub(qx_add(qx_mul(qx_const(4),qx_mul(k,k)),
                              qx_mul(qx_const(20),k)),
                        qx_add(qx_mul(qx_const(4),qx_mul(t,t)),qx_mul(qx_const(24),t))),
                  qx_const(5))


def chain_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=8:
        raise Error("unknown oriented H3/J/K/L packet")
    var group=kind//2
    var w=BoundaryLabel(0,2,0,-1,3)
    if group==1:
        w=BoundaryLabel(2,0,1,2,-4)
    elif group==2:
        w=BoundaryLabel(2,0,-1,-2,5)
    elif group==3:
        w=BoundaryLabel(2,0,0,3,-4)
    return reverse_label(w) if kind%2==1 else w


def _inflated(kind: Int, n: QX, k: QX, t: QX) -> List[QX]:
    var group=kind//2
    var out: List[QX]=[qx_const(2),qx_const(2),qx_sub(qx_add(n,n),qx_const(3))]
    if group==1:
        out=[qx_const(0),qx_const(-2),qx_add(t,qx_const(6))]
    elif group==2:
        out=[qx_const(1),qx_const(3),qx_sub(k,qx_const(4))]
    elif group==3:
        out=[qx_const(-1),qx_const(-1),qx_sub(qx_const(4),n)]
    if kind%2==1:
        for z in range(3):
            out[z]=qx_neg(out[z])
    return out^


def _next(kind: Int) raises -> BoundaryLabel:
    if kind//2<3:
        return chain_source(kind+2)
    return eh_source(3 if kind%2==1 else 2)


def certify_h3_children(corrupt: Bool=False) raises:
    certify_eh_children()
    certify_tm_children() # includes the exact minus alpha+2h<1 certificate
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var k=p[2].copy()
    var t=p[3].copy()
    var A=qx_add(n,d)
    var N=qx_sub(n,qx_const(1))
    var z=qx_add(qx_add(n,n),qx_const(5)) # 2*(n+5/2)
    var raw=qx_add(qx_add(
        qx_sub(qx_mul(qx_mul(z,z),z),
               qx_mul(qx_mul(qx_const(2),qx_add(n,qx_const(2))),qx_mul(z,z))),
        qx_mul(qx_mul(qx_const(4),qx_sub(qx_sub(n,d),qx_const(1))),z)),qx_const(16))
    var want=_separator(k,t)
    if corrupt:
        want=qx_add(want,qx_const(1))
    _same(raw,want)
    # Complete disjoint integer cones. New free parameter measures distance
    # above the diagonal; no finite parameter extrapolation is used.
    _cone_positive(_separator(qx_add(qx_add(t,k),qx_const(1)),t))
    _cone_positive(qx_neg(_separator(k,qx_add(qx_add(k,t),qx_const(1)))))
    _cone_positive(qx_neg(_separator(qx_add(k,qx_const(2)),qx_add(k,qx_const(2)))))
    _same(_separator(qx_const(0),qx_const(0)),qx_const(5))
    _same(_separator(qx_const(1),qx_const(1)),qx_const(1))
    for kind in range(8):
        var source=chain_source(kind)
        var base=_inflated(kind,n,k,t)
        var R=A.copy() if source.top==0 else N.copy()
        var B=A.copy() if source.bottom==0 else N.copy()
        for ri in [1,2]:
            for rj in [1,2]:
                var top=List[QX]()
                top.append(qx_const(0))
                top.append(qx_const(ri))
                top.append(qx_add(R,qx_const(1)))
                var bottom=List[QX]()
                bottom.append(qx_const(0))
                bottom.append(qx_const(rj))
                bottom.append(qx_add(B,qx_const(1)))
                for tk in range(3):
                    for bk in range(3):
                        var ct=2 if tk==RUN else (1 if tk==LAST and source.top==2 else 0)
                        var cb=2 if bk==RUN else (1 if bk==LAST and source.bottom==2 else 0)
                        var got=symbolic_child(-1,source.top,source.bottom,_offset(source),
                            tk,top[tk],bk,bottom[bk],ct,cb)
                        var tx=0 if tk==FIRST else 1
                        var bx=0 if bk==FIRST else 1
                        var ty=qx_const(0) if tk==FIRST else qx_sub(top[tk],qx_const(1))
                        var by=qx_const(0) if bk==FIRST else qx_sub(bottom[bk],qx_const(1))
                        var expected=List[QX]()
                        expected.append(qx_add(base[0],qx_const(bx-tx)))
                        expected.append(base[1].copy())
                        expected.append(qx_add(base[2],qx_sub(by,ty)))
                        _equal3(got,expected)
        var group=kind//2
        var i=qx_add(qx_add(n,n),qx_const(2))
        var j=qx_const(0)
        var tk=RUN
        var bk=FIRST
        if group==1:
            i=qx_add(t,qx_const(2))
        elif group==2:
            i=qx_add(k,qx_const(1))
        elif group==3:
            i=qx_const(0)
            j=qx_sub(n,qx_const(2))
            tk=FIRST
            bk=RUN
        if kind%2==1:
            var old_i=i.copy()
            i=j.copy()
            j=old_i.copy()
            var old_tk=tk
            tk=bk
            bk=old_tk
        var target=_next(kind)
        _equal3(symbolic_child(-1,source.top,source.bottom,_offset(source),
                              tk,i,bk,j,target.top,target.bottom),_offset(target))
    print("CLASS_A_BOUNDARY_H3 alpha_gt_half_iff_t_gt_k_or_diag_ge_2=true",
          "eight_complete_oriented_sources=true", "uniform_image_union=76",
          "selected_coincidence_paths_at_most_five=true", "universal_BH=false")


def _dimensions(kind: Int, k: Int, t: Int) raises -> Tuple[Int,Int,Int,Int]:
    var p=_parameters(-1,k,t)
    var w=chain_source(kind)
    var A=checked_add(p[0],p[1])
    var N=checked_sub(p[0],1)
    return (p[0],p[1],A if w.top==0 else N,A if w.bottom==0 else N)


def chain_child_allowed(kind: Int, k: Int, t: Int, i: Int, j: Int) raises -> Bool:
    var p=_dimensions(kind,k,t)
    if i<0 or i>checked_add(p[2],1) or j<0 or j>checked_add(p[3],1):
        raise Error("nonexistent H3-chain occurrence")
    var a=j if kind%2==1 else i
    var b=i if kind%2==1 else j
    var n=p[0]
    var d=p[1]
    var A=checked_add(n,d)
    var N=n-1
    var group=kind//2
    if group==0:
        var high=1 if alpha_high(k,t) else 0
        var twice=checked_add(n,n)
        if a>=1 and a<=A:
            if b==0:
                return a>=checked_add(twice,2) and a<=checked_add(twice,4+high)
            if b>=1 and b<=N:
                var delta=checked_sub(a,b)
                return delta==checked_add(twice,3+high) or delta==checked_add(twice,4+high)
        if a==A+1:
            if b==0:
                return t<=1 or (t==2 and high==1)
            return b>=max(1,t-1-high) and b<=t+1
        return False
    if group==1:
        if a>=1 and a<=N:
            if b==0:
                return a>=t+2 and a<=t+4
            if b>=1 and b<=A:
                var delta=checked_sub(a,b)
                return delta==t+3 or delta==t+4
        if a==n:
            return k<=1 if b==0 else (b>=max(1,k-1) and b<=k)
        return False
    if group==2:
        if a==0:
            return b==0 and k==0
        if a>=1 and a<=N:
            if b==0:
                return a>=max(1,k) and a<=k+2
            if b>=1 and b<=A:
                var delta=checked_sub(a,b)
                return delta==k+1 or delta==k+2
        return a==n and b>=t+1 and b<=t+2
    if a==0:
        return b>=n-2 and b<=n
    if a>=1 and a<=N and b>=1 and b<=A:
        var delta=checked_sub(a,b)
        return delta==-n or delta==1-n
    return a==n and b>=checked_add(n,n)-1 and b<=checked_add(n,n)


def _in_base(w: BoundaryLabel) -> Bool:
    if w.top==2 and w.bottom==0:
        return ((w.x==1 and w.c==2 and w.y>=-7 and w.y<=-4)
            or (w.x==-1 and w.c==-2 and w.y>=3 and w.y<=5)
            or (w.x==0 and w.c==3 and w.y>=-5 and w.y<=-3))
    if w.top==2 and w.bottom==2:
        return ((w.x==2 and w.c==2 and w.y>=-8 and w.y<=-6)
            or (w.x==0 and w.c==-2 and w.y>=2 and w.y<=3)
            or (w.x==1 and w.c==3 and w.y>=-6 and w.y<=-5)
            or (w.x==-1 and w.c==-1 and w.y>=3 and w.y<=4))
    if w.top==0 and w.bottom==0:
        return ((w.x==1 and w.c==2 and w.y>=-7 and w.y<=-5)
            or (w.x==1 and w.c==3 and w.y==-4))
    if w.top==0 and w.bottom==2:
        return ((w.x==2 and w.c==2 and w.y>=-8 and w.y<=-5)
            or (w.x==0 and w.c==-1 and w.y>=1 and w.y<=3))
    if w.top==1 and w.bottom==0:
        return w.x==-1 and w.c==-2 and w.y>=3 and w.y<=4
    if w.top==1 and w.bottom==2:
        return ((w.x==0 and w.c==-2 and w.y>=2 and w.y<=3)
            or (w.x==1 and w.c==3 and w.y>=-6 and w.y<=-5)
            or (w.x==-1 and w.c==-1 and w.y>=3 and w.y<=4))
    return False


def in_chain_image(w: BoundaryLabel) raises -> Bool:
    return _in_base(w) or _in_base(reverse_label(w))


def chain_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for y in range(-7,-3):
        base.append(BoundaryLabel(2,0,1,2,y))
    for y in range(-8,-5):
        base.append(BoundaryLabel(2,2,2,2,y))
    for y in range(-7,-4):
        base.append(BoundaryLabel(0,0,1,2,y))
    for y in range(-8,-4):
        base.append(BoundaryLabel(0,2,2,2,y))
    for y in range(3,6):
        base.append(BoundaryLabel(2,0,-1,-2,y))
    for y in range(2,4):
        base.append(BoundaryLabel(2,2,0,-2,y))
        base.append(BoundaryLabel(1,2,0,-2,y))
    for y in range(3,5):
        base.append(BoundaryLabel(1,0,-1,-2,y))
    base.append(BoundaryLabel(0,0,1,3,-4))
    for y in range(-5,-2):
        base.append(BoundaryLabel(2,0,0,3,y))
    for y in [-6,-5]:
        base.append(BoundaryLabel(2,2,1,3,y))
        base.append(BoundaryLabel(1,2,1,3,y))
    for y in range(1,4):
        base.append(BoundaryLabel(0,2,0,-1,y))
    for y in [3,4]:
        base.append(BoundaryLabel(2,2,-1,-1,y))
        base.append(BoundaryLabel(1,2,-1,-1,y))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def _append(mut out: List[BoundaryEdge], kind: Int, k: Int, t: Int, i: Int, j: Int) raises:
    var p=_dimensions(kind,k,t)
    var a=j if kind%2==1 else i
    var b=i if kind%2==1 else j
    if not chain_child_allowed(kind,k,t,a,b):
        raise Error("synthesized H3-chain child failed exact guard")
    var target=member_transport(-1,k,p[0],p[1],chain_source(kind),a,b)
    if not in_chain_image(target):
        raise Error("H3-chain child escaped target packet")
    out.append(BoundaryEdge(a,b,target))


def chain_child_star(kind: Int, k: Int, t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var A=checked_add(n,p[1])
    var N=n-1
    var group=kind//2
    var out=List[BoundaryEdge]()
    var lo=1
    var hi=0
    var d0=0
    if group==0:
        var high=1 if alpha_high(k,t) else 0
        var twice=checked_add(n,n)
        for i in range(twice+2,min(A,twice+4+high)+1):
            _append(out,kind,k,t,i,0)
        d0=twice+3+high
        for delta in [d0,d0+1]:
            for j in range(1,min(N,A-delta)+1):
                _append(out,kind,k,t,j+delta,j)
        if t<=1 or (t==2 and high==1):
            _append(out,kind,k,t,A+1,0)
        for j in range(max(1,t-1-high),t+2):
            _append(out,kind,k,t,A+1,j)
    elif group==1 or group==2:
        lo=t+2 if group==1 else max(1,k)
        hi=min(N,t+4) if group==1 else k+2
        for i in range(lo,hi+1):
            _append(out,kind,k,t,i,0)
        d0=t+3 if group==1 else k+1
        for delta in [d0,d0+1]:
            for j in range(1,min(A,N-delta)+1):
                _append(out,kind,k,t,j+delta,j)
        if group==1:
            if k<=1:
                _append(out,kind,k,t,n,0)
            lo=max(1,k-1)
            hi=k
        else:
            if k==0:
                _append(out,kind,k,t,0,0)
            lo=t+1
            hi=t+2
        for j in range(lo,hi+1):
            _append(out,kind,k,t,n,j)
    else:
        for j in range(n-2,n+1):
            _append(out,kind,k,t,0,j)
        for delta in [-n,1-n]:
            for i in range(1,N+1):
                _append(out,kind,k,t,i,i-delta)
        for j in range(checked_add(n,n)-1,checked_add(n,n)+1):
            _append(out,kind,k,t,n,j)
    return out^


def verify_chain_packet(tables: SeedOverlapTables, kind: Int, k: Int, t: Int,
                        edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not chain_child_allowed(kind,k,t,edge.i,edge.j):
        raise Error("H3-chain occurrence is geometrically disjoint")
    verify_member_edge(tables,-1,k,p[0],p[1],chain_source(kind),edge.i,edge.j,edge.target)


def chain_path(kind: Int, k: Int, t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var flip=kind%2
    var out=List[BoundaryEdge]()
    for group in range(kind//2,4):
        var i=checked_add(checked_add(n,n),2)
        var j=0
        if group==1:
            i=t+2
        elif group==2:
            i=k+1
        elif group==3:
            i=0
            j=n-2
        out.append(BoundaryEdge(j if flip==1 else i,i if flip==1 else j,_next(2*group+flip)))
    out.append(BoundaryEdge(2 if flip==1 else 1,1 if flip==1 else 2,BoundaryLabel(2,2,0,0,0)))
    return out^


def chain_rank(w: BoundaryLabel) raises -> Int:
    if w==BoundaryLabel(2,2,0,0,0):
        return 0
    if w==eh_source(2) or w==eh_source(3):
        return 1
    for kind in range(8):
        if w==chain_source(kind):
            return 5-kind//2
    raise Error("rank undefined outside selected H3 packet")


def verify_chain_path(tables: SeedOverlapTables, kind: Int, k: Int, t: Int,
                      packet: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    var want=chain_path(kind,k,t)
    if len(packet)!=len(want):
        raise Error("incomplete H3-chain path")
    var source=chain_source(kind)
    for step in range(len(packet)):
        var edge=packet[step]
        if edge.i!=want[step].i or edge.j!=want[step].j or edge.target!=want[step].target:
            raise Error("H3 path occurrence or target mismatch")
        if step+1<len(packet):
            verify_chain_packet(tables,kind+2*step,k,t,edge)
        else:
            verify_eh_packet(tables,3 if kind%2==1 else 2,k,t,edge)
        if chain_rank(edge.target)>=chain_rank(source):
            raise Error("selected H3 rank did not descend")
        source=edge.target
    if source!=BoundaryLabel(2,2,0,0,0):
        raise Error("wrong H3-chain terminal")
