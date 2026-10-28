"""Complete E2/Dxx stars and actual five-step exits; no global closure/BH."""
from finite_exact.checked_int import checked_add
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_p_children import certify_p_children
from psc.class_a_boundary_e_children import eh_source, _offset
from psc.class_a_boundary_h3_children import alpha_high, chain_source, chain_path
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, _child, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _cone_nonnegative, _same
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def e2_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=4:
        raise Error("unknown oriented E2/Dxx packet")
    var w=BoundaryLabel(0,0,0,0,2) if kind//2==0 else BoundaryLabel(0,0,1,2,-4)
    return reverse_label(w) if kind%2==1 else w


def _inflated(kind: Int, n: QX, t: QX) -> List[QX]:
    var out: List[QX]=[qx_const(2),qx_const(2),qx_sub(qx_add(n,n),qx_const(2))]
    if kind//2==1:
        out=[qx_const(0),qx_const(-2),qx_add(t,qx_const(6))]
    if kind%2==1:
        for z in range(3):
            out[z]=qx_neg(out[z])
    return out^


def _selected(kind: Int, n: QX, d: QX, t: QX, i: QX, j: QX,
              tk: Int, bk: Int, target: BoundaryLabel) raises:
    var source=e2_source(kind)
    if _child(0,tk)!=target.top or _child(0,bk)!=target.bottom:
        raise Error("selected child types mismatch")
    var top=_prefix(0,tk,i,-1,n,d)
    var bottom=_prefix(0,bk,j,-1,n,d)
    var base=_inflated(kind,n,t)
    var got=List[QX]()
    for z in range(3):
        got.append(qx_add(base[z],qx_sub(bottom[z],top[z])))
    _equal3(got,_offset(target))


def certify_e2_children(corrupt: Bool=False) raises:
    certify_p_children() # alpha>h, v<1, w<1 and the exact half separator
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var k=p[2].copy()
    var t=p[3].copy()
    var A=qx_add(n,d)
    var X=_linear(qx_const(0),qx_const(1))
    var X2=tp_mul(X,X)
    var f=_cubic(-1,n,d)
    var ba=tp_sub(tp_sub(X2,tp_scale(X,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    for kind in range(4):
        var source=e2_source(kind)
        var base=_inflated(kind,n,t)
        var field=tp_add(tp_add(tp_scale(ba,qx_const(source.x)),tp_scale(bb,qx_const(source.c))),
                         tp_scale(X,qx_const(source.y)))
        var expected=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(X,base[2]))
        if corrupt:
            expected=tp_add(expected,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(tp_mul(X,field),f),tp_mod_monic(expected,f))
        var betaB=tp_scale(X2,qx_const(2)) if kind//2==0 else _linear(qx_const(-2),qx_add(t,qx_const(4)))
        if kind%2==1:
            betaB=tp_scale(betaB,qx_const(-1))
        _equal(tp_mod_monic(expected,f),tp_mod_monic(betaB,f))
        for ri in [1,2]:
            for rj in [1,2]:
                var top: List[QX]=[qx_const(0),qx_const(ri),qx_add(A,qx_const(1))]
                var bottom: List[QX]=[qx_const(0),qx_const(rj),qx_add(A,qx_const(1))]
                for tk in range(3):
                    for bk in range(3):
                        var ct=2 if tk==RUN else 0
                        var cb=2 if bk==RUN else 0
                        var got=symbolic_child(-1,0,0,_offset(source),tk,top[tk],bk,bottom[bk],ct,cb)
                        var pt=_prefix(0,tk,top[tk],-1,n,d)
                        var pb=_prefix(0,bk,bottom[bk],-1,n,d)
                        var want=List[QX]()
                        for z in range(3):
                            want.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
                        _equal3(got,want)
    _same(A,qx_add(qx_add(qx_add(n,n),t),qx_const(2)))
    # Dxx's RF(t+2,0), plus all three last/run ordinals, are cone-legal.
    _cone_nonnegative(qx_sub(A,qx_add(t,qx_const(4))))
    _cone_nonnegative(qx_sub(A,qx_add(qx_add(n,n),qx_const(1))))
    for flip in range(2):
        var i=qx_add(t,qx_const(2))
        var j=qx_const(0)
        var tk=RUN
        var bk=FIRST
        var target=chain_source(4+flip)
        if flip==1:
            i=qx_const(0)
            j=qx_add(t,qx_const(2))
            tk=FIRST
            bk=RUN
        _selected(2+flip,n,d,t,i,j,tk,bk,target)
        # E2 t>=1: replace t by t'+1, n by n+1, d by d+2.
        var ns=qx_add(n,qx_const(1))
        var ds=qx_add(d,qx_const(2))
        var ts=qx_add(t,qx_const(1))
        var index=qx_add(qx_add(ns,ns),qx_const(3))
        target=chain_source(2+flip)
        i=index.copy() if flip==0 else qx_const(0)
        j=qx_const(0) if flip==0 else index.copy()
        _selected(flip,ns,ds,ts,i,j,RUN if flip==0 else FIRST,FIRST if flip==0 else RUN,target)
        # E2 t=0: LAST/FIRST, not a fictitious RUN at index A+1.
        ns=qx_add(k,qx_const(3))
        ds=qx_add(k,qx_const(5))
        index=qx_add(qx_add(ns,ds),qx_const(1))
        i=index.copy() if flip==0 else qx_const(0)
        j=qx_const(0) if flip==0 else index.copy()
        _selected(flip,ns,ds,qx_const(0),i,j,LAST if flip==0 else FIRST,FIRST if flip==0 else LAST,e2_source(2+flip))
    print("CLASS_A_BOUNDARY_E2 four_complete_oriented_stars=true", "chamber_union_labels=46",
          "E2_t0_unique_last_child=true", "typed_exits_at_most_five=true", "global_closure=false", "BH=false")


def _dimensions(kind: Int, k: Int, t: Int) raises -> Tuple[Int,Int,Int]:
    _=e2_source(kind)
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,8) # also bound unclipped diagonal/endpoint constants
    return (p[0],p[1],A)


def e2_child_allowed(kind: Int, k: Int, t: Int, i: Int, j: Int) raises -> Bool:
    var p=_dimensions(kind,k,t)
    var A=p[2]
    if i<0 or i>A+1 or j<0 or j>A+1:
        raise Error("nonexistent E2/Dxx occurrence")
    var a=j if kind%2==1 else i
    var b=i if kind%2==1 else j
    var twice=checked_add(p[0],p[0])
    if kind//2==0:
        var high=1 if alpha_high(k,t) else 0
        if a>=1 and a<=A:
            if b==0:
                return a>=twice+3 and a<=twice+5+high
            if b>=1 and b<=A:
                return a-b==twice+4+high or a-b==twice+5+high
        if a==A+1:
            if b==0:
                return t<=2 or (t==3 and high==1)
            return b>=max(1,t-2-high) and b<=t
        return False
    if a>=1 and a<=A:
        if b==0:
            return a>=t+2 and a<=t+4
        return b>=1 and b<=A and (a-b==t+3 or a-b==t+4)
    return a==A+1 and b>=twice-1 and b<=twice+1


def _in_base(w: BoundaryLabel) -> Bool:
    if w.top==2 and w.bottom==0:
        return (w.x==1 and w.c==2 and w.y>=-7 and w.y<=-4) or (w.x==-1 and w.c==-2 and w.y>=3 and w.y<=5)
    if w.top==2 and w.bottom==2:
        return (w.x==2 and w.c==2 and w.y>=-8 and w.y<=-6) or (w.x==0 and w.c==-2 and w.y>=2 and w.y<=3)
    if w.top==0 and w.bottom==0:
        return w.x==1 and w.c==2 and w.y>=-7 and w.y<=-4
    return w.top==0 and w.bottom==2 and ((w.x==2 and w.c==2 and w.y>=-8 and w.y<=-5)
        or (w.x==0 and w.c==-2 and w.y>=2 and w.y<=4))


def in_e2_image(w: BoundaryLabel) raises -> Bool:
    return _in_base(w) or _in_base(reverse_label(w))


def e2_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for y in range(-7,-3):
        base.append(BoundaryLabel(2,0,1,2,y))
        base.append(BoundaryLabel(0,0,1,2,y))
    for y in range(-8,-5):
        base.append(BoundaryLabel(2,2,2,2,y))
    for y in range(-8,-4):
        base.append(BoundaryLabel(0,2,2,2,y))
    for y in range(3,6):
        base.append(BoundaryLabel(2,0,-1,-2,y))
    for y in [2,3]:
        base.append(BoundaryLabel(2,2,0,-2,y))
    for y in [2,3,4]:
        base.append(BoundaryLabel(0,2,0,-2,y))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def _append(mut out: List[BoundaryEdge], kind: Int, k: Int, t: Int, i: Int, j: Int) raises:
    var p=_dimensions(kind,k,t)
    var a=j if kind%2==1 else i
    var b=i if kind%2==1 else j
    if not e2_child_allowed(kind,k,t,a,b):
        raise Error("synthesized E2 child failed exact guard")
    var target=member_transport(-1,k,p[0],p[1],e2_source(kind),a,b)
    if not in_e2_image(target):
        raise Error("E2 child escaped typed target packet")
    out.append(BoundaryEdge(a,b,target))


def e2_child_star(kind: Int, k: Int, t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var twice=checked_add(p[0],p[0])
    var A=p[2]
    var out=List[BoundaryEdge]()
    if kind//2==0:
        var high=1 if alpha_high(k,t) else 0
        for i in range(twice+3,min(A,twice+5+high)+1):
            _append(out,kind,k,t,i,0)
        for delta in [twice+4+high,twice+5+high]:
            for j in range(1,A-delta+1):
                _append(out,kind,k,t,j+delta,j)
        if t<=2 or(t==3 and high==1):
            _append(out,kind,k,t,A+1,0)
        for j in range(max(1,t-2-high),t+1):
            _append(out,kind,k,t,A+1,j)
    else:
        for i in range(t+2,t+5):
            _append(out,kind,k,t,i,0)
        for delta in [t+3,t+4]:
            for j in range(1,A-delta+1):
                _append(out,kind,k,t,j+delta,j)
        for j in range(twice-1,twice+2):
            _append(out,kind,k,t,A+1,j)
    return out^


def verify_e2_packet(tables: SeedOverlapTables, kind: Int, k: Int, t: Int, edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not e2_child_allowed(kind,k,t,edge.i,edge.j) or not in_e2_image(edge.target):
        raise Error("E2 occurrence/target packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],e2_source(kind),edge.i,edge.j,edge.target)


def e2_path(kind: Int, k: Int, t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var flip=kind%2
    var out=List[BoundaryEdge]()
    var start=4
    if kind//2==0:
        if t==0:
            out.append(BoundaryEdge(0 if flip==1 else p[2]+1,p[2]+1 if flip==1 else 0,e2_source(2+flip)))
        else:
            var i=checked_add(checked_add(p[0],p[0]),3)
            out.append(BoundaryEdge(0 if flip==1 else i,i if flip==1 else 0,chain_source(2+flip)))
            start=2
    if kind//2==1 or t==0:
        out.append(BoundaryEdge(0 if flip==1 else t+2,t+2 if flip==1 else 0,chain_source(4+flip)))
    var suffix=chain_path(start+flip,k,t)
    for edge in suffix:
        out.append(edge)
    return out^


def e2_rank(w: BoundaryLabel) raises -> Int:
    if w==BoundaryLabel(2,2,0,0,0):
        return 0
    if w==eh_source(2) or w==eh_source(3):
        return 1
    for kind in range(4):
        if w==e2_source(kind):
            return 5-kind//2
    for kind in range(2,8):
        if w==chain_source(kind):
            return 5-kind//2
    raise Error("rank undefined outside selected E2 packet")


def verify_e2_path(tables: SeedOverlapTables, kind: Int, k: Int, t: Int, packet: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    var want=e2_path(kind,k,t)
    if len(packet)!=len(want):
        raise Error("incomplete E2 path")
    var source=e2_source(kind)
    for step in range(len(packet)):
        var edge=packet[step]
        if edge.i!=want[step].i or edge.j!=want[step].j or edge.target!=want[step].target:
            raise Error("E2 path occurrence or intended typed target mismatch")
        verify_member_edge(tables,-1,k,p[0],p[1],source,edge.i,edge.j,edge.target)
        if e2_rank(edge.target)>=e2_rank(source):
            raise Error("selected E2 rank did not descend")
        source=edge.target
    if source!=BoundaryLabel(2,2,0,0,0):
        raise Error("wrong E2 typed terminal")
