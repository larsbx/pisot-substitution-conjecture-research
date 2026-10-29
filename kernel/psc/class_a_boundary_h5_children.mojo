"""Both complete H5 child stars; exact t separator, no closed-carrier/BH claim."""
from finite_exact.checked_int import checked_add, checked_sub
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_h5_exit import certify_h5_exits, h5_source, h5_path, verify_h5_path
from psc.class_a_boundary_e_children import _offset
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _same, _cone_positive, _cone_nonnegative
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def h5_child_source(flip: Int) raises -> BoundaryLabel:
    if flip<0 or flip>1:
        raise Error("unknown H5 orientation")
    return reverse_label(h5_source()) if flip==1 else h5_source()


def _inflated(flip: Int, q: QX) -> List[QX]:
    var out: List[QX]=[qx_const(1),qx_const(-3),qx_add(q,qx_const(2))]
    if flip==1:
        for z in range(3):
            out[z]=qx_neg(out[z])
    return out^


def certify_h5_children(corrupt: Bool=False) raises:
    certify_h5_exits()
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var k=p[2].copy()
    var t=p[3].copy()
    var A=qx_add(n,d)
    var N=qx_sub(n,qx_const(1))
    var q=qx_sub(qx_add(A,qx_const(2)),k)
    _same(q,qx_add(qx_add(n,qx_add(t,t)),qx_const(7)))
    _same(q,qx_add(qx_sub(qx_add(d,d),n),qx_const(3)))
    _same(qx_sub(A,qx_sub(q,qx_const(1))),qx_sub(k,qx_const(1)))
    _cone_positive(qx_sub(q,qx_const(1)))
    _cone_positive(qx_sub(N,k))
    var X=_linear(qx_const(0),qx_const(1))
    var X2=tp_mul(X,X)
    var alpha=tp_sub(X,_linear(qx_add(n,qx_const(2)),qx_const(0)))
    var f=_cubic(-1,n,d)
    # beta^2*(alpha-4/beta)=(t-1)*beta-2.
    var raw=tp_sub(tp_mul(X2,alpha),tp_scale(X,qx_const(4)))
    var want=_linear(qx_const(-2),qx_sub(t,qx_const(1)))
    if corrupt:
        want=tp_add(want,_linear(qx_const(1),qx_const(0)))
    _equal(tp_mod_monic(raw,f),want)
    # At t=0,1 the RHS is -beta-2,-2; at t>=2 its coefficient
    # after t=t'+2 is t'+1>=1, so it is >=beta-2>0.
    _same(qx_sub(qx_const(0),qx_const(1)),qx_const(-1))
    _same(qx_sub(qx_const(1),qx_const(1)),qx_const(0))
    _cone_positive(qx_sub(qx_add(t,qx_const(2)),qx_const(1)))
    var ba=tp_sub(tp_sub(X2,tp_scale(X,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    for flip in range(2):
        var source=h5_child_source(flip)
        var base=_inflated(flip,q)
        var field=tp_add(tp_add(tp_scale(ba,qx_const(source.x)),tp_scale(bb,qx_const(source.c))),tp_scale(X,qx_const(source.y)))
        var expected=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(X,base[2]))
        _equal(tp_mod_monic(tp_mul(X,field),f),tp_mod_monic(expected,f))
        var betaB=tp_add(X2,_linear(qx_const(-4),qx_add(qx_add(t,t),qx_const(6))))
        if flip==1:
            betaB=tp_scale(betaB,qx_const(-1))
        _equal(tp_mod_monic(expected,f),tp_mod_monic(betaB,f))
        var R=A.copy() if flip==0 else N.copy()
        var B=N.copy() if flip==0 else A.copy()
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
                        var target=List[QX]()
                        for z in range(3):
                            target.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
                        _equal3(got,target)
    print("CLASS_A_BOUNDARY_H5_CHILDREN eta_positive_iff_t_ge_2=true", "two_complete_orientations=true",
          "occurrences_each=2k+1", "chamber_union_labels=30", "selected_typed_exits_at_most_three=true", "BH=false")


def _dimensions(flip: Int,k: Int,t: Int) raises -> Tuple[Int,Int,Int,Int,Int]:
    _=h5_child_source(flip)
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,8)
    return (p[0],p[1],A,p[0]-1,checked_sub(checked_add(A,2),k))


def h5_child_allowed(flip: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    var p=_dimensions(flip,k,t)
    var R=p[2] if flip==0 else p[3]
    var B=p[3] if flip==0 else p[2]
    if i<0 or i>R+1 or j<0 or j>B+1:
        raise Error("nonexistent H5 child occurrence")
    var a=j if flip==1 else i
    var b=i if flip==1 else j
    var high=1 if t>=2 else 0
    var q=p[4]
    if a>=1 and a<=p[2]:
        if b==0:
            return a>=q-1 and a<=q+1+high
        return b>=1 and b<=p[3] and (a-b==q+high or a-b==q+1+high)
    if a==p[2]+1:
        if b==0:
            return k<=2 or(k==3 and high==1)
        return b>=max(1,k-2-high) and b<=k
    return False


def _in_base(w: BoundaryLabel) -> Bool:
    if w.c!=-3:
        return False
    if w.top==2 and w.bottom==0:
        return w.x==0 and w.y>=1 and w.y<=4
    if w.top==0 and w.bottom==0:
        return w.x==0 and w.y>=1 and w.y<=4
    if w.top==2 and w.bottom==2:
        return w.x==1 and w.y>=0 and w.y<=2
    return w.top==0 and w.bottom==2 and w.x==1 and w.y>=0 and w.y<=3


def in_h5_image(w: BoundaryLabel) raises -> Bool:
    return _in_base(w) or _in_base(reverse_label(w))


def h5_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for y in range(1,5):
        base.append(BoundaryLabel(2,0,0,-3,y))
        base.append(BoundaryLabel(0,0,0,-3,y))
    for y in range(3):
        base.append(BoundaryLabel(2,2,1,-3,y))
    for y in range(4):
        base.append(BoundaryLabel(0,2,1,-3,y))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def _append(mut out: List[BoundaryEdge],flip: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(flip,k,t)
    var a=j if flip==1 else i
    var b=i if flip==1 else j
    if not h5_child_allowed(flip,k,t,a,b):
        raise Error("synthesized H5 child failed guard")
    var target=member_transport(-1,k,p[0],p[1],h5_child_source(flip),a,b)
    if not in_h5_image(target):
        raise Error("H5 child escaped typed target packet")
    out.append(BoundaryEdge(a,b,target))


def h5_child_star(flip: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(flip,k,t)
    var high=1 if t>=2 else 0
    var q=p[4]
    var out=List[BoundaryEdge]()
    for i in range(q-1,min(p[2],q+1+high)+1):
        _append(out,flip,k,t,i,0)
    for delta in [q+high,q+1+high]:
        for j in range(1,min(p[3],p[2]-delta)+1):
            _append(out,flip,k,t,j+delta,j)
    if k<=2 or(k==3 and high==1):
        _append(out,flip,k,t,p[2]+1,0)
    for j in range(max(1,k-2-high),k+1):
        _append(out,flip,k,t,p[2]+1,j)
    return out^


def verify_h5_child_packet(tables: SeedOverlapTables,flip: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(flip,k,t)
    if not h5_child_allowed(flip,k,t,edge.i,edge.j) or not in_h5_image(edge.target):
        raise Error("H5 occurrence/typed target refused")
    verify_member_edge(tables,-1,k,p[0],p[1],h5_child_source(flip),edge.i,edge.j,edge.target)


def h5_child_path(flip: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=_dimensions(flip,k,t)
    var base=h5_path(k,t)
    if flip==0:
        return base^
    var out=List[BoundaryEdge]()
    for edge in base:
        out.append(BoundaryEdge(edge.j,edge.i,reverse_label(edge.target)))
    return out^


def h5_child_rank(w: BoundaryLabel,k: Int,t: Int) raises -> Int:
    _=_parameters(-1,k,t)
    if w==BoundaryLabel(2,2,0,0,0):
        return 0
    if w==h5_child_source(0) or w==h5_child_source(1):
        return 3 if k==0 else 2
    var middle=BoundaryLabel(0,0,0,-3,4) if k==0 else (BoundaryLabel(0,0,0,-3,3) if k==1 else BoundaryLabel(2,0,0,-3,3))
    if w==middle or w==reverse_label(middle):
        return 2 if k==0 else 1
    var V=BoundaryLabel(2,0,0,1,-1)
    if k==0 and (w==V or w==reverse_label(V)):
        return 1
    raise Error("rank undefined outside selected H5 packet")


def verify_h5_child_path(tables: SeedOverlapTables,flip: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    var p=_dimensions(flip,k,t)
    var want=h5_child_path(flip,k,t)
    verify_h5_path(tables,k,t,h5_path(k,t)) # includes the actual H4 ancestry
    if len(steps)!=len(want):
        raise Error("incomplete oriented H5 path")
    var source=h5_child_source(flip)
    for z in range(len(steps)):
        var edge=steps[z]
        if edge.i!=want[z].i or edge.j!=want[z].j or edge.target!=want[z].target:
            raise Error("H5 path differs from intended occurrence packet")
        verify_member_edge(tables,-1,k,p[0],p[1],source,edge.i,edge.j,edge.target)
        if h5_child_rank(edge.target,k,t)>=h5_child_rank(source,k,t):
            raise Error("selected H5 rank did not decrease")
        source=edge.target
    if source!=BoundaryLabel(2,2,0,0,0):
        raise Error("wrong oriented H5 terminal")
