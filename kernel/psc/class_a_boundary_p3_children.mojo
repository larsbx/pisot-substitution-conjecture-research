"""Complete actual P3 stars and typed exits, not forward closure or global BH."""
from finite_exact.checked_int import checked_add
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_f_children import certify_f_children, f_source
from psc.class_a_boundary_w_children import minus_seed_path, selected_path_label, selected_path_rank
from psc.class_a_boundary_e_children import _offset
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _cone_positive, _cone_nonnegative
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def p3_source(flip: Int) raises -> BoundaryLabel:
    if flip<0 or flip>1:
        raise Error("unknown P3 orientation")
    var w=BoundaryLabel(0,2,1,3,-4)
    return reverse_label(w) if flip==1 else w


def certify_p3_children(corrupt: Bool=False) raises:
    certify_f_children()
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var k=p[2].copy()
    var t=p[3].copy()
    var A=qx_add(n,d)
    var N=qx_sub(n,qx_const(1))
    var q=qx_add(d,qx_const(5))
    _cone_positive(qx_sub(q,qx_const(2)))
    _cone_nonnegative(qx_sub(A,qx_sub(q,qx_const(2)))) # n-3>=0
    var X=_linear(qx_const(0),qx_const(1))
    var X2=tp_mul(X,X)
    var f=_cubic(-1,n,d)
    var alpha=tp_sub(X,_linear(qx_add(n,qx_const(2)),qx_const(0)))
    # beta^2*theta=(t+1)*beta-2, theta=alpha-2/beta in (0,1).
    var raw=tp_sub(tp_mul(X2,alpha),tp_scale(X,qx_const(2)))
    var want=_linear(qx_const(-2),qx_add(t,qx_const(1)))
    if corrupt:
        want=tp_add(want,_linear(qx_const(1),qx_const(0)))
    _equal(tp_mod_monic(raw,f),want)
    _cone_positive(qx_add(t,qx_const(1)))
    # beta>n+2>=5 gives (t+1)*beta-2>0; theta<alpha<1.
    var ba=tp_sub(tp_sub(X2,tp_scale(X,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    for flip in range(2):
        var source=p3_source(flip)
        var base: List[QX]=[qx_const(1),qx_const(-1),qx_add(d,qx_const(4))]
        if flip==1:
            for z in range(3):base[z]=qx_neg(base[z])
        var field=tp_add(tp_add(tp_scale(ba,qx_const(source.x)),tp_scale(bb,qx_const(source.c))),tp_scale(X,qx_const(source.y)))
        var inflated=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(X,base[2]))
        _equal(tp_mod_monic(tp_mul(X,field),f),tp_mod_monic(inflated,f))
        var betaB=tp_add(X2,_linear(qx_const(-2),qx_add(qx_sub(d,n),qx_const(3))))
        if flip==1:betaB=tp_scale(betaB,qx_const(-1))
        _equal(tp_mod_monic(inflated,f),tp_mod_monic(betaB,f))
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
                        for z in range(3):target.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
                        _equal3(got,target)
        # Uniform actual E3 ancestry, including k=t=0.
        var parent=f_source(4+flip)
        var i=qx_add(A,qx_const(1)) if flip==0 else qx_sub(qx_sub(A,k),qx_const(1))
        var j=qx_sub(qx_sub(A,k),qx_const(1)) if flip==0 else qx_add(A,qx_const(1))
        _equal3(symbolic_child(-1,parent.top,parent.bottom,_offset(parent),
                              LAST if flip==0 else RUN,i,RUN if flip==0 else LAST,j,
                              source.top,source.bottom),_offset(source))
        # Uniform first exit into V; the existing seed suffix is V->W->Q->C.
        var target=selected_path_label(3)
        if flip==1:target=reverse_label(target)
        _equal3(symbolic_child(-1,source.top,source.bottom,_offset(source),
                              RUN if flip==0 else FIRST,qx_sub(q,qx_const(2)) if flip==0 else qx_const(0),
                              FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_sub(q,qx_const(2)),
                              target.top,target.bottom),_offset(target))
    # Short Q exit is legal on n>=4, the union of the k>=1 and t>=1 cones.
    for direction in range(2):
        var ns=qx_add(n,qx_const(1))
        var ds=qx_add(d,qx_const(1 if direction==0 else 2))
        var As=qx_add(ns,ds)
        var i=qx_add(ds,qx_const(4))
        var prefix=_prefix(0,RUN,i,-1,ns,ds)
        var base: List[QX]=[qx_const(1),qx_const(-1),qx_add(ds,qx_const(4))]
        var got=List[QX]()
        for z in range(3):got.append(qx_sub(base[z],prefix[z]))
        _equal3(got,_offset(selected_path_label(5)))
        _cone_nonnegative(qx_sub(As,i))
    print("CLASS_A_BOUNDARY_P3 two_complete_oriented_stars=true", "count_each=2n-3",
          "chamber_union_labels=26", "typed_exit_at_most_four=true", "global_closure=false", "BH=false")


def _dimensions(flip: Int,k: Int,t: Int) raises -> Tuple[Int,Int,Int,Int]:
    _=p3_source(flip)
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,12)
    return(p[0],p[1],A,p[0]-1)


def p3_child_allowed(flip: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    var p=_dimensions(flip,k,t)
    var R=p[2] if flip==0 else p[3]
    var B=p[3] if flip==0 else p[2]
    if i<0 or i>R+1 or j<0 or j>B+1:
        raise Error("nonexistent P3 occurrence")
    var a=j if flip==1 else i
    var b=i if flip==1 else j
    var q=p[1]+5
    if a>=1 and a<=p[2]:
        if b==0:return a>=q-2 and a<=q+1
        return b>=1 and b<=p[3] and (a-b==q or a-b==q+1)
    if a==p[2]+1:
        if b==0:return p[0]<=5
        return b>=max(1,p[0]-5) and b<=p[0]-2
    return False


def _in_base(w: BoundaryLabel) -> Bool:
    if w.x==0 and w.c==-1:
        return (w.top==2 and w.bottom==0 and w.y>=-1 and w.y<=2) or(w.top==0 and w.bottom==0 and w.y>=-1 and w.y<=1)
    return w.x==1 and w.c==-1 and ((w.top==2 and w.bottom==2 and w.y>=-2 and w.y<=-1) or(w.top==0 and w.bottom==2 and w.y>=-2 and w.y<=1))


def in_p3_image(w: BoundaryLabel) raises -> Bool:
    return _in_base(w) or _in_base(reverse_label(w))


def p3_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for y in range(-1,3):base.append(BoundaryLabel(2,0,0,-1,y))
    for y in [-2,-1]:base.append(BoundaryLabel(2,2,1,-1,y))
    for y in range(-1,2):base.append(BoundaryLabel(0,0,0,-1,y))
    for y in range(-2,2):base.append(BoundaryLabel(0,2,1,-1,y))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def _append(mut out: List[BoundaryEdge],flip: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(flip,k,t)
    var a=j if flip==1 else i
    var b=i if flip==1 else j
    if not p3_child_allowed(flip,k,t,a,b):raise Error("synthesized P3 guard failed")
    var target=member_transport(-1,k,p[0],p[1],p3_source(flip),a,b)
    if not in_p3_image(target):raise Error("P3 target escaped envelope")
    out.append(BoundaryEdge(a,b,target))


def p3_child_star(flip: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(flip,k,t)
    var n=p[0]
    var A=p[2]
    var q=p[1]+5
    var out=List[BoundaryEdge]()
    for i in range(q-2,min(A,q+1)+1):_append(out,flip,k,t,i,0)
    for delta in [q,q+1]:
        for j in range(1,min(p[3],A-delta)+1):_append(out,flip,k,t,j+delta,j)
    if n<=5:_append(out,flip,k,t,A+1,0)
    for j in range(max(1,n-5),n-1):_append(out,flip,k,t,A+1,j)
    return out^


def verify_p3_packet(tables: SeedOverlapTables,flip: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(flip,k,t)
    if not p3_child_allowed(flip,k,t,edge.i,edge.j) or not in_p3_image(edge.target):
        raise Error("P3 intended packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],p3_source(flip),edge.i,edge.j,edge.target)


def p3_path(flip: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(flip,k,t)
    var out=List[BoundaryEdge]()
    if p[0]>=4:
        out.append(BoundaryEdge(p[1]+4,0,selected_path_label(5)))
        out.append(BoundaryEdge(1,2,selected_path_label(6)))
    else:
        out.append(BoundaryEdge(p[1]+3,0,selected_path_label(3)))
        var suffix=minus_seed_path(k,t)
        for z in range(3,6):out.append(suffix[z])
    if flip==0:return out^
    var reversed=List[BoundaryEdge]()
    for edge in out:reversed.append(BoundaryEdge(edge.j,edge.i,reverse_label(edge.target)))
    return reversed^


def p3_rank(w: BoundaryLabel) raises -> Int:
    for flip in range(2):
        if w==p3_source(flip):return 4
        for stage in range(3,7):
            var target=selected_path_label(stage)
            if flip==1:target=reverse_label(target)
            if w==target:return selected_path_rank(selected_path_label(stage))
    raise Error("rank undefined outside selected P3 packet")


def verify_p3_path(tables: SeedOverlapTables,flip: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    var p=_dimensions(flip,k,t)
    var want=p3_path(flip,k,t)
    if len(steps)!=len(want):raise Error("incomplete P3 path")
    var w=p3_source(flip)
    for z in range(len(steps)):
        var edge=steps[z]
        if edge.i!=want[z].i or edge.j!=want[z].j or edge.target!=want[z].target:
            raise Error("different intended P3 path")
        verify_member_edge(tables,-1,k,p[0],p[1],w,edge.i,edge.j,edge.target)
        if p3_rank(edge.target)>=p3_rank(w):raise Error("selected P3 rank did not decrease")
        w=edge.target
    if w!=BoundaryLabel(2,2,0,0,0):raise Error("wrong P3 typed terminal")
