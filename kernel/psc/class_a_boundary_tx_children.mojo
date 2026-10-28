"""Complete T/X/Y0 stars and selected typed exits; retain the real T/X cycle."""
from finite_exact.checked_int import checked_add
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_p3_children import certify_p3_children, p3_source
from psc.class_a_boundary_w_children import local_source, local_child_allowed, local_child_star, X, selected_path_label
from psc.class_a_boundary_p_children import p_source, p_path
from psc.class_a_boundary_e_children import eh_source, _offset
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _cone_nonnegative
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def tx_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=6:raise Error("unknown T/X/Y0 orientation")
    var w=BoundaryLabel(0,2,1,-1,1)
    if kind//2==1:w=local_source(X)
    elif kind//2==2:w=BoundaryLabel(2,2,1,-1,-1)
    return reverse_label(w) if kind%2==1 else w


def _inflated(kind: Int,n: QX,d: QX,t: QX) -> List[QX]:
    var out: List[QX]=[qx_const(2),qx_const(0),qx_sub(qx_add(n,d),qx_const(1))]
    if kind//2==1:out=[qx_const(1),qx_const(-1),qx_add(d,qx_const(1))]
    elif kind//2==2:out=[qx_const(0),qx_const(-2),qx_add(t,qx_const(3))]
    if kind%2==1:
        for z in range(3):out[z]=qx_neg(out[z])
    return out^


def certify_tx_children(corrupt: Bool=False) raises:
    certify_p3_children() # inherited exact theta in (0,1), v<1 and h<1/5
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var t=p[3].copy()
    var k=p[2].copy()
    var A=qx_add(n,d)
    var N=qx_sub(n,qx_const(1))
    var beta=_linear(qx_const(0),qx_const(1))
    var beta2=tp_mul(beta,beta)
    var f=_cubic(-1,n,d)
    var ba=tp_sub(tp_sub(beta2,tp_scale(beta,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    for kind in range(6):
        var source=tx_source(kind)
        var base=_inflated(kind,n,d,t)
        var field=tp_add(tp_add(tp_scale(ba,qx_const(source.x)),tp_scale(bb,qx_const(source.c))),tp_scale(beta,qx_const(source.y)))
        var inflated=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(beta,base[2]))
        _equal(tp_mod_monic(tp_mul(beta,field),f),tp_mod_monic(inflated,f))
        var betaG=tp_add(tp_scale(beta2,qx_const(2)),_linear(qx_const(-2),qx_add(t,qx_const(1))))
        if kind//2==1:betaG=tp_add(beta2,_linear(qx_const(-2),qx_add(t,qx_const(2))))
        elif kind//2==2:betaG=_linear(qx_const(-2),qx_add(t,qx_const(1)))
        if kind%2==1:betaG=tp_scale(betaG,qx_const(-1))
        if corrupt:betaG=tp_add(betaG,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(inflated,f),tp_mod_monic(betaG,f))
        var R=N.copy() if source.top==2 else A.copy()
        var B=N.copy() if source.bottom==2 else A.copy()
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
                        for z in range(3):want.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
                        _equal3(got,want)
    # All new selected edges, ancestry and both genuine cycle edges.
    for flip in range(2):
        for step in range(7):
            var source=tx_source(0)
            var target=tx_source(2)
            var i=qx_add(A,qx_const(1))
            var j=qx_const(0)
            var tk=LAST
            var bk=FIRST
            if step==1:
                source=tx_source(2)
                target=selected_path_label(5)
                i=qx_add(d,qx_const(1))
                tk=RUN
            elif step==2:
                source=tx_source(4)
                target=p_source(7)
                i=qx_add(t,qx_const(1))
                j=qx_const(1)
                tk=RUN
                bk=RUN
            elif step==3:
                source=p3_source(0)
                target=tx_source(0)
                j=qx_sub(n,qx_const(2))
                bk=RUN
            elif step==4:
                source=tx_source(2)
                target=tx_source(0)
                j=qx_add(n,qx_const(1))
                bk=RUN
            elif step==5:
                source=tx_source(2)
                target=tx_source(4)
                i=qx_add(d,qx_const(3))
                j=qx_const(1)
                tk=RUN
                bk=RUN
            elif step==6:
                source=tx_source(4)
                target=BoundaryLabel(1,2,0,-2,2)
                i=n.copy()
                j=qx_add(k,qx_const(2))
                tk=LAST
                bk=RUN
            if flip==1:
                source=reverse_label(source)
                target=reverse_label(target)
                var old=i.copy()
                i=j.copy()
                j=old.copy()
                var oldkind=tk
                tk=bk
                bk=oldkind
            _equal3(symbolic_child(-1,source.top,source.bottom,_offset(source),tk,i,bk,j,target.top,target.bottom),_offset(target))
    _cone_nonnegative(qx_sub(A,qx_add(d,qx_const(3))))
    _cone_nonnegative(qx_sub(N,qx_add(t,qx_const(1))))
    print("CLASS_A_BOUNDARY_TX six_complete_oriented_stars=true", "T_has_exactly_one_child=true",
          "X_count=2n+3", "Y0_count=2k+8-minus-one-if-t0", "union_labels=42",
          "typed_exits_at_most_three=true", "real_T_X_cycle_with_exit=true", "closed_carrier=false", "BH=false")


def _dimensions(kind: Int,k: Int,t: Int) raises -> Tuple[Int,Int,Int,Int]:
    _=tx_source(kind)
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,12)
    return(p[0],p[1],A,p[0]-1)


def tx_child_allowed(kind: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    var p=_dimensions(kind,k,t)
    var w=tx_source(kind)
    var R=p[3] if w.top==2 else p[2]
    var B=p[3] if w.bottom==2 else p[2]
    if i<0 or i>R+1 or j<0 or j>B+1:raise Error("nonexistent T/X/Y0 occurrence")
    var a=j if kind%2==1 else i
    var b=i if kind%2==1 else j
    if kind//2==0:return a==p[2]+1 and b==0
    if kind//2==1:return local_child_allowed(X,k,t,a,b)
    if a==0:return b==0 and t<=1
    if a<=p[3]:
        if b==0:return a>=max(1,t-1) and a<=t+1
        return b>=1 and b<=p[3] and (a-b==t or a-b==t+1)
    if b==p[0]:return t==0
    return b>=k+2 and b<=min(p[3],k+3)


def _in_base(w: BoundaryLabel) -> Bool:
    if w==BoundaryLabel(0,0,1,0,-1):return True
    if w.c==-1:
        return (w.top==2 and w.bottom==0 and w.x==0 and w.y>=-1 and w.y<=2) or(w.top==2 and w.bottom==2 and w.x==1 and w.y>=-2 and w.y<=-1) or(w.top==0 and w.bottom==2 and w.x==1 and w.y>=-2 and w.y<=1)
    if w.c==-2:
        return (w.top==0 and w.bottom==0 and w.x==0 and w.y>=3 and w.y<=4) or(w.top==2 and w.bottom==0 and w.x==-1 and w.y>=3 and w.y<=5) or(w.top==2 and w.bottom==2 and w.x==0 and w.y>=2 and w.y<=3) or(w.top==1 and w.bottom==2 and w.x==0 and w.y>=2 and w.y<=3) or(w.top==1 and w.bottom==1 and w.x==0 and w.y==3)
    return False


def in_tx_image(w: BoundaryLabel) raises -> Bool:return _in_base(w) or _in_base(reverse_label(w))


def tx_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    base.append(local_source(X))
    for y in range(-1,3):base.append(BoundaryLabel(2,0,0,-1,y))
    for y in [-2,-1]:base.append(BoundaryLabel(2,2,1,-1,y))
    for y in range(-2,2):base.append(BoundaryLabel(0,2,1,-1,y))
    for y in [3,4]:base.append(BoundaryLabel(0,0,0,-2,y))
    for y in range(3,6):base.append(BoundaryLabel(2,0,-1,-2,y))
    for y in [2,3]:
        base.append(BoundaryLabel(2,2,0,-2,y))
        base.append(BoundaryLabel(1,2,0,-2,y))
    base.append(BoundaryLabel(1,1,0,-2,3))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def _orient(i: Int,j: Int,target: BoundaryLabel,flip: Int) raises -> BoundaryEdge:
    return BoundaryEdge(j,i,reverse_label(target)) if flip==1 else BoundaryEdge(i,j,target)


def _append(mut out: List[BoundaryEdge],kind: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(kind,k,t)
    var a=j if kind%2==1 else i
    var b=i if kind%2==1 else j
    if not tx_child_allowed(kind,k,t,a,b):raise Error("synthesized T/X/Y0 guard failed")
    var target=member_transport(-1,k,p[0],p[1],tx_source(kind),a,b)
    if not in_tx_image(target):raise Error("T/X/Y0 target escaped image")
    out.append(BoundaryEdge(a,b,target))


def tx_child_star(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var out=List[BoundaryEdge]()
    if kind//2==0:_append(out,kind,k,t,p[2]+1,0)
    elif kind//2==1:
        var old=local_child_star(X,k,t)
        for edge in old:
            var oriented=_orient(edge.i,edge.j,edge.target,kind%2)
            if not in_tx_image(oriented.target):raise Error("reused X target escaped T/X/Y0 image")
            out.append(oriented)
    else:
        if t<=1:_append(out,kind,k,t,0,0)
        for i in range(max(1,t-1),t+2):_append(out,kind,k,t,i,0)
        for delta in [t,t+1]:
            for j in range(1,p[3]-delta+1):_append(out,kind,k,t,j+delta,j)
        for j in range(k+2,min(p[3],k+3)+1):_append(out,kind,k,t,p[0],j)
        if t==0:_append(out,kind,k,t,p[0],p[0])
    return out^


def verify_tx_packet(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not tx_child_allowed(kind,k,t,edge.i,edge.j) or not in_tx_image(edge.target):raise Error("T/X/Y0 packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],tx_source(kind),edge.i,edge.j,edge.target)


def tx_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var flip=kind%2
    var out=List[BoundaryEdge]()
    if kind//2==0:out.append(_orient(p[2]+1,0,tx_source(2),flip))
    if kind//2<=1:
        out.append(_orient(p[1]+1,0,selected_path_label(5),flip))
        out.append(_orient(1,2,BoundaryLabel(2,2,0,0,0),flip))
    else:
        out.append(_orient(t+1,1,p_source(7),flip))
        var suffix=p_path(6 if flip==1 else 7,k,t)
        for edge in suffix:out.append(edge)
    return out^


def tx_rank(w: BoundaryLabel) raises -> Int:
    if w==BoundaryLabel(2,2,0,0,0):return 0
    for kind in range(6):
        if w==tx_source(kind):return 2 if kind//2==1 else 3
    for flip in range(2):
        var q=selected_path_label(5)
        if w==(reverse_label(q) if flip==1 else q):return 1
    if w==p_source(6) or w==p_source(7):return 2
    if w==eh_source(2) or w==eh_source(3):return 1
    raise Error("rank undefined outside selected T/X/Y0 packet")


def verify_tx_path(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    var want=tx_path(kind,k,t)
    if len(steps)!=len(want):raise Error("incomplete T/X/Y0 path")
    var w=tx_source(kind)
    for z in range(len(steps)):
        var edge=steps[z]
        if edge.i!=want[z].i or edge.j!=want[z].j or edge.target!=want[z].target:raise Error("different intended T/X/Y0 path")
        verify_member_edge(tables,-1,k,p[0],p[1],w,edge.i,edge.j,edge.target)
        if tx_rank(edge.target)>=tx_rank(w):raise Error("selected T/X/Y0 rank did not decrease")
        w=edge.target
    if w!=BoundaryLabel(2,2,0,0,0):raise Error("wrong T/X/Y0 typed terminal")
