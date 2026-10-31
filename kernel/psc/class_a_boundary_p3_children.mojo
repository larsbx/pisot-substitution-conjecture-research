"""Six P3/T/U oriented stars and at-most-two-step typed exits; no closure."""
from finite_exact.checked_int import checked_add
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_h5_children import certify_h5_children
from psc.class_a_boundary_e_children import _offset
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _cone_positive
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg, qx_mul, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def p3_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=6:
        raise Error("unknown oriented P3-family packet")
    var w=BoundaryLabel(0,2,1,3,-4)
    if kind//2==1:
        w=BoundaryLabel(2,0,0,-1,1)
    elif kind//2==2:
        w=BoundaryLabel(0,0,0,-1,1)
    return reverse_label(w) if kind%2==1 else w


def _inflated(kind: Int,d: QX) raises -> List[QX]:
    _=p3_source(kind)
    var out: List[QX]=[qx_const(1),qx_const(-1),qx_add(d,qx_const(4))]
    if kind//2!=0:
        out=[qx_const(0),qx_const(0),qx_const(-1)]
    if kind%2==1:
        for z in range(3):
            out[z]=qx_neg(out[z])
    return out^


def _first_identity(n: QX,d: QX,tk: Int,i: QX,target: BoundaryLabel) raises:
    if tk!=RUN and tk!=LAST:
        raise Error("P3 exit requires actual RUN or LAST")
    if target.top!=(2 if tk==RUN else 0) or target.bottom!=0:
        raise Error("P3 exit target types disagree with actual occurrence")
    var pt=_prefix(0,tk,i,-1,n,d)
    var pb=_prefix(2,FIRST,qx_const(0),-1,n,d)
    var base=_inflated(0,d)
    var out=List[QX]()
    for z in range(3):
        out.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
    _equal3(out,_offset(target))


def certify_p3_children(corrupt: Bool=False) raises:
    certify_h5_children() # h<1/5, 0<rho,w<1, inherited exact field bounds
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var t=p[3].copy()
    var A=qx_add(n,d)
    var N=qx_sub(n,qx_const(1))
    var X=_linear(qx_const(0),qx_const(1))
    var X2=tp_mul(X,X)
    var f=_cubic(-1,n,d)
    var ba=tp_sub(tp_sub(X2,tp_scale(X,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    # beta^2*zeta=(t+1)*beta-2, zeta=alpha-2/beta.
    var alpha=tp_sub(X,_linear(qx_add(n,qx_const(2)),qx_const(0)))
    var lhs=tp_sub(tp_mul(X2,alpha),tp_scale(X,qx_const(2)))
    _equal(tp_mod_monic(lhs,f),_linear(qx_const(-2),qx_add(t,qx_const(1))))
    _cone_positive(qx_sub(qx_mul(qx_add(t,qx_const(1)),qx_add(n,qx_const(2))),qx_const(2)))
    for kind in range(6):
        var w=p3_source(kind)
        var base=_inflated(kind,d)
        var field=tp_add(tp_add(tp_scale(ba,qx_const(w.x)),tp_scale(bb,qx_const(w.c))),tp_scale(X,qx_const(w.y)))
        var target=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(X,base[2]))
        if corrupt:
            target=tp_add(target,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(tp_mul(X,field),f),tp_mod_monic(target,f))
        var betaG=tp_add(X2,_linear(qx_const(-2),qx_add(qx_sub(d,n),qx_const(3))))
        if kind//2!=0:
            betaG=tp_scale(X,qx_const(-1))
        if kind%2==1:
            betaG=tp_scale(betaG,qx_const(-1))
        _equal(tp_mod_monic(target,f),tp_mod_monic(betaG,f))
        var R=A.copy() if w.top==0 else N.copy()
        var B=A.copy() if w.bottom==0 else N.copy()
        for ri in [1,2]:
            for rj in [1,2]:
                var top: List[QX]=[qx_const(0),qx_const(ri),qx_add(R,qx_const(1))]
                var bottom: List[QX]=[qx_const(0),qx_const(rj),qx_add(B,qx_const(1))]
                for tk in range(3):
                    for bk in range(3):
                        var ct=2 if tk==RUN else (1 if tk==LAST and w.top==2 else 0)
                        var cb=2 if bk==RUN else (1 if bk==LAST and w.bottom==2 else 0)
                        var got=symbolic_child(-1,w.top,w.bottom,_offset(w),tk,top[tk],bk,bottom[bk],ct,cb)
                        var pt=_prefix(w.top,tk,top[tk],-1,n,d)
                        var pb=_prefix(w.bottom,bk,bottom[bk],-1,n,d)
                        var want=List[QX]()
                        for z in range(3):
                            want.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
                        _equal3(got,want)
        if kind//2!=0:
            var i=qx_const(2 if kind%2==1 else 1)
            var j=qx_const(1 if kind%2==1 else 2)
            _equal3(symbolic_child(-1,w.top,w.bottom,_offset(w),RUN,i,RUN,j,2,2),_offset(BoundaryLabel(2,2,0,0,0)))
    # n>=4 is covered by k=k'+1 or t=t'+1, with true RUN indices.
    for dk in [0,1]:
        var ns=qx_add(n,qx_const(1))
        var ds=qx_add(d,qx_const(2-dk))
        _first_identity(ns,ds,RUN,qx_add(ds,qx_const(4)),p3_source(2))
    # Sole n=3 member k=t=0: use LAST, never invent a RUN d+4.
    _first_identity(qx_const(3),qx_const(5),LAST,qx_const(9),p3_source(4))
    # The actual E3 ancestry is cone-legal throughout.
    var e3=BoundaryLabel(0,0,-1,0,3)
    _equal3(symbolic_child(-1,0,0,_offset(e3),LAST,qx_add(A,qx_const(1)),RUN,qx_sub(qx_sub(A,p[2]),qx_const(1)),0,2),_offset(p3_source(0)))
    print("CLASS_A_BOUNDARY_P3 six_complete_oriented_stars=true", "chamber_union_labels=37", "typed_exits_at_most_two=true", "global_closure=false", "BH=false")


def _dimensions(kind: Int,k: Int,t: Int) raises -> Tuple[Int,Int,Int,Int]:
    _=p3_source(kind)
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,12)
    return(p[0],p[1],A,p[0]-1)


def p3_child_allowed(kind: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    var p=_dimensions(kind,k,t)
    var w=p3_source(kind)
    var R=p[2] if w.top==0 else p[3]
    var B=p[2] if w.bottom==0 else p[3]
    if i<0 or i>R+1 or j<0 or j>B+1:
        raise Error("nonexistent P3-family occurrence")
    var a=j if kind%2==1 else i
    var b=i if kind%2==1 else j
    var n=p[0]
    var d=p[1]
    var A=p[2]
    var N=p[3]
    if kind//2==0:
        if a>=1 and a<=A:
            if b==0:
                return a>=d+3 and a<=d+6
            return b>=1 and b<=N and (a-b==d+5 or a-b==d+6)
        if a==A+1:
            return n<=5 if b==0 else b>=max(1,n-5) and b<=n-2
        return False
    if a==0:
        return b==0 or b==1
    var run=N if kind//2==1 else A
    if a>=1 and a<=run:
        return (b>=1 and b<=A and b==a+1) or(kind//2==2 and a==A and b==A+1)
    return (b>=n+1 and b<=n+2) if kind//2==1 else b==A+1


def p3_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for y in range(-1,3):
        base.append(BoundaryLabel(2,0,0,-1,y))
    for y in [-2,-1]:
        base.append(BoundaryLabel(2,2,1,-1,y))
    for y in [-1,0,1]:
        base.append(BoundaryLabel(0,0,0,-1,y))
    for y in range(-2,2):
        base.append(BoundaryLabel(0,2,1,-1,y))
    base.append(BoundaryLabel(0,0,0,0,-1))
    base.append(BoundaryLabel(0,2,1,0,-1))
    base.append(BoundaryLabel(1,2,0,0,0))
    base.append(BoundaryLabel(1,2,0,0,1))
    base.append(BoundaryLabel(2,0,0,0,0))
    var out=List[BoundaryLabel]()
    out.append(BoundaryLabel(2,2,0,0,0))
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def in_p3_image(w: BoundaryLabel) raises -> Bool:
    var z=w if w.c<=0 else reverse_label(w)
    if z.c==-1:
        if z.top==2 and z.bottom==0:
            return z.x==0 and z.y>=-1 and z.y<=2
        if z.top==2 and z.bottom==2:
            return z.x==1 and z.y>=-2 and z.y<=-1
        if z.top==0 and z.bottom==0:
            return z.x==0 and z.y>=-1 and z.y<=1
        return z.top==0 and z.bottom==2 and z.x==1 and z.y>=-2 and z.y<=1
    if z.c!=0:
        return False
    for flip in range(2):
        z=w if flip==0 else reverse_label(w)
        if z.x==0 and ((z.top==0 and z.bottom==0 and z.y==-1) or(z.top==1 and z.bottom==2 and z.y>=0 and z.y<=1) or(z.top==2 and z.bottom==0 and z.y==0) or(z.top==2 and z.bottom==2 and z.y==0)):
            return True
        if z==BoundaryLabel(0,2,1,0,-1):
            return True
    return False


def _append(mut out: List[BoundaryEdge],kind: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(kind,k,t)
    var a=j if kind%2==1 else i
    var b=i if kind%2==1 else j
    if not p3_child_allowed(kind,k,t,a,b):
        raise Error("synthesized P3-family guard failed")
    var target=member_transport(-1,k,p[0],p[1],p3_source(kind),a,b)
    if not in_p3_image(target):
        raise Error("P3-family target escaped envelope")
    out.append(BoundaryEdge(a,b,target))


def p3_child_star(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var d=p[1]
    var A=p[2]
    var N=p[3]
    var out=List[BoundaryEdge]()
    if kind//2==0:
        for i in range(d+3,min(A,d+6)+1):
            _append(out,kind,k,t,i,0)
        for delta in [d+5,d+6]:
            for j in range(1,min(N,A-delta)+1):
                _append(out,kind,k,t,j+delta,j)
        if n<=5:
            _append(out,kind,k,t,A+1,0)
        for j in range(max(1,n-5),n-1):
            _append(out,kind,k,t,A+1,j)
    else:
        var R=N if kind//2==1 else A
        _append(out,kind,k,t,0,0)
        _append(out,kind,k,t,0,1)
        for i in range(1,min(R,A-1)+1):
            _append(out,kind,k,t,i,i+1)
        if kind//2==1:
            for j in [n+1,n+2]:
                _append(out,kind,k,t,n,j)
        else:
            _append(out,kind,k,t,A,A+1)
            _append(out,kind,k,t,A+1,A+1)
    return out^


def verify_p3_packet(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not p3_child_allowed(kind,k,t,edge.i,edge.j) or not in_p3_image(edge.target):
        raise Error("P3-family packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],p3_source(kind),edge.i,edge.j,edge.target)


def p3_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var out=List[BoundaryEdge]()
    var flip=kind%2
    if kind//2==0:
        var i=p[2]+1 if p[0]==3 else p[1]+4
        var w=p3_source(4 if p[0]==3 else 2)
        out.append(BoundaryEdge(0 if flip==1 else i,i if flip==1 else 0,reverse_label(w) if flip==1 else w))
    out.append(BoundaryEdge(2 if flip==1 else 1,1 if flip==1 else 2,BoundaryLabel(2,2,0,0,0)))
    return out^


def verify_p3_path(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    var want=p3_path(kind,k,t)
    if len(steps)!=len(want):
        raise Error("incomplete P3-family path")
    var w=p3_source(kind)
    for z in range(len(steps)):
        var edge=steps[z]
        if edge.i!=want[z].i or edge.j!=want[z].j or edge.target!=want[z].target:
            raise Error("P3-family intended path mismatch")
        verify_member_edge(tables,-1,k,p[0],p[1],w,edge.i,edge.j,edge.target)
        w=edge.target
    if w!=BoundaryLabel(2,2,0,0,0):
        raise Error("wrong P3-family typed terminal")
