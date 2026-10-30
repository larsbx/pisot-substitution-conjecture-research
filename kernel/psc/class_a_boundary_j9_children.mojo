"""J9 complete stars and uniform selected exits, without an all-child claim."""
from finite_exact.checked_int import checked_add, checked_mul
from std.collections import Dict
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_j8_children import certify_j8_children, j8_star_interface, j8_exit_interface
from psc.class_a_boundary_e7_children import e7_source, verify_e7_steps
from psc.class_a_boundary_r4_children import r4_source, r4_path, _image, _transition
from psc.class_a_boundary_y4_children import _reverse_steps
from psc.class_a_boundary_e_children import _offset
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, _child, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def j9_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=6:raise Error("unknown J9/companion orientation")
    var base: List[BoundaryLabel]=[BoundaryLabel(2,0,1,2,-6),BoundaryLabel(0,2,-1,-4,7),BoundaryLabel(0,0,1,3,-6)]
    var w=base[kind//2]
    return reverse_label(w) if kind%2==1 else w


def j9_star_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=j8_star_interface(w,True)
    if old!=0:return old
    if include_new and (w==j9_source(0) or w==j9_source(1)):return 61
    return 0


def j9_exit_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=j8_exit_interface(w,True)
    if old!=0:return old
    if include_new:
        for kind in range(6):
            if w==j9_source(kind):return 61+kind//2
    return 0


def certify_j9_separator(corrupt: Bool=False) raises:
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var k=p[2].copy()
    var t=p[3].copy()
    var beta=_linear(qx_const(0),qx_const(1))
    var beta2=tp_mul(beta,beta)
    var f=_cubic(-1,n,p[1])
    # g4=beta*(alpha+4h-1); sign(g4)<0 at k>=2.
    var g4=tp_add(tp_sub(beta2,tp_scale(beta,qx_add(n,qx_const(3)))),_linear(qx_const(4),qx_const(0)))
    var want=_linear(qx_const(2),qx_sub(qx_const(1),k))
    if corrupt:want=tp_add(want,_linear(qx_const(1),qx_const(0)))
    _equal(tp_mod_monic(tp_mul(tp_add(beta,_linear(qx_const(1),qx_const(0))),g4),f),want)
    # beta*(2v-1)=t-k+3-alpha-4h, clearing a further positive beta.
    var q=tp_add(tp_sub(tp_scale(beta2,qx_const(2)),tp_scale(beta,qx_add(qx_add(n,n),qx_const(5)))),_linear(qx_const(2),qx_const(0)))
    var right=tp_add(tp_scale(beta2,qx_const(-1)),_linear(qx_const(-4),qx_add(qx_add(n,qx_sub(t,k)),qx_const(5))))
    _equal(tp_mod_monic(tp_mul(beta,q),f),tp_mod_monic(right,f))


def _expected(group: Int,n: QX,k: QX) -> List[QX]:
    if group==0:return [qx_const(-2),qx_const(-4),qx_sub(qx_sub(qx_const(5),n),k)]
    if group==1:return [qx_const(1),qx_const(3),qx_sub(k,qx_const(6))]
    return [qx_const(-1),qx_const(-3),qx_sub(qx_const(5),k)]


def certify_j9_children(corrupt: Bool=False) raises:
    certify_j8_children()
    certify_j9_separator()
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var k=p[2].copy()
    var t=p[3].copy()
    var beta=_linear(qx_const(0),qx_const(1))
    var beta2=tp_mul(beta,beta)
    var f=_cubic(-1,n,d)
    var ba=tp_sub(tp_sub(beta2,tp_scale(beta,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    for kind in range(6):
        var w=j9_source(kind)
        var base=_image(w,n,d)
        var want=_expected(kind//2,n,k)
        if kind%2==1:
            for z in range(3):want[z]=qx_neg(want[z])
        _equal3(base,want)
        var field=tp_add(tp_add(tp_scale(ba,qx_const(w.x)),tp_scale(bb,qx_const(w.c))),tp_scale(beta,qx_const(w.y)))
        var image=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(beta,base[2]))
        if corrupt:image=tp_add(image,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(tp_mul(beta,field),f),tp_mod_monic(image,f))
        if kind<2:
            var betaG=tp_add(tp_scale(beta2,qx_const(-2)),_linear(qx_const(-2),qx_sub(qx_add(n,qx_const(1)),k)))
            if kind==1:betaG=tp_scale(betaG,qx_const(-1))
            _equal(tp_mod_monic(image,f),tp_mod_monic(betaG,f))
            var R=qx_sub(n,qx_const(1)) if kind==0 else qx_add(n,d)
            var B=qx_add(n,d) if kind==0 else qx_sub(n,qx_const(1))
            for ri in [1,2]:
                for rj in [1,2]:
                    var top: List[QX]=[qx_const(0),qx_const(ri),qx_add(R,qx_const(1))]
                    var bottom: List[QX]=[qx_const(0),qx_const(rj),qx_add(B,qx_const(1))]
                    for tk in range(3):
                        for bk in range(3):
                            var got=symbolic_child(-1,w.top,w.bottom,_offset(w),tk,top[tk],bk,bottom[bk],_child(w.top,tk),_child(w.bottom,bk))
                            var pt=_prefix(w.top,tk,top[tk],-1,n,d)
                            var pb=_prefix(w.bottom,bk,bottom[bk],-1,n,d)
                            var expected=List[QX]()
                            for z in range(3):expected.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
                            _equal3(got,expected)
    for flip in range(2):
        var j=qx_add(qx_add(n,k),qx_const(3))
        _transition(n,d,j9_source(flip),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else j.copy(),RUN if flip==0 else FIRST,j.copy() if flip==0 else qx_const(0),j9_source(2+flip))
        _transition(n,d,j9_source(4+flip),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else qx_add(k,qx_const(1)),RUN if flip==0 else FIRST,qx_add(k,qx_const(1)) if flip==0 else qx_const(0),r4_source(10+flip))
        # k=0 ray: ordinal zero is true FIRST x, never RUN y.
        var nr=qx_add(t,qx_const(3))
        var dr=qx_add(qx_add(t,t),qx_const(5))
        _transition(nr,dr,j9_source(2+flip),FIRST,qx_const(0),FIRST,qx_const(0),j9_source(4+flip))
        # k=k'+1: k is now a real top RUN and reaches existing R(G5).
        var ns=qx_add(n,qx_const(1))
        var ds=qx_add(d,qx_const(1))
        var ks=qx_add(k,qx_const(1))
        _transition(ns,ds,j9_source(2+flip),RUN if flip==0 else FIRST,ks.copy() if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else ks.copy(),r4_source(11-flip))
        # E7 ancestry on t=t'+4 only.
        ns=qx_add(n,qx_const(4));ds=qx_add(d,qx_const(8))
        var i=qx_add(qx_add(ns,ns),qx_const(6))
        _transition(ns,ds,e7_source(flip),RUN if flip==0 else FIRST,i.copy() if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else i.copy(),j9_source(flip))
    print("CLASS_A_BOUNDARY_J9 two_complete_oriented_stars=true", "chamber_union_labels=34", "v_half_high=t>=k-2", "source_exit_k0=8", "source_exit_kpositive=7", "P9_exit_k0=7", "P9_exit_kpositive=6", "H9_exit=6", "all_direct_children_productivity_proved=false", "closed_carrier=false", "global_BH=false")


def _dimensions(kind: Int,k: Int,t: Int) raises -> Tuple[Int,Int,Int,Int]:
    _=j9_source(kind)
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,20)
    _=checked_add(checked_add(checked_add(p[0],p[0]),k),20)
    return(p[0],p[1],A,p[0]-1)


def j9_v_high(k: Int,t: Int) raises -> Bool:
    _=_dimensions(0,k,t)
    return t+2>=k


def j9_count(k: Int,t: Int) raises -> Int:
    var p=_dimensions(0,k,t)
    var m=t-k
    if m<=-3:return checked_add(checked_mul(4,t),9)
    if m == -2:return 2*p[0]-1
    if m == -1:return 2*p[0]+1
    return 2*p[0]+min(m,2)+2-(1 if k==0 else 0)


def j9_child_allowed(kind: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    if kind<0 or kind>=2:raise Error("only J9 has a new complete-star interface")
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var A=p[2]
    var R=p[3] if kind==0 else A
    var B=A if kind==0 else p[3]
    if i<0 or i>R+1 or j<0 or j>B+1:raise Error("nonexistent J9 occurrence")
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    var s=1 if j9_v_high(k,t) else 0
    if a==0:return b>=n+k+2+(1 if k==0 else 0) and b<=n+k+4+s
    if a>=1 and a<=p[3]:
        if b>=1 and b<=A:return b-a==n+k+3+s or b-a==n+k+4+s
        return b==A+1 and a>=2*t+2-s and a<=2*t+4
    if a==n:
        return (t-k>=-1 and t-k<=2) if b==A+1 else b>=2*n+k+4 and b<=2*n+k+5 and b<=A
    return False


def j9_image() raises -> List[BoundaryLabel]:
    var base=List[BoundaryLabel]()
    for r in range(6,10):base.append(BoundaryLabel(0,2,-1,-4,r))
    for r in range(8,11):base.append(BoundaryLabel(2,2,-2,-4,r))
    for r in range(7,11):base.append(BoundaryLabel(2,0,-2,-4,r))
    for r in [9,10]:base.append(BoundaryLabel(1,2,-2,-4,r))
    for r in range(7,11):base.append(BoundaryLabel(1,0,-2,-4,r))
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def in_j9_image(w: BoundaryLabel) raises -> Bool:
    var z=w if w.c<0 else reverse_label(w)
    if z.c != -4:return False
    if z.top==0 and z.bottom==2:return z.x == -1 and z.y>=6 and z.y<=9
    if z.x != -2:return False
    if z.top==2 and z.bottom==2:return z.y>=8 and z.y<=10
    if z.top==2 and z.bottom==0:return z.y>=7 and z.y<=10
    if z.top==1 and z.bottom==2:return z.y==9 or z.y==10
    return z.top==1 and z.bottom==0 and z.y>=7 and z.y<=10


def _append(mut out: List[BoundaryEdge],kind: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(kind,k,t)
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if not j9_child_allowed(kind,k,t,a,b):raise Error("synthesized J9 guard failed")
    var target=member_transport(-1,k,p[0],p[1],j9_source(kind),a,b)
    if not in_j9_image(target):raise Error("J9 target escaped image")
    out.append(BoundaryEdge(a,b,target))


def j9_child_star(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    if kind<0 or kind>=2:raise Error("no companion complete-star request")
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var A=p[2]
    var s=1 if j9_v_high(k,t) else 0
    var out=List[BoundaryEdge]()
    for j in range(n+k+2+(1 if k==0 else 0),n+k+5+s):_append(out,kind,k,t,0,j)
    for delta in [n+k+3+s,n+k+4+s]:
        for i in range(1,min(p[3],A-delta)+1):_append(out,kind,k,t,i,i+delta)
    for i in range(2*t+2-s,min(p[3],2*t+4)+1):_append(out,kind,k,t,i,A+1)
    for j in range(2*n+k+4,min(A,2*n+k+5)+1):_append(out,kind,k,t,n,j)
    if t-k>=-1 and t-k<=2:_append(out,kind,k,t,n,A+1)
    return out^


def verify_j9_packet(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not j9_child_allowed(kind,k,t,edge.i,edge.j) or not in_j9_image(edge.target):raise Error("J9 packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],j9_source(kind),edge.i,edge.j,edge.target)


def verify_j9_star(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edges: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    if len(edges)!=j9_count(k,t):raise Error("incomplete J9 indexed star")
    var stride=checked_add(p[2] if kind==0 else p[3],2)
    var seen=Dict[Int,Bool]()
    for edge in edges:
        verify_j9_packet(tables,kind,k,t,edge)
        var key=checked_add(checked_mul(edge.i,stride),edge.j)
        if key in seen:raise Error("duplicate J9 occurrence")
        seen[key]=True


def j9_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var out=List[BoundaryEdge]()
    var group=kind//2
    if group==0:
        out.append(BoundaryEdge(0,p[0]+k+3,j9_source(2)))
        var suffix=j9_path(2,k,t)
        for edge in suffix:out.append(edge)
    elif group==1:
        if k==0:
            out.append(BoundaryEdge(0,0,j9_source(4)))
            var suffix=j9_path(4,k,t)
            for edge in suffix:out.append(edge)
        else:
            out.append(BoundaryEdge(k,0,r4_source(11)))
            var suffix=r4_path(11,k,t)
            for edge in suffix:out.append(edge)
    else:
        out.append(BoundaryEdge(0,k+1,r4_source(10)))
        var suffix=r4_path(10,k,t)
        for edge in suffix:out.append(edge)
    if kind%2==1:_reverse_steps(out)
    return out^


def j9_registered_tail(w: BoundaryLabel,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=_dimensions(0,k,t)
    if not in_j9_image(w):raise Error("outside J9 image tail interface")
    for flip in range(2):
        if w==j9_source(2+flip):return j9_path(2+flip,k,t)
    raise Error("no registered uniform J9-image tail")


def verify_j9_path(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    verify_e7_steps(tables,j9_source(kind),k,t,steps,j9_path(kind,k,t))
