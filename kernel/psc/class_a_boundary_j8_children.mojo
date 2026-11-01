"""J8 complete stars and guarded completion after every actual first choice.

Conditional image/helper tails never become full-cone uniform interfaces.
"""
from finite_exact.checked_int import checked_add, checked_mul
from std.collections import Dict
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_d0_children import certify_d0_children, d0_star_interface, d0_exit_interface
from psc.class_a_boundary_e7_children import e7_source, verify_e7_steps
from psc.class_a_boundary_r4_children import r4_source, r4_path, _image, _transition
from psc.class_a_boundary_b4_children import b4_source, b4_path
from psc.class_a_boundary_h3_children import chain_source, chain_path
from psc.class_a_boundary_p_children import p_source, p_path
from psc.class_a_boundary_p3_children import p3_source, p3_path
from psc.class_a_boundary_e_children import eh_source, short_eh_path, _offset
from psc.class_a_boundary_y4_children import _reverse_steps
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, _child, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def j8_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=28:raise Error("unknown J8/companion orientation")
    var base: List[BoundaryLabel]=[
        BoundaryLabel(2,0,1,2,-5),   # J8, only new complete star
        BoundaryLabel(0,0,-1,-3,4),  # H8
        BoundaryLabel(0,2,0,-3,4),   # P8 local alias = reversed L
        BoundaryLabel(2,2,-1,-3,5),  # R8
        BoundaryLabel(2,2,-1,-3,6),  # S8
        BoundaryLabel(1,2,-1,-3,5),  # A8
        BoundaryLabel(1,2,-1,-3,6),  # B8
        BoundaryLabel(0,1,1,2,-5),   # C8
        BoundaryLabel(2,0,0,3,-5),   # Y8 local alias = reversed G5
        BoundaryLabel(1,1,1,2,-5),   # Q8
        BoundaryLabel(0,0,0,-3,5),   # W8
        BoundaryLabel(0,0,2,3,-6),   # Z8: path only k=0
        BoundaryLabel(1,1,1,2,-4),   # D8: path only k=1
        BoundaryLabel(1,2,-1,-3,7)]  # L8: source and path only k=0
    var w=base[kind//2]
    return reverse_label(w) if kind%2==1 else w


def j8_star_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=d0_star_interface(w,True)
    if old!=0:return old
    if include_new and (w==j8_source(0) or w==j8_source(1)):return 47
    return 0


def j8_exit_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=d0_exit_interface(w,True)
    if old!=0:return old
    if include_new:
        for kind in range(22):
            if w==j8_source(kind):return 47+kind//2
    return 0 # Z8/D8 have guarded tails; L8 is disjoint outside k=0


def certify_j8_separator(corrupt: Bool=False) raises:
    var p=chamber_parameters(-1)
    var beta=_linear(qx_const(0),qx_const(1))
    var g=tp_add(tp_sub(tp_mul(beta,beta),tp_scale(beta,qx_add(p[0],qx_const(3)))),_linear(qx_const(3),qx_const(0)))
    var want=_linear(qx_const(1),qx_neg(p[2]))
    if corrupt:want=tp_add(want,_linear(qx_const(1),qx_const(0)))
    _equal(tp_mod_monic(tp_mul(tp_add(beta,_linear(qx_const(1),qx_const(0))),g),_cubic(-1,p[0],p[1])),want)


def _expected(group: Int,n: QX,d: QX,k: QX,t: QX) raises -> List[QX]:
    if group==0 or group==7 or group==9:return [qx_const(-1),qx_const(-3),qx_sub(qx_const(4),k)]
    if group==1:return [qx_const(-1),qx_const(1),qx_neg(qx_add(d,qx_const(4)))]
    if group==2:return [qx_const(1),qx_const(1),qx_sub(n,qx_const(4))]
    if group==3 or group==5:return [qx_const(0),qx_const(2),qx_neg(qx_add(t,qx_const(7)))]
    if group==4 or group==6:return [qx_const(1),qx_const(3),qx_sub(k,qx_const(5))]
    if group==8:return [qx_const(-2),qx_const(-2),qx_sub(qx_const(5),qx_add(n,n))]
    if group==10:return [qx_const(2),qx_const(2),qx_sub(qx_add(n,n),qx_const(5))]
    if group==11:return [qx_const(1),qx_const(-3),qx_add(qx_sub(qx_add(d,d),n),qx_const(6))]
    if group==12:return [qx_const(0),qx_const(-2),qx_add(t,qx_const(6))]
    return [qx_const(2),qx_const(4),qx_sub(qx_sub(qx_add(qx_add(n,n),n),d),qx_const(7))]


def _tr(n: QX,d: QX,group: Int,flip: Int,tk: Int,i: QX,bk: Int,j: QX,target: BoundaryLabel) raises:
    if flip==0:_transition(n,d,j8_source(2*group),tk,i,bk,j,target)
    else:_transition(n,d,j8_source(2*group+1),bk,j,tk,i,reverse_label(target))


def certify_j8_children(corrupt: Bool=False) raises:
    certify_d0_children()
    certify_j8_separator()
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
    for flip in range(2):
        if j8_source(4+flip)!=chain_source(7-flip):raise Error("P8 must retain reversed L identity")
        if j8_source(16+flip)!=r4_source(11-flip):raise Error("Y8 must retain reversed G5 identity")
    for kind in range(28):
        var w=j8_source(kind)
        var base=_image(w,n,d)
        var want=_expected(kind//2,n,d,k,t)
        if kind%2==1:
            for z in range(3):want[z]=qx_neg(want[z])
        _equal3(base,want)
        var field=tp_add(tp_add(tp_scale(ba,qx_const(w.x)),tp_scale(bb,qx_const(w.c))),tp_scale(beta,qx_const(w.y)))
        var image=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(beta,base[2]))
        if corrupt:image=tp_add(image,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(tp_mul(beta,field),f),tp_mod_monic(image,f))
        if kind<2:
            var betaG=tp_sub(tp_scale(beta,qx_sub(qx_add(n,qx_const(1)),k)),tp_add(beta2,_linear(qx_const(2),qx_const(0))))
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
    # Disjoint exhaustive regions: (0,0), (0,t'+1), (1,t), (k'+2,t).
    for region in range(4):
        var ks=qx_const(0) if region<2 else (qx_const(1) if region==2 else qx_add(k,qx_const(2)))
        var ts=qx_const(0) if region==0 else (qx_add(t,qx_const(1)) if region==1 else t.copy())
        var ns=qx_add(qx_add(ks,ts),qx_const(3))
        var ds=qx_sub(qx_sub(qx_add(ns,ns),qx_const(1)),ks)
        var A=qx_add(ns,ds)
        for flip in range(2):
            _tr(ns,ds,0,flip,FIRST,qx_const(0),RUN,qx_const(2) if region<2 else ks.copy(),r4_source(10 if region<2 else 4))
            _tr(ns,ds,1,flip,FIRST,qx_const(0),LAST if region==0 else RUN,qx_add(ds,qx_const(4)),p3_source(5 if region==0 else 3))
            _tr(ns,ds,2,flip,RUN,qx_sub(ns,qx_const(2)),FIRST,qx_const(0),eh_source(3))
            _tr(ns,ds,3,flip,FIRST,qx_const(0),LAST if region<2 else RUN,ns.copy() if region<2 else qx_add(ts,qx_const(3)),j8_source(14) if region<2 else chain_source(5))
            _tr(ns,ds,4,flip,RUN,qx_add(ks,qx_const(1)),FIRST,qx_const(0),j8_source(16))
            if region<3:
                _tr(ns,ds,5,flip,FIRST,qx_const(0),LAST,ns.copy(),j8_source(18 if region<2 else 24))
            else:_tr(ns,ds,5,flip,RUN,qx_const(1),RUN,qx_add(ts,qx_const(4)),p_source(3))
            _tr(ns,ds,6,flip,RUN,qx_add(ks,qx_const(1)),FIRST,qx_const(0),j8_source(0))
            _tr(ns,ds,7,flip,FIRST,qx_const(0),RUN,qx_add(ks,qx_const(1)),b4_source(4))
            _tr(ns,ds,8,flip,FIRST,qx_const(0),RUN,qx_add(ns,ns),b4_source(4))
            _tr(ns,ds,9,flip,RUN,qx_const(1),RUN,qx_add(ks,qx_const(2)),j8_source(6))
            _tr(ns,ds,10,flip,RUN,qx_add(ns,ns),FIRST,qx_const(0),chain_source(2))
            if region<2:
                _tr(ns,ds,11,flip,LAST,qx_add(A,qx_const(1)),FIRST,qx_const(0),j8_source(20))
                _tr(ns,ds,13,flip,LAST,qx_add(ns,qx_const(1)),FIRST,qx_const(0),j8_source(22))
            if region==2:_tr(ns,ds,12,flip,RUN,qx_add(ts,qx_const(4)),RUN,qx_const(1),p_source(7))
    # E7 ancestry holds only on the shifted t>=3 cone.
    var ns=qx_add(n,qx_const(3))
    var ds=qx_add(d,qx_const(6))
    for flip in range(2):
        var i=qx_add(qx_add(ns,ns),qx_const(5))
        _transition(ns,ds,e7_source(flip),RUN if flip==0 else FIRST,i.copy() if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else i.copy(),j8_source(flip))
    print("CLASS_A_BOUNDARY_J8 two_complete_oriented_stars=true", "count=2n+3+[k=0]", "chamber_union_labels=18", "source_exit_k0=6", "source_exit_kpositive=4", "every_actual_child_tail_at_most_eight=true", "walk_bound=9", "conditional_L8_k0_only=true", "new_companion_stars=false", "closed_carrier=false", "global_BH=false")


def _dimensions(kind: Int,k: Int,t: Int) raises -> Tuple[Int,Int,Int,Int]:
    _=j8_source(kind)
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,20)
    return(p[0],p[1],A,p[0]-1)


def j8_child_allowed(kind: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    if kind<0 or kind>=2:raise Error("only J8 has a new complete-star interface")
    var p=_dimensions(kind,k,t)
    var R=p[3] if kind==0 else p[2]
    var B=p[2] if kind==0 else p[3]
    if i<0 or i>R+1 or j<0 or j>B+1:raise Error("nonexistent J8 occurrence")
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if a==0:return k==0 if b==0 else b>=max(1,k) and b<=k+2
    if a>=1 and a<=p[3]:return b>=1 and b<=p[2] and (b-a==k+1 or b-a==k+2)
    return a==p[0] and b>=p[0]+k+1 and b<=p[0]+k+2+(1 if k==0 else 0)


def j8_image() raises -> List[BoundaryLabel]:
    var base: List[BoundaryLabel]=[j8_source(2),r4_source(4),j8_source(4),r4_source(10),j8_source(6),j8_source(8),j8_source(10),j8_source(12),j8_source(26)]
    var out=List[BoundaryLabel]()
    for w in base:
        out.append(w)
        out.append(reverse_label(w))
    return out^


def in_j8_image(w: BoundaryLabel) raises -> Bool:
    var z=w if w.c<0 else reverse_label(w)
    if z.c != -3:return False
    if z.top==0 and z.bottom==0:return z.x == -1 and z.y==4
    if z.top==0 and z.bottom==2:return z.x==0 and z.y>=3 and z.y<=5
    if z.top==2 and z.bottom==2:return z.x == -1 and (z.y==5 or z.y==6)
    return z.top==1 and z.bottom==2 and z.x == -1 and z.y>=5 and z.y<=7


def _append(mut out: List[BoundaryEdge],kind: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(kind,k,t)
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if not j8_child_allowed(kind,k,t,a,b):raise Error("synthesized J8 guard failed")
    var target=member_transport(-1,k,p[0],p[1],j8_source(kind),a,b)
    if not in_j8_image(target):raise Error("J8 target escaped image")
    out.append(BoundaryEdge(a,b,target))


def j8_child_star(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    if kind<0 or kind>=2:raise Error("no companion complete-star request")
    var p=_dimensions(kind,k,t)
    var out=List[BoundaryEdge]()
    if k==0:_append(out,kind,k,t,0,0)
    for j in range(max(1,k),k+3):_append(out,kind,k,t,0,j)
    for delta in [k+1,k+2]:
        for i in range(1,p[0]):_append(out,kind,k,t,i,i+delta)
    for j in range(p[0]+k+1,p[0]+k+3+(1 if k==0 else 0)):_append(out,kind,k,t,p[0],j)
    return out^


def verify_j8_packet(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not j8_child_allowed(kind,k,t,edge.i,edge.j) or not in_j8_image(edge.target):raise Error("J8 packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],j8_source(kind),edge.i,edge.j,edge.target)


def verify_j8_star(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edges: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    if len(edges)!=2*p[0]+3+(1 if k==0 else 0):raise Error("incomplete J8 indexed star")
    var stride=checked_add(p[2] if kind==0 else p[3],2)
    var seen=Dict[Int,Bool]()
    for edge in edges:
        verify_j8_packet(tables,kind,k,t,edge)
        var key=checked_add(checked_mul(edge.i,stride),edge.j)
        if key in seen:raise Error("duplicate J8 occurrence")
        seen[key]=True


def _extend(mut out: List[BoundaryEdge],suffix: List[BoundaryEdge]):
    for edge in suffix:out.append(edge)


def j8_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var n=p[0]
    var d=p[1]
    var group=kind//2
    if (group==11 or group==13) and k!=0:raise Error("companion path is k=0-only")
    if group==12 and k!=1:raise Error("D8 path is k=1-only")
    var out=List[BoundaryEdge]()
    if group==0:
        out.append(BoundaryEdge(0,2 if k==0 else k,r4_source(10 if k==0 else 4)))
        _extend(out,r4_path(10 if k==0 else 4,k,t))
    elif group==1:
        out.append(BoundaryEdge(0,d+4,p3_source(5 if n==3 else 3)))
        _extend(out,p3_path(5 if n==3 else 3,k,t))
    elif group==2:
        return chain_path(7-kind%2,k,t)
    elif group==3:
        out.append(BoundaryEdge(0,n if k==0 else t+3,j8_source(14) if k==0 else chain_source(5)))
        _extend(out,j8_path(14,k,t) if k==0 else chain_path(5,k,t))
    elif group==4:
        out.append(BoundaryEdge(k+1,0,j8_source(16)))
        _extend(out,j8_path(16,k,t))
    elif group==5:
        if k<=1:
            out.append(BoundaryEdge(0,n,j8_source(18 if k==0 else 24)))
            _extend(out,j8_path(18 if k==0 else 24,k,t))
        else:
            out.append(BoundaryEdge(1,t+4,p_source(3)))
            _extend(out,p_path(3,k,t))
    elif group==6:
        out.append(BoundaryEdge(k+1,0,j8_source(0)))
        _extend(out,j8_path(0,k,t))
    elif group==7:
        out.append(BoundaryEdge(0,k+1,b4_source(4)))
        _extend(out,b4_path(4,k,t))
    elif group==8:
        return r4_path(11-kind%2,k,t)
    elif group==9:
        out.append(BoundaryEdge(1,k+2,j8_source(6)))
        _extend(out,j8_path(6,k,t))
    elif group==10:
        out.append(BoundaryEdge(2*n,0,chain_source(2)))
        _extend(out,chain_path(2,k,t))
    elif group==11:
        out.append(BoundaryEdge(p[2]+1,0,j8_source(20)))
        _extend(out,j8_path(20,k,t))
    elif group==12:
        out.append(BoundaryEdge(t+4,1,p_source(7)))
        _extend(out,p_path(7,k,t))
    else:
        out.append(BoundaryEdge(n+1,0,j8_source(22)))
        _extend(out,j8_path(22,k,t))
    if kind%2==1:_reverse_steps(out)
    return out^


def j8_child_tail(w: BoundaryLabel,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=_dimensions(0,k,t)
    if not in_j8_image(w):raise Error("outside J8-image tail interface")
    for flip in range(2):
        for group in [1,2,3,4,5,6,13]:
            if w==j8_source(2*group+flip):return j8_path(2*group+flip,k,t)
        if w==r4_source(4+flip):return r4_path(4+flip,k,t)
        if w==r4_source(10+flip):return r4_path(10+flip,k,t)
    raise Error("J8-image tail dispatch missed a label")


def j8_walk(kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    if not j8_child_allowed(kind,k,t,edge.i,edge.j) or member_transport(-1,k,p[0],p[1],j8_source(kind),edge.i,edge.j)!=edge.target:raise Error("wrong J8 first indexed packet")
    var out: List[BoundaryEdge]=[edge]
    _extend(out,j8_child_tail(edge.target,k,t))
    return out^


def verify_j8_path(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    verify_e7_steps(tables,j8_source(kind),k,t,steps,j8_path(kind,k,t))


def verify_j8_walk(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge,steps: List[BoundaryEdge]) raises:
    verify_j8_packet(tables,kind,k,t,edge)
    if len(steps)>9:raise Error("J8 first-choice walk exceeds nine edges")
    verify_e7_steps(tables,j8_source(kind),k,t,steps,j8_walk(kind,k,t,edge))
