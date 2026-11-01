"""Complete D5 stars and typed completions through every indexed first choice.

Composes R5/B5 registries; x/x zero is a typed terminal, not a new full star.
"""
from finite_exact.checked_int import checked_add, checked_mul
from std.collections import Dict
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_r5_children import certify_r5_children, r5_star_interface, r5_exit_interface
from psc.class_a_boundary_b5_children import certify_b5_children, b5_star_interface, b5_exit_interface
from psc.class_a_boundary_y4_children import y4_source, y4_path, _seed_suffix, _reverse_steps, _verify_steps
from psc.class_a_boundary_r4_children import _image, _transition
from psc.class_a_boundary_e_children import _offset
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, _child, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _cone_nonnegative
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def d5_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>=9:raise Error("unknown D5/companion orientation")
    var w=BoundaryLabel(0,1,1,-1,0)
    if kind//2==1:w=BoundaryLabel(2,1,0,-1,1) # D6, selected exit only
    elif kind//2==2:w=BoundaryLabel(2,1,0,-1,2) # D7, selected exit only
    elif kind//2==3:w=BoundaryLabel(1,1,0,1,-1) # C6, selected exit only
    elif kind==8:w=BoundaryLabel(0,0,0,0,0) # X0, self-reverse typed terminal
    return reverse_label(w) if kind%2==1 else w


def d5_candidate(include_d5: Bool=False) raises -> List[BoundaryLabel]:
    var out=enlarged_candidate(True)
    if include_d5:
        out.append(d5_source(0))
        out.append(d5_source(1))
    return out^


def d5_star_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    # A positive value binds a complete nonterminal star OR an explicit terminal.
    var old=r5_star_interface(w,True)
    if old==0:old=b5_star_interface(w,True)
    if old!=0:return old
    if include_new:
        if w==d5_source(0) or w==d5_source(1):return 30
        if w==d5_source(8):return 39 # terminal only; no X0 complete-star claim
    return 0


def d5_exit_interface(w: BoundaryLabel,include_new: Bool=False) raises -> Int:
    var old=r5_exit_interface(w)
    if old==0:old=b5_exit_interface(w,True)
    if old!=0:return old
    if include_new:
        if w==d5_source(8):return 39
        for group in [1,2,3]:
            if w==d5_source(2*group) or w==d5_source(2*group+1):return 39+group
    return 0


def certify_d5_children(corrupt: Bool=False) raises:
    certify_r5_children()
    certify_b5_children() # retain both proof branches, including finite E7 scope
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var A=qx_add(n,d)
    _cone_nonnegative(qx_sub(n,qx_const(3)))
    _cone_nonnegative(qx_sub(d,qx_const(2)))
    var beta=_linear(qx_const(0),qx_const(1))
    var beta2=tp_mul(beta,beta)
    var f=_cubic(-1,n,d)
    var ba=tp_sub(tp_sub(beta2,tp_scale(beta,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    for kind in range(9):
        var w=d5_source(kind)
        var base=_image(w,n,d)
        var expected: List[QX]=[qx_const(1),qx_const(-1),d.copy()]
        if kind//2==1:expected=[qx_const(0),qx_const(0),qx_const(-1)]
        elif kind//2==2:expected=[qx_const(1),qx_const(1),qx_sub(n,qx_const(2))]
        elif kind//2==3:expected=[qx_const(0),qx_const(0),qx_const(1)]
        elif kind==8:expected=[qx_const(0),qx_const(0),qx_const(0)]
        if kind%2==1:
            for z in range(3):expected[z]=qx_neg(expected[z])
        _equal3(base,expected)
        var field=tp_add(tp_add(tp_scale(ba,qx_const(w.x)),tp_scale(bb,qx_const(w.c))),tp_scale(beta,qx_const(w.y)))
        var image=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(beta,base[2]))
        if corrupt:image=tp_add(image,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(tp_mul(beta,field),f),tp_mod_monic(image,f))
        if kind<2:
            var betaG=tp_add(beta2,_linear(qx_const(-2),qx_sub(qx_sub(d,n),qx_const(1))))
            if kind==1:betaG=tp_scale(betaG,qx_const(-1))
            _equal(tp_mod_monic(image,f),tp_mod_monic(betaG,f))
            var R=A.copy() if kind==0 else n.copy()
            var B=n.copy() if kind==0 else A.copy()
            for ri in [1,2]:
                for rj in [1,2]:
                    var top=[qx_const(0),qx_const(ri),qx_add(R,qx_const(1))]
                    var bottom=[qx_const(0),qx_const(rj),qx_add(B,qx_const(1))]
                    for tk in range(3):
                        for bk in range(3):
                            var got=symbolic_child(-1,w.top,w.bottom,_offset(w),tk,top[tk],bk,bottom[bk],_child(w.top,tk),_child(w.bottom,bk))
                            var pt=_prefix(w.top,tk,top[tk],-1,n,d)
                            var pb=_prefix(w.bottom,bk,bottom[bk],-1,n,d)
                            var want=List[QX]()
                            for z in range(3):want.append(qx_add(base[z],qx_sub(pb[z],pt[z])))
                            _equal3(got,want)
    for flip in range(2):
        _transition(n,d,y4_source(flip),LAST,qx_add(A.copy() if flip==0 else qx_sub(n,qx_const(1)),qx_const(1)),LAST,qx_add(qx_sub(n,qx_const(1)) if flip==0 else A.copy(),qx_const(1)),d5_source(flip))
        for r in [1,2]:
            var i=qx_add(d,qx_const(1-r))
            _transition(n,d,d5_source(flip),RUN if flip==0 else FIRST,i.copy() if flip==0 else qx_const(0),FIRST if flip==0 else RUN,qx_const(0) if flip==0 else i.copy(),d5_source(2*r+flip))
        _transition(n,d,d5_source(flip),RUN,qx_add(d,qx_const(1)) if flip==0 else qx_const(1),RUN,qx_const(1) if flip==0 else qx_add(d,qx_const(1)),BoundaryLabel(2,2,0,0,0))
        _transition(n,d,d5_source(flip),LAST,qx_add(A.copy() if flip==0 else n.copy(),qx_const(1)),LAST,qx_add(n.copy() if flip==0 else A.copy(),qx_const(1)),d5_source(8))
        var t1=BoundaryLabel(2,2,-1,1,1)
        _transition(n,d,d5_source(2+flip),RUN,qx_const(1 if flip==0 else 3),RUN,qx_const(3 if flip==0 else 1),reverse_label(t1) if flip==1 else t1)
        _transition(n,d,d5_source(4+flip),LAST if flip==0 else FIRST,n.copy() if flip==0 else qx_const(0),FIRST if flip==0 else LAST,qx_const(0) if flip==0 else n.copy(),d5_source(6+flip))
        _transition(n,d,d5_source(6+flip),RUN,qx_const(2 if flip==0 else 1),RUN,qx_const(1 if flip==0 else 2),BoundaryLabel(2,2,0,0,0))
    _transition(n,d,d5_source(8),RUN,qx_const(1),RUN,qx_const(1),BoundaryLabel(2,2,0,0,0))
    print("CLASS_A_BOUNDARY_D5 two_complete_oriented_stars=true", "count=n+3", "union_labels=6", "source_exit_one=true", "all_first_choice_walks_at_most_seven=true", "two_typed_terminals=true", "Y4_image_all_stars_registered=true", "closed_carrier=false", "global_BH=false")


def _dimensions(kind: Int,k: Int,t: Int) raises -> Tuple[Int,Int,Int]:
    _=d5_source(kind)
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,12)
    return(p[0],p[1],A)


def d5_child_allowed(kind: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    if kind<0 or kind>=2:raise Error("new complete stars only cover D5 orientations")
    var p=_dimensions(kind,k,t)
    var R=p[2] if kind==0 else p[0]
    var B=p[0] if kind==0 else p[2]
    if i<0 or i>R+1 or j<0 or j>B+1:raise Error("nonexistent D5 occurrence")
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if a>=1 and a<=p[2]:
        if b==0:return a==p[1]-1 or a==p[1]
        return b>=1 and b<=p[0] and a-b==p[1]
    return a==p[2]+1 and b==p[0]+1


def d5_image() raises -> List[BoundaryLabel]:
    return [BoundaryLabel(2,2,0,0,0),d5_source(8),d5_source(2),d5_source(3),d5_source(4),d5_source(5)]


def in_d5_image(w: BoundaryLabel) raises -> Bool:
    if w==BoundaryLabel(2,2,0,0,0) or w==d5_source(8):return True
    var z=w if w.c<0 else reverse_label(w)
    return z.top==2 and z.bottom==1 and z.x==0 and z.c==-1 and (z.y==1 or z.y==2)


def _append(mut out: List[BoundaryEdge],kind: Int,k: Int,t: Int,i: Int,j: Int) raises:
    var p=_dimensions(kind,k,t)
    var a=i if kind==0 else j
    var b=j if kind==0 else i
    if not d5_child_allowed(kind,k,t,a,b):raise Error("synthesized D5 guard failed")
    var target=member_transport(-1,k,p[0],p[1],d5_source(kind),a,b)
    if not in_d5_image(target):raise Error("D5 target escaped exact image")
    out.append(BoundaryEdge(a,b,target))


def d5_child_star(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    if kind<0 or kind>=2:raise Error("no new companion complete-star certificate")
    var p=_dimensions(kind,k,t)
    var out=List[BoundaryEdge]()
    for i in [p[1]-1,p[1]]:_append(out,kind,k,t,i,0)
    for j in range(1,p[0]+1):_append(out,kind,k,t,j+p[1],j)
    _append(out,kind,k,t,p[2]+1,p[0]+1)
    return out^


def verify_d5_packet(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not d5_child_allowed(kind,k,t,edge.i,edge.j) or not in_d5_image(edge.target):raise Error("D5 packet refused")
    verify_member_edge(tables,-1,k,p[0],p[1],d5_source(kind),edge.i,edge.j,edge.target)


def verify_d5_star(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edges: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    if kind>=2 or len(edges)!=p[0]+3:raise Error("incomplete or unsupported D5 star")
    var stride=checked_add(p[0] if kind==0 else p[2],2)
    var seen=Dict[Int,Bool]()
    for edge in edges:
        verify_d5_packet(tables,kind,k,t,edge)
        var key=checked_add(checked_mul(edge.i,stride),edge.j)
        if key in seen:raise Error("duplicate D5 occurrence")
        seen[key]=True


def d5_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    if kind<2:return y4_path(4+kind,k,t)
    var out=List[BoundaryEdge]()
    if kind//2==1:
        out.append(BoundaryEdge(1,3,BoundaryLabel(2,2,-1,1,1)))
        var suffix=_seed_suffix(1,0,k,t)
        for edge in suffix:out.append(edge)
    elif kind//2==2:
        out.append(BoundaryEdge(p[0],0,d5_source(6)))
        out.append(BoundaryEdge(2,1,BoundaryLabel(2,2,0,0,0)))
    elif kind//2==3:out.append(BoundaryEdge(2,1,BoundaryLabel(2,2,0,0,0)))
    else:out.append(BoundaryEdge(1,1,BoundaryLabel(2,2,0,0,0)))
    if kind%2==1:_reverse_steps(out)
    return out^


def d5_child_tail(w: BoundaryLabel,k: Int,t: Int) raises -> List[BoundaryEdge]:
    _=_dimensions(0,k,t)
    if not in_d5_image(w):raise Error("unknown D5-image tail source")
    if w==BoundaryLabel(2,2,0,0,0):return List[BoundaryEdge]()
    for kind in [2,3,4,5,8]:
        if w==d5_source(kind):return d5_path(kind,k,t)
    raise Error("D5 complete tail dispatch missed a label")


def d5_walk(kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    if not d5_child_allowed(kind,k,t,edge.i,edge.j) or member_transport(-1,k,p[0],p[1],d5_source(kind),edge.i,edge.j)!=edge.target:raise Error("wrong D5 first-choice packet")
    var out: List[BoundaryEdge]=[edge]
    var suffix=d5_child_tail(edge.target,k,t)
    for step in suffix:out.append(step)
    return out^


def verify_d5_path(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    _=_dimensions(kind,k,t)
    _verify_steps(tables,d5_source(kind),k,t,steps,d5_path(kind,k,t))


def verify_d5_walk(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge,steps: List[BoundaryEdge]) raises:
    verify_d5_packet(tables,kind,k,t,edge)
    if len(steps)>7:raise Error("D5 first-choice walk exceeded seven edges")
    _verify_steps(tables,d5_source(kind),k,t,steps,d5_walk(kind,k,t,edge))
