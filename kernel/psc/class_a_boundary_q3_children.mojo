"""Complete two oriented Q3 stars, singleton X child, five-edge typed exit.

Q3->X->Q3 is an actual cycle, not an all-edge descent or global closure.
Exact nine-kind guard proof: docs/class-a-boundary-q3-carrier-2026-10-28.md.
"""
from finite_exact.checked_int import checked_add
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_p3_children import certify_p3_children, p3_source
from psc.class_a_boundary_w_children import certify_w_children, local_source, X, selected_path_label, typed_coincidence
from psc.class_a_boundary_e_children import _offset
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_next_first import _linear, _cubic, _equal
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, _prefix, FIRST, RUN, LAST
from psc.class_a_boundary_signs import chamber_parameters, _cone_positive
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_neg, tp_add, tp_sub, tp_mul, tp_scale, tp_mod_monic
from psc.overlap_seed_patch import SeedOverlapTables


def q3_source(kind: Int) raises -> BoundaryLabel:
    if kind<0 or kind>1:
        raise Error("unknown Q3 orientation")
    var w=BoundaryLabel(0,2,1,-1,1)
    return reverse_label(w) if kind==1 else w


def q3_target(kind: Int) raises -> BoundaryLabel:
    _=q3_source(kind)
    var w=local_source(X)
    return reverse_label(w) if kind==1 else w


def _inflated(kind: Int,A: QX) raises -> List[QX]:
    _=q3_source(kind)
    var out: List[QX]=[qx_const(2),qx_const(0),qx_sub(A,qx_const(1))]
    if kind==1:
        for z in range(3):
            out[z]=qx_neg(out[z])
    return out^


def _stage(stage: Int) raises -> BoundaryLabel:
    if stage==0:
        return q3_source(0)
    if stage==1:
        return q3_target(0)
    if stage>=2 and stage<=5:
        return selected_path_label(stage+1)
    raise Error("outside selected Q3 path")


def certify_q3_children(corrupt: Bool=False) raises:
    certify_p3_children() # inherited exact h,rho,zeta signs and P3 star
    certify_w_children() # established X star and V/W/Q selected suffix
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var A=qx_add(n,d)
    var N=qx_sub(n,qx_const(1))
    _cone_positive(qx_sub(n,qx_const(2))) # P3->Q3 bottom run n-2>=1
    _cone_positive(qx_sub(A,qx_add(n,qx_const(1)))) # real return run n+1<=A
    # Nine-kind strict-guard reductions, after i<=A,j>=1 and a=2+rho.
    # These are the constant terms of the excluded upper-margin violations
    # FF,FR,FL,RF,RR,RL,LR,LL and the two included LF margins.
    # The omitted rho coefficients are respectively 1,2,2,1,2,2,1,1,2,0,
    # all nonnegative; inherited rho>0 makes each displayed bound strict.
    for margin in [qx_add(A,qx_const(1)),qx_add(A,qx_const(3)),
                   qx_add(qx_add(A,N),qx_const(3)),qx_const(1),
                   qx_const(3),qx_add(N,qx_const(3)),qx_const(1),
                   qx_add(N,qx_const(1)),qx_const(3),qx_const(1)]:
        _cone_positive(margin)
    var beta=_linear(qx_const(0),qx_const(1))
    var beta2=tp_mul(beta,beta)
    var f=_cubic(-1,n,d)
    var ba=tp_sub(tp_sub(beta2,tp_scale(beta,n)),_linear(qx_const(1),qx_const(0)))
    var bb=_linear(qx_const(1),qx_const(1))
    for kind in range(2):
        var w=q3_source(kind)
        var base=_inflated(kind,A)
        var field=tp_add(tp_add(tp_scale(ba,qx_const(w.x)),tp_scale(bb,qx_const(w.c))),tp_scale(beta,qx_const(w.y)))
        var target=tp_add(tp_add(tp_scale(ba,base[0]),tp_scale(bb,base[1])),tp_scale(beta,base[2]))
        if corrupt:
            target=tp_add(target,_linear(qx_const(1),qx_const(0)))
        _equal(tp_mod_monic(tp_mul(beta,field),f),tp_mod_monic(target,f))
        # beta*G = 2*(beta*a)+(A-1)*beta, i.e. G=A+2a-1.
        var betaG=tp_add(tp_scale(ba,qx_const(2)),tp_scale(beta,qx_sub(A,qx_const(1))))
        if kind==1:
            betaG=tp_scale(betaG,qx_const(-1))
        _equal(tp_mod_monic(target,f),tp_mod_monic(betaG,f))
        # All nine affine prefix kinds, with independent full incidence image.
        var R=A.copy() if kind==0 else N.copy()
        var B=N.copy() if kind==0 else A.copy()
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
        # Exact inherited P3 ancestry, including n=3, and real reversed edge.
        var parent=p3_source(kind)
        var ai=qx_add(A,qx_const(1)) if kind==0 else qx_sub(n,qx_const(2))
        var aj=qx_sub(n,qx_const(2)) if kind==0 else qx_add(A,qx_const(1))
        _equal3(symbolic_child(-1,parent.top,parent.bottom,_offset(parent),LAST if kind==0 else RUN,ai,RUN if kind==0 else LAST,aj,w.top,w.bottom),_offset(w))
        # Selected five-edge exit with actual word bounds and target types.
        for stage in range(5):
            var source=_stage(stage)
            var dest=_stage(stage+1)
            var tk=LAST if stage==0 or stage==2 else RUN
            var bk=RUN if stage==4 else FIRST
            var i=qx_add(A,qx_const(1)) if stage==0 else (d.copy() if stage==1 else (n.copy() if stage==2 else qx_const(1)))
            var j=qx_const(2 if stage==4 else 0)
            if kind==1:
                source=reverse_label(source)
                dest=reverse_label(dest)
            var ti=j.copy() if kind==1 else i.copy()
            var bj=i.copy() if kind==1 else j.copy()
            _equal3(symbolic_child(-1,source.top,source.bottom,_offset(source),bk if kind==1 else tk,ti,tk if kind==1 else bk,bj,dest.top,dest.bottom),_offset(dest))
        # X's genuine LAST/RUN return rules out all-edge strict descent.
        var xs=q3_target(kind)
        _equal3(symbolic_child(-1,xs.top,xs.bottom,_offset(xs),LAST if kind==0 else RUN,qx_add(A if kind==0 else n,qx_const(1)),RUN if kind==0 else LAST,qx_add(n if kind==0 else A,qx_const(1)),w.top,w.bottom),_offset(w))
    print("CLASS_A_BOUNDARY_Q3 two_complete_oriented_stars=true", "children_per_orientation=1", "chamber_union_labels=2", "all_direct_Q3_children_typed_tail_at_most_four=true", "Q3_typed_exit_at_most_five=true", "actual_two_cycle=true", "global_closure=false", "BH=false")


def _dimensions(kind: Int,k: Int,t: Int) raises -> Tuple[Int,Int,Int]:
    _=q3_source(kind)
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,2)
    return(p[0],p[1],A)


def q3_child_allowed(kind: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    var p=_dimensions(kind,k,t)
    var R=p[2] if kind==0 else p[0]-1
    var B=p[0]-1 if kind==0 else p[2]
    if i<0 or i>R+1 or j<0 or j>B+1:
        raise Error("nonexistent Q3 occurrence")
    return (i==p[2]+1 and j==0) if kind==0 else (i==0 and j==p[2]+1)


def q3_child_star(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var i=p[2]+1 if kind==0 else 0
    var j=0 if kind==0 else p[2]+1
    if not q3_child_allowed(kind,k,t,i,j):
        raise Error("Q3 singleton synthesis failed")
    var target=member_transport(-1,k,p[0],p[1],q3_source(kind),i,j)
    if target!=q3_target(kind):
        raise Error("Q3 singleton target mismatch")
    var out=List[BoundaryEdge]()
    out.append(BoundaryEdge(i,j,target))
    return out^


def verify_q3_packet(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,edge: BoundaryEdge) raises:
    var p=_dimensions(kind,k,t)
    if not q3_child_allowed(kind,k,t,edge.i,edge.j) or edge.target!=q3_target(kind):
        raise Error("Q3 packet guard or typed target refused")
    verify_member_edge(tables,-1,k,p[0],p[1],q3_source(kind),edge.i,edge.j,edge.target)


def q3_path(kind: Int,k: Int,t: Int) raises -> List[BoundaryEdge]:
    var p=_dimensions(kind,k,t)
    var out=List[BoundaryEdge]()
    for stage in range(5):
        var i=p[2]+1 if stage==0 else (p[1] if stage==1 else (p[0] if stage==2 else 1))
        var j=2 if stage==4 else 0
        var target=_stage(stage+1)
        out.append(BoundaryEdge(j if kind==1 else i,i if kind==1 else j,reverse_label(target) if kind==1 else target))
    return out^


def verify_q3_path(tables: SeedOverlapTables,kind: Int,k: Int,t: Int,steps: List[BoundaryEdge]) raises:
    var p=_dimensions(kind,k,t)
    var want=q3_path(kind,k,t)
    if len(steps)!=5:
        raise Error("incomplete five-edge Q3 path")
    var w=q3_source(kind)
    for z in range(5):
        var edge=steps[z]
        if edge.i!=want[z].i or edge.j!=want[z].j or edge.target!=want[z].target:
            raise Error("Q3 intended occurrence or intermediate mismatch")
        verify_member_edge(tables,-1,k,p[0],p[1],w,edge.i,edge.j,edge.target)
        w=edge.target
    if not typed_coincidence(w):
        raise Error("Q3 terminal is not typed coincidence")
