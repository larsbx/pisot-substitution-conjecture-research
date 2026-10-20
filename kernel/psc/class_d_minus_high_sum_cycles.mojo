"""Genuine formal higher-sum cycles: a control against dropping seed reachability.

On a=2k-1,b=1,k>=2, U_k=(y,c,-2k,4k,-3k) and its mirror form
an exact interior two-cycle. This does not show either vertex seed-reachable.
"""
from finite_linear_algebra.scalar import q_int
from psc.param_poly import QX, qx_affine, qx_add, qx_sub, qx_const, qx_is_zero, qx_neg, tp_add, tp_sub, tp_neg, tp_scale
from psc.symbolic_line import Eventual, certify_wedge_pisot
from psc.class_d_positive_b_geometry import _perron_sign
from symbolic_line_certificate import ClassLine
from a1_normal_form_census import CLASS_D


# Concrete calibration uses the independent exact Perron-field seed graph,
# not the conditional 1971-state box or a presumed |s| bound.
from psc.class_d_minus_cycle_superset import CycleState
from psc.class_d_minus_shared_cycles import cycle_forms
from psc.class_d_minus_recurrent_support import member, state_of, emit_counterexample
from psc.overlap_seed_patch import (
    build_seed_overlap_tables_screened, build_seed_overlap_graph_from_tables,
    selected_overlap_child, interior_overlap,
)

def verify_high_sum_ray() raises:
    # a=2k-1,b=1: p=6k+3,q=6k+4,r=4k+3.
    var line = ClassLine(CLASS_D,[6,3,6,4,4,3],True).line()
    if line.first[1] != 1 or line.first[2] != 1 or line.last[2] != 1 or line.y != 2:
        raise Error("high-sum ray endpoint itinerary changed")
    var ev = Eventual()
    ev.threshold = q_int(1)
    var cert = certify_wedge_pisot(line,ev)
    if not cert.holds:
        raise Error("high-sum ray failed PIP certification")
    var w = List[QX]()
    w.append(qx_affine(0,-2))
    w.append(qx_affine(0,4))
    w.append(qx_affine(0,-3))
    if not qx_is_zero(qx_add(qx_add(qx_add(w[0],w[1]),w[2]),qx_affine(0,1))):
        raise Error("high-sum ray no longer has sum -k")
    # LAST of sigma(y) is c at r+1; last RUN of sigma(c) is y at q.
    # Both prefixes have one c; their y-counts are r and q-1.
    var mw = line.mw(w)
    var delta_y = qx_sub(qx_sub(line.run[1],qx_const(1)),line.run[2])
    var child = List[QX]([mw[0].copy(),mw[1].copy(),qx_add(mw[2],delta_y)])
    for d in range(3):
        if not qx_is_zero(qx_add(child[d],w[d])):
            raise Error("symbolic high-sum occurrence edge is not the mirror")
    var reverse = List[QX]()
    for x in w:
        reverse.append(qx_neg(x))
    var rmw = line.mw(reverse)
    rmw[2] = qx_sub(rmw[2],delta_y)
    for d in range(3):
        if not qx_is_zero(qx_sub(rmw[d],w[d])):
            raise Error("symbolic high-sum closing edge failed")
    # All indices are legal: r+1 is LAST, and q>=1 is a RUN index.
    if ev.sign(qx_sub(line.run[1],qx_const(1))) < 0:
        raise Error("high-sum bottom run index is not legal")
    var t = line.t_of(w)
    var lower = tp_add(line.ell[1],t)
    var upper = tp_sub(line.ell[2],t)
    if _perron_sign(line,lower,ev)*cert.ell_sign <= 0 or _perron_sign(line,upper,ev)*cert.ell_sign <= 0:
        raise Error("high-sum ray interior margins not certified")
    if _perron_sign(line,tp_neg(t),ev)*cert.ell_sign <= 0 or _perron_sign(line,tp_add(tp_scale(t,qx_const(2)),line.ell[2]),ev)*cert.ell_sign <= 0:
        raise Error("high-sum ray normalized offset failed -1/2<t<0")
    # Mirroring exchanges these same two margins; no independent assumption.
    if ev.first_integer_above() != 2 or ev.b_floor != 0:
        print("HIGH_SUM_RAY_UNDECLARED_CUT",ev.first_integer_above(),ev.b_floor)
        raise Error("high-sum ray certificate narrowed k>=2")
    print("HIGH_SUM_FORMAL_RAY_CERTIFIED k>=2 a=2k-1 b=1 abs_sum=k interior=true period=2 seed_reachability=not_asserted_by_this_certificate")



def high_sum_seed_sample(k: Int, cap: Int = 20000) raises -> List[Int]:
    if k < 2 or k > 50:
        raise Error("high-sum finite calibration budget requires 2<=k<=50")
    var a = 2*k-1
    var states = List[CycleState]()
    states.append(CycleState(2,1,-2*k,4*k,-3*k))
    states.append(CycleState(1,2,2*k,-4*k,3*k))
    var segments = List[List[Int]]()
    segments.append([2,1])
    segments.append([1,2])
    var forms = cycle_forms(states,segments)
    for f in forms:
        if f[0]+f[1]*(a-2) < 0:
            raise Error("shared parameters fail the scaled U cycle guards")
    var tables = build_seed_overlap_tables_screened(member(a,1))
    var source = state_of(tables,states[0])
    var mirror = state_of(tables,states[1])
    if not interior_overlap(tables,source) or not interior_overlap(tables,mirror):
        raise Error("scaled U control lost interior geometry")
    var last_y = 4*k+4
    var run_c = 6*k+4
    if selected_overlap_child(tables,source,last_y,run_c) != mirror or selected_overlap_child(tables,mirror,run_c,last_y) != source:
        raise Error("scaled U control lost occurrence-level cycle replay")
    print("HIGH_SUM_OCCURRENCE",a,1,states[0].key(),last_y,run_c,states[1].key())
    print("HIGH_SUM_OCCURRENCE",a,1,states[1].key(),run_c,last_y,states[0].key())
    var graph = build_seed_overlap_graph_from_tables(tables,cap)
    if graph.capped:
        print("HIGH_SUM_SEED_GRAPH_CAPPED",k,cap)
        raise Error("capped graph cannot decide seed reachability")
    var reached = 0
    for i in range(graph.size()):
        if graph.states[i] == source or graph.states[i] == mirror:
            reached += 1
            emit_counterexample(tables,graph,i,a,1)
    print("HIGH_SUM_SEED_SAMPLE",k,"a",a,"b",1,"complete_states",graph.size(),"reachable_pair_vertices",reached)
    return [graph.size(),reached]
