"""Exact whole-cycle guard conjunction over ONE fixed u=a-2,v=b-1.

This checks supplied cycles, never enumerates all cycles and never asserts
CycleSum. A missing certificate means NOT REFUTED, not feasible or reachable.
"""
from finite_exact.rat_q import Q
from psc.exact import q_string
from finite_linear_algebra.scalar import q_int
from psc.farkas_lp import farkas_certificate, farkas_refutes
from psc.class_d_minus_cycle_superset import CycleState, _segment, edge_forms


def cycle_forms(states: List[CycleState], segments: List[List[Int]]) raises -> List[List[Int]]:
    if len(states) == 0 or len(states) != len(segments) or len(states) > 128:
        raise Error("whole-cycle budget requires 1..128 states and one segment pair per edge")
    # This explicit input budget keeps all affine coefficient arithmetic below
    # 100 million, well inside Int64. Never accept arbitrary overflowing inputs.
    for v in states:
        if v.top < 0 or v.top > 2 or v.bottom < 0 or v.bottom > 2 or v.x < -1000000 or v.x > 1000000 or v.c < -1000000 or v.c > 1000000 or v.y < -1000000 or v.y > 1000000:
            raise Error("cycle state outside exact diagnostic budget")
    var forms = List[List[Int]]()
    for i in range(len(states)):
        if len(segments[i]) != 2:
            raise Error("cycle edge needs top/bottom segment kinds")
        var source = states[i].copy()
        var target = states[(i+1)%len(states)].copy()
        var st = _segment(source.top,segments[i][0])
        var sb = _segment(source.bottom,segments[i][1])
        var x = source.x+source.c+sb[1][0]-st[1][0]
        var c = source.x+source.c+2*source.y+sb[1][1]-st[1][1]
        if target.top != st[0][0] or target.bottom != sb[0][0] or target.x != x or target.c != c:
            raise Error("cycle edge fails typed x/c affine replay, including closing edge")
        var guard = edge_forms(source,st,sb,target.x+target.c+target.y)
        for f in guard:
            forms.append(f.copy())
    return forms^


def refute_cycle(states: List[CycleState], segments: List[List[Int]]) raises -> Bool:
    var forms = cycle_forms(states,segments)
    var cert = farkas_certificate(forms,2)
    print("SHARED_CYCLE",len(states),"variables=u,v parameter_scope=whole_cycle")
    for i in range(len(states)):
        print("CYCLE_EDGE",i,states[i].key(),segments[i][0],segments[i][1],states[(i+1)%len(states)].key())
    for i in range(len(forms)):
        print("CYCLE_GUARD",i,forms[i][0],forms[i][1],forms[i][2])
    if len(cert) == 0:
        print("CYCLE_NOT_REFUTED integer_feasibility_geometry_and_seed_reachability_unresolved")
        return False
    if not farkas_refutes(forms,2,cert):
        raise Error("whole-cycle Farkas replay failed")
    for i in range(len(cert)):
        print("FARKAS_MULTIPLIER",i,q_string(cert[i]))
    print("CYCLE_REFUTED_SHARED_PARAMETERS")
    return True


def verify_documented_negative_control() raises:
    # v=2u+7 and v<=u, written as nonnegative affine forms.
    var forms = List[List[Int]]()
    forms.append([-7,-2,1])
    forms.append([7,2,-1])
    forms.append([0,1,-1])
    var y = List[Q]()
    y.append(q_int(1))
    y.append(q_int(0))
    y.append(q_int(1))
    # Sum of the first and third rows is -7-u<0 on u>=0.
    if not farkas_refutes(forms,2,y):
        raise Error("documented shared-parameter negative control changed")
    print("SHARED_PARAMETER_NEGATIVE_CONTROL_CERTIFIED combination=-7-u multipliers=1,0,1")


def negative_cycle() -> List[CycleState]:
    var states = List[CycleState]()
    states.append(CycleState(1,1,-4,7,-5))
    states.append(CycleState(1,0,3,-6,4))
    states.append(CycleState(1,0,-3,5,-4))
    states.append(CycleState(1,2,3,-6,4))
    states.append(CycleState(1,1,-3,5,-4))
    states.append(CycleState(2,2,2,-6,6))
    return states^


def negative_segments() -> List[List[Int]]:
    var pairs = List[List[Int]]()
    pairs.append([0,2])
    pairs.append([0,0])
    pairs.append([0,1])
    pairs.append([0,0])
    pairs.append([1,1])
    pairs.append([2,0])
    return pairs^


def verify_negative_cycle() raises:
    var states = negative_cycle()
    var pairs = negative_segments()
    var forms = cycle_forms(states,pairs)
    # Each edge has its own exact integral parameter witness. These different
    # valuations must NEVER be used as a witness for the complete cycle.
    var points = List[List[Int]]()
    points.append([0,7])
    points.append([0,2])
    points.append([0,0])
    points.append([0,2])
    points.append([1,0])
    points.append([0,4])
    for i in range(6):
        for k in range(2):
            var f = forms[2*i+k].copy()
            if f[0]+f[1]*points[i][0]+f[2]*points[i][1] < 0:
                raise Error("negative-control edge lost its individual integer witness")
    if forms[0] != List[Int]([-7,-2,1]) or forms[1] != List[Int]([7,2,-1]) or forms[5] != List[Int]([0,1,-1]):
        raise Error("documented v=2u+7 / v<=u guards no longer recovered from cycle")
    var cert = List[Q]()
    for i in range(len(forms)):
        cert.append(q_int(1 if i == 0 or i == 5 else 0))
    if not farkas_refutes(forms,2,cert):
        raise Error("cycle's explicit -7-u certificate failed")
    if not refute_cycle(states,pairs):
        raise Error("shared-parameter checker missed the exact impossible cycle")
    print("SIX_EDGE_CONTROL_CERTIFIED each_edge_integer_feasible=true whole_cycle_refuted=true explicit_rows=0,5 sum=-7-u")
