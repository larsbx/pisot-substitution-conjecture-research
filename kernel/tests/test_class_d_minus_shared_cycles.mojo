"""Whole-cycle parameters cannot be reselected on successive edges."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_d_minus_cycle_superset import CycleState
from psc.class_d_minus_shared_cycles import (
    cycle_forms, refute_cycle, negative_cycle, negative_segments,
    verify_documented_negative_control, verify_negative_cycle,
)


def main() raises:
    verify_documented_negative_control()
    verify_negative_cycle()
    var states = List[CycleState]()
    states.append(CycleState(2,1,-2,4,-3))
    states.append(CycleState(1,2,2,-4,3))
    var segments = List[List[Int]]()
    segments.append([2,1])
    segments.append([1,2])
    var forms = cycle_forms(states,segments)
    for f in forms:
        assert_true(f[0]>=0)  # u=v=0 is a shared integer witness
    assert_equal(refute_cycle(states,segments),False)
    var broken = negative_segments()
    broken[5] = [0,0]  # only the closing edge is broken
    var refused = False
    try:
        _ = cycle_forms(negative_cycle(),broken)
    except:
        refused = True
    assert_true(refused)
    states[0] = CycleState(2,1,Int.MAX,4,-3)
    refused = False
    try:
        _ = cycle_forms(states,segments)
    except:
        refused = True
    assert_true(refused)
    require_contract("minus class-D shared-parameter cycle guards: replay every typed affine edge including closure; checked Farkas refutation over one u,v; six individually feasible edges jointly require v=2u+7 and v<=u; retain genuine U/Ubar cycle; bounded supplied cycles do not prove CycleSum")
