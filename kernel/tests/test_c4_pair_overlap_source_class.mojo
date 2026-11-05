"""Period/domain controls; the driver separately replays all 18 complete graphs."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.c4_pair_overlap_graph import (
    source_class_images, source_class_step, build_source_class_graph,
    construct_weights_at_rate, verify_weights_at_rate, outside_source_box,
)


def main() raises:
    var step_three = 0
    for index in range(18):
        var sigma = source_class_images(index)
        var expected: List[List[Int]] = [[0,1,0],[1,1,1],[2,1,0]]
        for j in range(3):
            var mass: List[Int] = [0,0,0]
            for c in sigma[j]:
                mass[c] += 1
            assert_equal(mass,expected[j])
        if source_class_step(index) == 3:
            step_three += 1
    assert_equal(step_three,4)
    var graph = build_source_class_graph(12)
    assert_equal(len(graph.states),16664)
    var result = construct_weights_at_rate(graph,233,3)
    var weights = result[0].copy()
    assert_equal(weights[0],756)
    assert_equal(weights[1],1710)
    assert_equal(weights[2],3878)
    assert_true(verify_weights_at_rate(graph,weights,233,3) > 0)
    weights[0] = 0
    var refused = False
    try:
        _ = verify_weights_at_rate(graph,weights,233,3)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = build_source_class_graph(12,2)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = build_source_class_graph(0,0,3)
    except:
        refused = True
    assert_true(refused)
    for bad in [-1,18]:
        refused = False
        try:
            _ = source_class_images(bad)
        except:
            refused = True
        assert_true(refused)
    assert_true(not outside_source_box(48,0,24,24,12))
    assert_true(outside_source_box(49,0,0,24,12))
    print("source-class domains, period-three graph and refusal controls passed")
    require_contract("all 18 fixed-incidence sources use authenticated fixed-point periods; complete interval/quotient graph and positive integer subinvariance; period-three and wrong-period controls; written compact measure argument, no general PSC")
