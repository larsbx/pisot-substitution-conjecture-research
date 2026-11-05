"""All 18 complete non-unit pair graphs; no SC witness input."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.c4_pair_overlap_attractor import (
    build_source_order_graph, construct_attractor_weights, verify_pair_weights,
)
from psc.c4_pair_overlap_graph import source_class_images, outside_source_box


def main() raises:
    var sizes: List[Int] = [15824, 15877, 15850, 15909, 15896, 15897, 15802, 15867, 15847, 15913, 15895, 15876, 15891, 15881, 15890, 15895, 15872, 15904]
    var edges: List[Int] = [78333, 78356, 78359, 78296, 78305, 78246, 78306, 78353, 78359, 78276, 78336, 78348, 78288, 78299, 78278, 78326, 78334, 78331]
    var sweeps: List[Int] = [334, 97, 458, 148, 283, 168, 129, 89, 118, 161, 294, 127, 152, 85, 152, 471, 106, 332]
    var roots: List[List[Int]] = [[51342, 8165, 27199], [7864, 3988, 8984], [63257, 12357, 27900], [12581, 1, 1], [34566, 7387, 2], [5573, 1004, 1], [9004, 3337, 1], [9459, 1448, 3253], [12462, 1, 1], [2038, 1, 4598], [17935, 333, 23541], [1500, 3386, 7639], [1509, 3407, 7687], [3568, 3287, 7452], [6837, 1, 5439], [55180, 15331, 34619], [12961, 2543, 5749], [44233, 6960, 35165]]
    var total_states = 0
    var total_edges = 0
    for index in range(18):
        var graph = build_source_order_graph(index)
        var result = construct_attractor_weights(graph,4000)
        var weights = result[0].copy()
        assert_equal(len(graph.states),sizes[index])
        assert_equal(result[1],sweeps[index])
        assert_equal(verify_pair_weights(graph,weights),102)
        var count = 0
        for i in range(len(graph.rows)):
            count += len(graph.rows[i])
            var s = graph.states[i].copy()
            assert_true(not (s[0] == s[1] and s[2] == 0 and s[3] == 0 and s[4] == 0))
        assert_equal(count,edges[index])
        for i in range(3):
            assert_equal(weights[i],roots[index][i])
        total_states += len(graph.states)
        total_edges += count
    assert_equal(total_states,285786)
    assert_equal(total_edges,1409729)
    assert_true(not outside_source_box(48,0,24,24,12))
    assert_true(outside_source_box(49,0,0,24,12))
    for index in [-1,18]:
        var refused = False
        try:
            _ = source_class_images(index)
        except:
            refused = True
        assert_true(refused)
    # State-cap refusal control: a budget of three states is exhausted before
    # the graph closes, and the run must report an inconclusive budget, not a
    # verdict.  (It is not a prefix-period control: the attractor's 12 % period
    # check is an invariant on a three-letter alphabet and cannot fail.)
    var cap_error = String("")
    try:
        _ = build_source_order_graph(5,state_cap=3)
    except e:
        cap_error = String(e)
    assert_equal(cap_error,"state budget exhausted; inconclusive")
    print("all 18 source-order pair graphs passed exact contraction")
    require_contract("complete 18-source nonunit incidence class: all paired occurrences, certified common box, positive integer rate 51/10 below beta squared, original controls retained; no SC input, no general PSC or PDS inference")
