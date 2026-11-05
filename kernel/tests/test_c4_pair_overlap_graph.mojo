"""Finite graph arithmetic controls. Measure theorem remains a written proof."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.c4_pair_overlap_graph import (
    build_pair_graph, construct_pair_weights, verify_pair_weights,
    outside_pair_box, canonical_pair,
)


def main() raises:
    var sizes: List[Int] = [7150,7083]
    var edges: List[Int] = [34826,34853]
    var iterations: List[Int] = [856,1695]
    var roots: List[List[Int]] = [[38500,1,1],[82573,12935,44045]]
    for fixture in range(2):
        var graph = build_pair_graph(fixture)
        var result = construct_pair_weights(graph)
        var weights = result[0].copy()
        assert_equal(len(graph.states),sizes[fixture])
        assert_equal(result[1],iterations[fixture])
        var count = 0
        for i in range(len(graph.rows)):
            count += len(graph.rows[i])
            var s = graph.states[i].copy()
            assert_true(not (s[0] == s[1] and s[2] == 0 and s[3] == 0 and s[4] == 0))
        assert_equal(count,edges[fixture])
        for i in range(3):
            assert_equal(weights[i],roots[fixture][i])
        assert_true(verify_pair_weights(graph,weights) > 0)
        weights[0] = 0
        var refused = False
        try:
            _ = verify_pair_weights(graph,weights)
        except:
            refused = True
        assert_true(refused)
        refused = False
        try:
            _ = construct_pair_weights(graph,1)
        except:
            refused = True
        assert_true(refused)
    var refused = False
    try:
        _ = build_pair_graph(0,3)
    except:
        refused = True
    assert_true(refused)
    assert_true(not outside_pair_box(32,0,16))
    assert_true(outside_pair_box(33,0,0))
    assert_equal(canonical_pair(2,0,1,-2,3),[0,2,-1,2,-3])
    print("two complete overlap graphs and exact positive subinvariance passed")
    require_contract("complete two-step paired-prefix graphs for the two named nonunit controls; exact residue and enclosure pruning, every occurrence multiplicity, positive integer contraction weights and cap refusals; written null-measure implication only, no general C4/PSC")
