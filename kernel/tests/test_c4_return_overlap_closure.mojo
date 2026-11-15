"""Native full occurrence closure; emits every state/edge for independent parity."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.c4_return_overlap_closure import (
    ReturnOverlapClosure, strict_physical_overlap, perron_sign,
)


def test_strict_endpoints_and_exact_signs() raises:
    for x in range(3):
        for y in range(3):
            assert_true(strict_physical_overlap(x,y,[0,0,0]))
            var contact: List[Int] = [0,0,0]
            contact[y] = 1
            assert_true(not strict_physical_overlap(x,y,contact))
            contact = [0,0,0]
            contact[x] = -1
            assert_true(not strict_physical_overlap(x,y,contact))
    assert_equal(perron_sign([0,0,0]),0)
    var refused = False
    try:
        _ = perron_sign([1001,0,0])
    except:
        refused = True
    assert_true(refused)


def test_budget_exhaustion_is_not_a_receipt() raises:
    for cap in [0, 1, 117, 1133, 2049]:
        var refused = False
        try:
            _ = ReturnOverlapClosure(cap)
        except:
            refused = True
        assert_true(refused)


def main() raises:
    test_strict_endpoints_and_exact_signs()
    test_budget_exhaustion_is_not_a_receipt()
    var g = ReturnOverlapClosure()
    g.verify_productivity()
    assert_equal(g.initial_count,118)
    assert_equal(len(g.states),1134)
    var counts: List[Int] = [0,0,0,0,0,0]
    var edge_count = 0
    for i in range(len(g.states)):
        assert_true(g.distance[i] >= 0 and g.distance[i] <= 5)
        counts[g.distance[i]] += 1
        var s = g.states[i].copy()
        for k in range(2,5):
            assert_true(s[k] >= -2 and s[k] <= 2)
        print("RCO_STATE",i,s[0],s[1],s[2],s[3],s[4])
        for e in g.edges[i]:
            print("RCO_EDGE",i,e[0],e[1],e[2])
            edge_count += 1
        print("RCO_DIST",i,g.distance[i])
    assert_equal(edge_count,3106)
    assert_equal(counts,[120,90,278,286,256,104])
    require_contract("complete strict physical-overlap closure of aligned return-word roots for 01/121/012 retains all 3106 child occurrences on 1134 decorated states; every state has a verified coincidence path of length at most five; no guessed register bound and no arbitrary-PIP claim")
