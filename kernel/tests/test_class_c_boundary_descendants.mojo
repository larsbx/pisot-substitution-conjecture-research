"""Complete actual occurrence pairs guard the two uniform boundary stars."""
from std.collections import Dict
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_c_seed_interfaces import SeedInterface, segment_children
from psc.class_c_boundary_descendants import boundary_parent, boundary_children
from psc.overlap_seed_patch import OverlapState, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt, sign_at_perron
from class_c_seed_interfaces import compare_sets


def main() raises:
    var interfaces = 0
    var occurrences = 0
    var duplicate_occurrences = 0
    for d in range(7,65):
        var m = SeedInterface(d,1,0)
        ref tab = m.tables
        var cache = Dict[CubicElt,Int]()
        # Strict W, E, G chambers from the hand proof.
        for bounds in [[3,-10,10,-1,0],[-4,11,0,9,10],[-5,11,0,6,7]]:
            assert_true(sign_at_perron(tab.field,m.v(bounds[0],bounds[1],bounds[2]-bounds[3])) > 0)
            assert_true(sign_at_perron(tab.field,m.v(-bounds[0],-bounds[1],bounds[4]-bounds[2])) > 0)
        var P = boundary_parent(m,0)
        var Q = boundary_parent(m,1)
        assert_equal(selected_overlap_child(tab,m.seed(1),m.p+1,d-5),P)
        assert_equal(selected_overlap_child(tab,P,0,m.r+1),Q)
        for s in range(9):
            assert_true(m.seed(s) != Q)
            var cs = m.children(s)
            for i in range(len(cs)):
                assert_true(cs[i] != Q)
        for stage in range(2):
            var parent = boundary_parent(m,stage)
            var seen = Dict[OverlapState,Bool]()
            var actual = List[OverlapState]()
            var pairs = 0
            for i in range(len(tab.sigma[parent.top])):
                for j in range(len(tab.sigma[parent.bottom])):
                    var ch = selected_overlap_child(tab,parent,i,j)
                    if interior_overlap_cached(tab,cache,ch):
                        pairs += 1
                        if ch not in seen:
                            seen[ch] = True
                            actual.append(ch)
                        else:
                            duplicate_occurrences += 1
            assert_equal(pairs,1 if stage == 0 else 2*d+1)
            compare_sets(actual,boundary_children(m,stage))
            compare_sets(actual,segment_children(m,cache,parent))
            assert_equal(len(actual),1 if stage == 0 else 10)
            occurrences += pairs
            interfaces += 1
        for stage in [-1,2]:
            var rejected = False
            try:
                _ = boundary_children(m,stage)
            except:
                rejected = True
            assert_true(rejected)
    for params in [[7,1,1],[7,-1,0]]:
        var m = SeedInterface(params[0],params[1],params[2])
        var rejected = False
        try:
            _ = boundary_children(m,0)
        except:
            rejected = True
        assert_true(rejected)
    assert_equal(interfaces,116)
    assert_equal(occurrences,4234)
    assert_equal(duplicate_occurrences,3596)
    print("BOUNDARY_DESCENDANT_ACTUAL_OCCURRENCE_PASS",interfaces,occurrences,duplicate_occurrences)
    require_contract("Class-C plus c=0 boundary P and Q complete descendant stars equal exhaustive actual occurrences for d=7..64; uniform escape witnesses, strict mixed walls, multiplicities and out-of-scope refusals")
