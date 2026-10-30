"""Literal occurrences and sharp adjacent-index controls for A_K."""
from std.collections import Dict
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_c_seed_interfaces import SeedInterface, segment_children
from psc.class_c_boundary_frontier import BoundaryOffset
from psc.class_c_boundary_descendants import boundary_parent
from psc.class_c_r_transfer import r_parent
from psc.class_c_indexed_transfer import indexed_parent, indexed_children, indexed_representatives
from psc.overlap_seed_patch import OverlapState, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt, sign_at_perron
from class_c_seed_interfaces import compare_sets


def main() raises:
    var cases = 0
    var accepted = 0
    var duplicates = 0
    for d in range(7,65):
        var m = SeedInterface(d,1,0)
        var cache = Dict[CubicElt,Int]()
        assert_equal(indexed_parent(m,4),boundary_parent(m,1))
        assert_equal(selected_overlap_child(m.tables,r_parent(m,2),m.p+1,0),indexed_parent(m,0))
        var Ks = indexed_representatives(d)
        for index in range(len(Ks)):
            var K = Ks[index]
            var parent = indexed_parent(m,K)
            var seen = Dict[OverlapState,Bool]()
            var actual = List[OverlapState]()
            var pairs = 0
            for i in range(len(m.tables.sigma[parent.top])):
                for j in range(len(m.tables.sigma[parent.bottom])):
                    var ch = selected_overlap_child(m.tables,parent,i,j)
                    if interior_overlap_cached(m.tables,cache,ch):
                        pairs += 1
                        if ch not in seen:
                            seen[ch] = True
                            actual.append(ch)
                        else:
                            duplicates += 1
            assert_equal(pairs,2*d+1)
            assert_equal(len(actual),12 if K == d else 10)
            compare_sets(actual,indexed_children(m,K))
            compare_sets(actual,segment_children(m,cache,parent))
            cases += 1
            accepted += pairs
        # g+1 switches sign between K=d-1 and K=d, strictly.
        for K in [d-1,d]:
            var margin = BoundaryOffset(1,-K-1,K-3).state(m,2,2).shift
            assert_equal(sign_at_perron(m.tables.field,margin),-1 if K == d else 1)
        for K in [-1,d+1]:
            var rejected = False
            try:
                _ = indexed_children(m,K)
            except:
                rejected = True
            assert_true(rejected)
    assert_equal(cases,357)
    assert_equal(accepted,25213)
    assert_equal(duplicates,21527)
    print("INDEXED_TRANSFER_ACTUAL_OCCURRENCE_PASS",cases,accepted,duplicates)
    require_contract("Class-C plus c=0 indexed A_K complete local child sets, K=0..d, equal exhaustive actual occurrences and general exact transfer on 357 representatives; sharp K=d-1/d sign/count change, constant occurrence count, Q/A_0 witnesses and invalid-index refusals")
