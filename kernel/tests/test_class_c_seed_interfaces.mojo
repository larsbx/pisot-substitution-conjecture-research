"""Actual occurrences independently guard every first-layer segment window."""
from std.collections import Dict
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_c_seed_interfaces import SeedInterface, segment_children, integer_window, sum_wall_polynomial, sum_wall_resultant
from psc.overlap_seed_patch import (
    OverlapState, selected_overlap_child, interior_overlap_cached,
)
from psc.perron_field3 import CubicElt
from class_c_seed_interfaces import representative_cs, compare_sets


def main() raises:
    var cases = 0
    var duplicate_occurrences = 0
    var tangencies = 0
    for d in [7,8,9,16]:
        for eps in [1,-1]:
            var cs = representative_cs(d,eps)
            for cc in range(len(cs)):
                var m = SeedInterface(d,eps,cs[cc])
                for k in range(3,7):
                    var P = sum_wall_polynomial(m,k)
                    assert_equal(sum_wall_resultant(m,k),-8*eps*P)
                    assert_equal(P < 0,k <= m.M)
                ref t = m.tables
                var cache = Dict[CubicElt,Int]()
                for s in range(9):
                    var parent = m.seed(s)
                    var seen = Dict[OverlapState,Bool]()
                    var actual = List[OverlapState]()
                    for i in range(len(t.sigma[parent.top])):
                        for j in range(len(t.sigma[parent.bottom])):
                            var ch = selected_overlap_child(t,parent,i,j)
                            if interior_overlap_cached(t,cache,ch):
                                if ch not in seen:
                                    seen[ch] = True
                                    actual.append(ch)
                                else:
                                    duplicate_occurrences += 1
                    compare_sets(actual,m.children(s))
                    compare_sets(actual,segment_children(m,cache,parent))
                    cases += 1
                # Closed endpoint controls in the reusable integer window:
                # (0,2) contains ONLY 1; clipping to [2,9] makes it empty.
                var open = integer_window(t,cache,CubicElt(),m.v(0,0,2),-3,9,2)
                assert_equal(len(open),1)
                assert_equal(open[0],1)
                assert_equal(len(integer_window(t,cache,CubicElt(),m.v(0,0,2),2,9,2)),0)
                var rejected = False
                try:
                    _ = segment_children(m,cache,OverlapState(0,0,t.lengths.l0))
                except:
                    rejected = True
                assert_true(rejected)
                tangencies += 1
    for invalid in [[6,1,0],[65,1,0],[7,0,0],[7,1,-1],[7,1,12],[7,-1,6]]:
        var rejected = False
        try:
            _ = SeedInterface(invalid[0],invalid[1],invalid[2])
        except:
            rejected = True
        assert_true(rejected)
    assert_true(duplicate_occurrences > 0 and tangencies > 0)
    print("NINE_SEED_ACTUAL_OCCURRENCE_PASS",cases,"duplicate_occurrences",duplicate_occurrences,"tangency_controls",tangencies)
    require_contract("Class-C lower-cone nine seed formulas and reusable clipped segment transfers equal exhaustive actual occurrence child sets at every declared chamber representative; strict endpoint, duplicate and out-of-scope controls")
