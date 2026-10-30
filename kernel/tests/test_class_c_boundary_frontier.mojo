"""Literal occurrences guard the bounded-coefficient symbolic frontier rules."""
from std.collections import Dict
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_c_seed_interfaces import SeedInterface, segment_children
from psc.class_c_boundary_frontier import (
    BoundaryOffset, boundary_fraction_sign, boundary_sign, boundary_window,
    frontier_parent, frontier_children,
)
from psc.class_c_boundary_descendants import boundary_children
from psc.overlap_seed_patch import OverlapState, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt, sign_at_perron
from class_c_seed_interfaces import compare_sets


def main() raises:
    var stars = 0
    var accepted = 0
    var duplicates = 0
    for d in range(7,65):
        var m = SeedInterface(d,1,0)
        ref tab = m.tables
        var cache = Dict[CubicElt,Int]()
        var roots = List[OverlapState]()
        for index in range(10):
            var parent = frontier_parent(m,index)
            roots.append(parent)
            var seen = Dict[OverlapState,Bool]()
            var actual = List[OverlapState]()
            for i in range(len(tab.sigma[parent.top])):
                for j in range(len(tab.sigma[parent.bottom])):
                    var ch = selected_overlap_child(tab,parent,i,j)
                    if interior_overlap_cached(tab,cache,ch):
                        accepted += 1
                        if ch not in seen:
                            seen[ch] = True
                            actual.append(ch)
                        else:
                            duplicates += 1
            compare_sets(actual,frontier_children(m,index))
            compare_sets(actual,segment_children(m,cache,parent))
            stars += 1
        compare_sets(roots,boundary_children(m,1))
        # Every fractional sign in the claimed coefficient envelope, with
        # integral cancellation controls and negative fractional corrections.
        for U in range(-5,6):
            for R in range(-10,11):
                var v = BoundaryOffset(0,U,R).state(m,2,2).shift
                assert_equal(boundary_fraction_sign(d,U,R),sign_at_perron(tab.field,v))
                assert_equal(boundary_sign(d,BoundaryOffset(1,U,R)),1)
                assert_equal(boundary_sign(d,BoundaryOffset(-1,U,R)),-1)
        var open = boundary_window(d,BoundaryOffset(),BoundaryOffset(2),-5,5,5)
        assert_equal(len(open),1)
        assert_equal(open[0],1)
        assert_equal(len(boundary_window(d,BoundaryOffset(),BoundaryOffset(2),2,5,5)),0)
    for params in [[7,6,0],[7,0,11],[6,0,0],[65,0,0]]:
        var rejected = False
        try:
            _ = boundary_fraction_sign(params[0],params[1],params[2])
        except:
            rejected = True
        assert_true(rejected)
    var m = SeedInterface(7,1,0)
    for invalid in [-1,10]:
        var rejected = False
        try:
            _ = frontier_children(m,invalid)
        except:
            rejected = True
        assert_true(rejected)
    for params in [[7,1,1],[7,-1,0]]:
        var other = SeedInterface(params[0],params[1],params[2])
        var rejected = False
        try:
            _ = frontier_children(other,0)
        except:
            rejected = True
        assert_true(rejected)
    assert_equal(stars,580)
    print("BOUNDARY_TEN_ACTUAL_OCCURRENCE_PASS",stars,accepted,duplicates)
    require_contract("Class-C plus c=0 ten Q-child outgoing stars use exact bounded-coefficient integer windows and equal literal occurrence and general exact transfer sets at d=7..64; all fractional signs, strict endpoints and envelope refusals")
