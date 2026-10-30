"""Complete literal R/T/U stars and strict translation/envelope controls."""
from std.collections import Dict
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_c_seed_interfaces import SeedInterface, segment_children
from psc.class_c_boundary_frontier import (
    BoundaryOffset, boundary_offset_children, frontier_parent, frontier_children,
)
from psc.class_c_boundary_descendants import boundary_children
from psc.class_c_r_transfer import r_parent, r_children
from psc.overlap_seed_patch import OverlapState, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt, cubic_add_checked, cubic_mul_beta
from class_c_seed_interfaces import compare_sets


def main() raises:
    var stars = 0
    var accepted = 0
    var duplicates = 0
    for d in range(7,65):
        var m = SeedInterface(d,1,0)
        ref tab = m.tables
        var cache = Dict[CubicElt,Int]()
        var seed_offsets: List[BoundaryOffset] = [
            BoundaryOffset(),BoundaryOffset(2,0,1),BoundaryOffset(-1,-1,-1),
            BoundaryOffset(),BoundaryOffset(1,0,0),BoundaryOffset(-2,-1,-2),
            BoundaryOffset(),BoundaryOffset(1,0,0),BoundaryOffset(-1,0,-1),
        ]
        for seed in range(9):
            var st = m.seed(seed)
            assert_equal(seed_offsets[seed].state(m,st.top,st.bottom),st)
            compare_sets(m.children(seed),boundary_offset_children(m,st.top,st.bottom,seed_offsets[seed]))
        assert_equal(selected_overlap_child(tab,frontier_parent(m,0),m.p+1,0),r_parent(m,0))
        assert_equal(selected_overlap_child(tab,r_parent(m,0),0,m.n+1),r_parent(m,1))
        assert_equal(selected_overlap_child(tab,r_parent(m,1),0,d),r_parent(m,2))
        var q_children = boundary_children(m,1)
        var shifted = List[OverlapState]()
        for i in range(len(q_children)):
            var ch = q_children[i]
            shifted.append(OverlapState(ch.top,ch.bottom,cubic_add_checked(ch.shift,m.v(1,-1,-1))))
        compare_sets(shifted,r_children(m,1))
        for index in range(3):
            var parent = r_parent(m,index)
            var offset = BoundaryOffset(-2,2,1) if index == 0 else (BoundaryOffset(-1,1,-4) if index == 1 else BoundaryOffset(3,-3,4))
            var actual = List[OverlapState]()
            var seen = Dict[OverlapState,Bool]()
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
                            duplicates += 1
            assert_equal(pairs,1 if index == 0 else (4*d-1 if index == 1 else 4))
            compare_sets(actual,r_children(m,index))
            compare_sets(actual,segment_children(m,cache,parent))
            compare_sets(actual,boundary_offset_children(m,parent.top,parent.bottom,offset))
            stars += 1
            accepted += pairs
        var old_child = selected_overlap_child(tab,frontier_parent(m,0),m.p+1,3)
        var false_child = OverlapState(old_child.top,old_child.bottom,cubic_add_checked(old_child.shift,cubic_mul_beta(tab.field,m.v(1,-1,-1))))
        assert_equal(false_child,BoundaryOffset(3,3,1).state(m,0,2))
        assert_true(not interior_overlap_cached(tab,cache,false_child))
        # A boundary-touching parent and an unsupported query must refuse.
        for invalid in [BoundaryOffset(1,0,0),BoundaryOffset(0,6,0)]:
            var rejected = False
            try:
                _ = boundary_offset_children(m,2,2,invalid)
            except:
                rejected = True
            assert_true(rejected)
    var control = SeedInterface(7,1,0)
    for invalid in [-1,3]:
        var rejected = False
        try:
            _ = r_children(control,invalid)
        except:
            rejected = True
        assert_true(rejected)
        rejected = False
        try:
            _ = boundary_offset_children(control,invalid,0,BoundaryOffset())
        except:
            rejected = True
        assert_true(rejected)
    for params in [[7,1,1],[7,-1,0]]:
        var other = SeedInterface(params[0],params[1],params[2])
        var rejected = False
        try:
            _ = r_children(other,0)
        except:
            rejected = True
        assert_true(rejected)
    assert_equal(stars,174)
    assert_equal(accepted,8468)
    assert_equal(duplicates,7598)
    # The exact one-star translation is not an inflation conjugacy.
    var m = SeedInterface(7,1,0)
    var base = frontier_children(m,0)
    var target = boundary_offset_children(m,0,2,BoundaryOffset(3,-3,4))
    var actual = List[OverlapState]()
    var seen = Dict[OverlapState,Bool]()
    var cache = Dict[CubicElt,Int]()
    var parent = BoundaryOffset(3,-3,4).state(m,0,2)
    for i in range(len(m.tables.sigma[parent.top])):
        for j in range(len(m.tables.sigma[parent.bottom])):
            var ch = selected_overlap_child(m.tables,parent,i,j)
            if interior_overlap_cached(m.tables,cache,ch) and ch not in seen:
                seen[ch] = True
                actual.append(ch)
    compare_sets(actual,target)
    var delta = cubic_mul_beta(m.tables.field,m.v(1,-1,-1))
    var escapes = 0
    for i in range(len(base)):
        var ch = OverlapState(base[i].top,base[i].bottom,cubic_add_checked(base[i].shift,delta))
        if ch not in seen:
            escapes += 1
    assert_true(escapes > 0)
    print("R_TRANSLATION_NONCOMMUTATION_PASS",len(base),len(target),escapes)
    print("R_TRANSFER_SEED_REGRESSION_PASS",522)
    print("R_TRANSFER_ACTUAL_OCCURRENCE_PASS",stars,accepted,duplicates)
    require_contract("Class-C plus c=0 R/T/U complete child sets and uniform occurrence witnesses at d=7..64; exact one-star translation and rejected recursive extension; shared integer-coordinate transfer agrees with general transfer and exhaustive words, with tangency and unsupported-envelope refusal")
