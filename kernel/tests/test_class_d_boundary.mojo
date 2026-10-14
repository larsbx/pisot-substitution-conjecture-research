"""Scope and exact graph/depth calibration for the residual b=0 edge."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_d_boundary import boundary_member, boundary_probe, boundary_edge_flags
from psc.overlap_seed_patch import OverlapState, SeedOverlapTables, build_seed_overlap_tables_screened, interior_overlap, seed_overlap_states
from psc.overlap_zipper import ordered_child_occurrences
from psc.vertex_coincidence import offset_of


def labelled_state(tables: SeedOverlapTables, label: List[Int]) raises -> OverlapState:
    var lengths = [tables.lengths.at(0), tables.lengths.at(1), tables.lengths.at(2)]
    return OverlapState(label[0], label[1], offset_of(lengths, [label[2],label[3],label[4]]))


def prescribed_edge(tables: SeedOverlapTables, parent: OverlapState, child: OverlapState, i: Int, j: Int) raises -> Bool:
    var occurrences = ordered_child_occurrences(tables, parent)
    for k in range(len(occurrences)):
        if occurrences[k].top_index == i and occurrences[k].bottom_index == j:
            return occurrences[k].state == child
    return False


def test_uniform_path_formulas_at_bounded_parameters() raises:
    # Finite calibration of the hand proof in the family note section 4h.
    # Reuse the exact occurrence scan; do not fit paths from adjacency counts.
    for a in range(9):
        var tables = build_seed_overlap_tables_screened(boundary_member(-1, a))
        var s = labelled_state(tables, [0,1,0,0,0])
        var p = labelled_state(tables, [0,0,0,0,1])
        var q = labelled_state(tables, [1,0,-1,1,1])
        var u = labelled_state(tables, [2,2,0,2,-3])
        var v = labelled_state(tables, [2,2,1,1,-3])
        var rr = labelled_state(tables, [1,2,2,-3,1])
        var t = labelled_state(tables, [2,1,-1,1,0])
        var z = labelled_state(tables, [1,2,0,0,0])
        var states = [s,p,q,u,v,rr,t,z]
        for state in states:
            assert_true(interior_overlap(tables, state))
        var seeds = seed_overlap_states(tables)
        var saw_s = False
        var saw_p = False
        for seed in seeds:
            saw_s = saw_s or seed == s
            saw_p = saw_p or seed == p
        assert_true(saw_s and saw_p)
        var r = 2*a+4
        assert_true(prescribed_edge(tables, s, q, 3*a+6, 3*a+7))
        assert_equal(prescribed_edge(tables, p, u, r+4, 1), a >= 3)
        assert_equal(prescribed_edge(tables, q, v, r+5, 1), a >= 3)
        assert_true(prescribed_edge(tables, u, rr, 0, 2))
        assert_true(prescribed_edge(tables, v, rr, 0, 3))
        assert_true(prescribed_edge(tables, rr, t, a+1, r+1))
        assert_true(prescribed_edge(tables, t, z, r+1, r))
        assert_true(not prescribed_edge(tables, t, z, r+1, r+1))
        assert_true(z.shift.is_zero())
        assert_true(not z.is_coincidence())


def main() raises:
    test_uniform_path_formulas_at_bounded_parameters()
    var x = boundary_member(1, 0)
    assert_equal(x[0], List[Int]([0, 2, 2, 2, 1]))
    assert_equal(x[1], List[Int]([1, 2, 2, 0]))
    assert_equal(x[2], List[Int]([1, 1]))
    assert_equal(boundary_probe(1, 0), List[Int]([3, 2, 0, 1026, 6, 0]))
    assert_equal(boundary_probe(1, 1), List[Int]([6, 5, 2, 977, 6, 0]))
    assert_equal(boundary_probe(-1, 0), List[Int]([5, 6, 4, 148, 4, 0]))
    assert_equal(boundary_probe(-1, 1), List[Int]([8, 9, 6, 145, 4, 0]))
    assert_equal(boundary_probe(1, 2), List[Int]([9, 8, 4, 887, 6, 0]))
    assert_equal(boundary_probe(1, 3), List[Int]([12, 11, 6, 868, 6, 0]))
    assert_equal(boundary_probe(-1, 2), List[Int]([11, 12, 8, 145, 4, 0]))
    assert_equal(boundary_probe(-1, 3), List[Int]([14, 15, 10, 145, 4, 0]))
    assert_equal(boundary_edge_flags(2), List[Bool]([False,False]))
    assert_equal(boundary_edge_flags(3), List[Bool]([True,True]))
    var refused = False
    try:
        _ = boundary_probe(1, 0, 1)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = boundary_member(1, 9)
    except:
        refused = True
    assert_true(refused)
    require_contract("bounded class-D b=0 replay: eight parameter members, exact support-change witnesses despite equal 145-vertex counts, all-seed graph sizes and half-depths, state-cap and parameter-limit refusal; no family-wide hitting claim")
    require_contract("class-D minus b=0 witness paths at a=0..8: exact seed membership, prescribed child occurrences to offset zero, threshold edges absent below three, and rejection of a perturbed occurrence index; finite calibration of section 4h, not complete-graph closure")
