"""Exact core and segment support; independent generic occurrence controls."""
from std.collections import Dict
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from a1_normal_form_census import CLASS_B, class_member
from psc.class_b_core_exact import core_graph
from psc.class_b_segment_graph import root_box, segment_children, check_class_b_images, class_b_seed_graph
from psc.overlap_seed_patch import OverlapState, build_seed_overlap_tables_screened, overlap_children_cached, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt
from psc.vertex_coincidence import offset_of, offset_vector, length_matrix
from psc.class_b_middle_tables import middle_rows


def main() raises:
    for eps in [-1, 1]:
        var g = 16 if eps == 1 else 12
        var q = 98 if eps == 1 else 78
        var graph = core_graph(eps == 1, g, q)
        assert_equal(graph.size(), 2299 if eps == 1 else 2275)
        var tables = build_seed_overlap_tables_screened(class_member(CLASS_B, 3 * q + 6 + 6 * eps - g, q, q + eps))
        var cache = Dict[CubicElt, Int]()
        var box = root_box(tables)
        var fast_cache = Dict[CubicElt, Int]()
        # All nine tile pairs and interior/run-end offsets occur in this
        # deterministic stride. Compare exact child supports, not counts.
        var checked = 0
        for i in range(0, graph.size(), 79):
            var v = graph.states[i]
            var slow = overlap_children_cached(tables, cache, v)
            var fast = segment_children(tables, fast_cache, box, v)
            var a = Dict[OverlapState, Int]()
            var b = Dict[OverlapState, Int]()
            for s in slow:
                a[s] = 1
            for s in fast:
                b[s] = 1
            assert_equal(len(a), len(b))
            for s in a.keys():
                assert_true(s in b)
            checked += 1
        assert_true(checked >= 29)
        var refused = False
        try:
            _ = core_graph(eps == 1, g, q, 1)
        except:
            refused = True
        assert_true(refused)
    # Empty runs are legal segment data and must not manufacture RUN children.
    var empty = build_seed_overlap_tables_screened(class_member(CLASS_B, 2, 1, 0))
    check_class_b_images(empty)
    var cache = Dict[CubicElt, Int]()
    var box = root_box(empty)
    var state = OverlapState(2, 2, CubicElt())
    var slow = overlap_children_cached(empty, cache, state)
    var fast = segment_children(empty, cache, box, state)
    var unique = Dict[OverlapState, Int]()
    for s in slow:
        unique[s] = 1
    assert_equal(len(unique), len(fast))
    for s in fast:
        assert_true(s in unique)
    var bad = empty.copy()
    bad.sigma[0][1] = 1
    var refused = False
    try:
        check_class_b_images(bad)
    except:
        refused = True
    assert_true(refused)
    # Actual escaping children at the first omitted low-band residues.
    # These forbid extending the middle table without changing its carrier.
    for eps in [-1, 1]:
        var g = 16 if eps == 1 else 13
        var q = 97 if eps == 1 else 83
        var tables = build_seed_overlap_tables_screened(class_member(CLASS_B, 3 * q + 6 + 6 * eps - g, q, q + eps))
        var lengths = List[CubicElt]([tables.lengths.at(0), tables.lengths.at(1), tables.lengths.at(2)])
        var w = List[Int]([6, 20, -38]) if eps == 1 else List[Int]([6, 14, -32])
        var parent = OverlapState(0, 2, offset_of(lengths, w))
        var child = selected_overlap_child(tables, parent, 0, 99 if eps == 1 else 83)
        var cache = Dict[CubicElt, Int]()
        assert_true(interior_overlap_cached(tables, cache, parent))
        assert_true(interior_overlap_cached(tables, cache, child))
        var cw = offset_vector(length_matrix(tables), child.shift)
        assert_equal(child.top, 0)
        assert_equal(child.bottom, 0)
        assert_equal(cw[0], -6)
        assert_equal(cw[1], -17)
        assert_equal(cw[2], 36)
        var parent_inside = False
        var child_inside = False
        for row in middle_rows(eps):
            if row[0] == 0 and row[1] == 2 and row[2] == 3 * w[0] + w[1] + w[2] and row[3] == w[1] - 3 * w[0] and row[4] * 6 + row[5] <= w[0] and w[0] <= row[6] * 6 + row[7]:
                parent_inside = True
            if row[0] == 0 and row[1] == 0 and row[2] == 1 and row[3] == 1 and row[4] * 6 + row[5] <= -6 and -6 <= row[6] * 6 + row[7]:
                child_inside = True
        assert_true(parent_inside)
        assert_true(not child_inside)
    require_contract("class-B exact bounded strict-core closure contains canonical swap seeds and every vertex reaches offset zero; FIRST/RUN/LAST segment child supports equal generic ordered occurrence supports on deterministic exact states, including an empty y-run; malformed images and exhausted closure caps refuse; finite members only, no uniform BH")
