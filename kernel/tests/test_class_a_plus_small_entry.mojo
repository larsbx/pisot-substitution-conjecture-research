"""Complete original-occurrence certificates for the five small plus seams."""
from std.testing import assert_true, assert_equal
from std.sys import argv
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import build_seed_overlap_tables_screened
from psc.class_a_boundary_children import BoundaryLabel
from psc.class_a_x_productivity import terminal
from psc.class_a_plus_small_certificate import (
    bind_small, build_small, distances, select_edges, verify_small,
)
from psc.perron_field3 import CubicElt


def main() raises:
    var args = argv()
    var emit = len(args) == 2 and args[1] == "--emit-certificates"
    if len(args) > 1 and not emit:
        raise Error("only --emit-certificates is supported")
    var states_total = 0
    var edges_total = 0
    var pairs_total = 0
    var paths_total = 0
    var path_edges_total = 0
    var maximum_total = 0
    var refusals = 0
    for n in range(1, 6):
        var d = n+4
        var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, n+d, n, n+1))
        var g = build_small(tables, n, d)
        var distance = distances(g)
        var selected = select_edges(g, distance)
        var counts = verify_small(tables, n, d, g, distance, selected)
        assert_true(counts[0] >= 18 and counts[1] > counts[0])
        assert_true(counts[2] >= counts[1] and counts[3] > 0)
        var plus_middle = False
        for v in range(len(g.states)):
            var w = g.states[v]
            if w == BoundaryLabel(2, 2, 0, -1, 0):
                plus_middle = True
            if v < 18:
                assert_true(w != BoundaryLabel(1, 1, 0, 0, 1))
            assert_true(distance[v] >= 0)
            if w.x == 0 and w.c == 0 and w.y == 0 and w.top != w.bottom:
                assert_true(distance[v] > 0 and len(g.adj[v]) > 0)
            var pairs = 0 if terminal(w) else len(tables.sigma[w.top])*len(tables.sigma[w.bottom])
            if emit:
                print("PLUS_SMALL_VERTEX", n, d, v, w.top, w.bottom, w.x, w.c, w.y,
                      distance[v], selected[v], pairs)
                for z in range(len(g.adj[v])):
                    print("PLUS_SMALL_EDGE", n, d, v, z, g.adj[v][z], g.ii[v][z], g.jj[v][z])
            var row = "PLUS_SMALL_PATH " + String(n) + " " + String(d) + " " + String(v) + " " + String(distance[v])
            var cursor = v
            var steps = 0
            while not terminal(g.states[cursor]):
                var z = selected[cursor]
                assert_true(z >= 0 and z < len(g.adj[cursor]))
                var target = g.adj[cursor][z]
                assert_equal(distance[target], distance[cursor]-1)
                if emit:
                    row += " " + String(g.ii[cursor][z]) + " " + String(g.jj[cursor][z]) + " " + String(target)
                cursor = target
                steps += 1
                assert_true(steps <= distance[v])
            assert_equal(steps, distance[v])
            paths_total += 1
            path_edges_total += steps
            if emit:
                print(row)
        assert_true(plus_middle)
        if emit:
            print("PLUS_SMALL_COMPLETE", n, d, counts[0], counts[1], counts[2], counts[3], counts[4], 6000, 20000000)
        print("CLASS_A_PLUS_SMALL_MEMBER_PASS", n, d, counts[0], counts[1], counts[2], counts[3], counts[4])
        states_total += counts[0]
        edges_total += counts[1]
        pairs_total += counts[2]
        maximum_total = max(maximum_total, counts[3])

        if n == 1:
            var refused = False
            try:
                _ = build_small(tables, 0, 4)
            except:
                refused = True
            assert_true(refused)
            refusals += 1
            refused = False
            try:
                _ = build_small(tables, 1, 5, 18)
            except:
                refused = True
            assert_true(refused)
            refusals += 1
            refused = False
            try:
                _ = build_small(tables, 1, 5, 6000, 1)
            except:
                refused = True
            assert_true(refused)
            refusals += 1
            var missing_seed = g.copy()
            missing_seed.states[0] = missing_seed.states[1]
            refused = False
            try:
                _ = verify_small(tables, n, d, missing_seed, distance, selected)
            except:
                refused = True
            assert_true(refused)
            refusals += 1
            var missing_edge = g.copy()
            _ = missing_edge.adj[0].pop()
            _ = missing_edge.ii[0].pop()
            _ = missing_edge.jj[0].pop()
            refused = False
            try:
                _ = verify_small(tables, n, d, missing_edge, distance, selected)
            except:
                refused = True
            assert_true(refused)
            refusals += 1
            var changed_state = g.copy()
            var old = changed_state.states[18]
            changed_state.states[18] = BoundaryLabel(old.top, old.bottom, old.x+1, old.c, old.y)
            refused = False
            try:
                _ = verify_small(tables, n, d, changed_state, distance, selected)
            except:
                refused = True
            assert_true(refused)
            refusals += 1
            var changed_index = g.copy()
            changed_index.ii[0][0] += 1
            refused = False
            try:
                _ = verify_small(tables, n, d, changed_index, distance, selected)
            except:
                refused = True
            assert_true(refused)
            refusals += 1
            var wrong_distance = distance.copy()
            wrong_distance[0] += 1
            refused = False
            try:
                _ = verify_small(tables, n, d, g, wrong_distance, selected)
            except:
                refused = True
            assert_true(refused)
            refusals += 1
            var wrong_selected = selected.copy()
            wrong_selected[0] = -1
            refused = False
            try:
                _ = verify_small(tables, n, d, g, distance, wrong_selected)
            except:
                refused = True
            assert_true(refused)
            refusals += 1
            var truncated = g.copy()
            _ = truncated.adj.pop()
            refused = False
            try:
                _ = verify_small(tables, n, d, truncated, distance, selected)
            except:
                refused = True
            assert_true(refused)
            refusals += 1
            var bad_cache = tables.copy()
            bad_cache.prefix_positions[1] = CubicElt()
            refused = False
            try:
                bind_small(bad_cache, n, d)
            except:
                refused = True
            assert_true(refused)
            refusals += 1
            var bad_word = tables.copy()
            bad_word.sigma[0][1] = 1
            refused = False
            try:
                bind_small(bad_word, n, d)
            except:
                refused = True
            assert_true(refused)
            refusals += 1
    assert_equal(paths_total, states_total)
    assert_equal(refusals, 12)
    print("CLASS_A_PLUS_FIVE_SMALL_ENTRY_PASS", states_total, edges_total, pairs_total,
          paths_total, path_edges_total, maximum_total, refusals)
    require_contract("ClassAPlusFiveSmallCompleteS18; every original ordered child and every full integral state has an actual typed-zero path; exactly n=1..5,d=n+4; caps refuse")
