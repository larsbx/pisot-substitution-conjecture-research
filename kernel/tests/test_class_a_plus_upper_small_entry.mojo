"""Complete original-occurrence S18 certificates for the 70 upper plus members
n=0..6, n+5<=d<=2n+11, below the n>=7 all-source entry theorem.

Same exact builder, verifier and record format as the five-seam test; caps
refuse. Scope: the eighteen canonical swap sources and everything they reach,
not arbitrary strict integral sources."""
from std.testing import assert_true, assert_equal
from std.sys import argv
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import build_seed_overlap_tables_screened
from psc.class_a_x_productivity import terminal
from psc.class_a_plus_small_certificate import (
    build_small, distances, select_edges, verify_small, upper_small_member,
)


def refuses_build(n: Int, d: Int, p: Int, q: Int, r: Int, state_cap: Int=6000) raises -> Bool:
    try:
        _ = build_small(build_seed_overlap_tables_screened(class_member(CLASS_A, p, q, r)), n, d, state_cap)
    except:
        return True
    return False


def main() raises:
    var args = argv()
    var emit = len(args) == 2 and args[1] == "--emit-certificates"
    if len(args) > 1 and not emit:
        raise Error("only --emit-certificates is supported")
    var members = 0
    var states_total = 0
    var edges_total = 0
    var pairs_total = 0
    var paths_total = 0
    var path_edges_total = 0
    var maximum_total = 0
    for n in range(0, 7):
        for d in range(n+5, 2*n+12):
            assert_true(upper_small_member(n, d))
            var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, n+d, n, n+1))
            var g = build_small(tables, n, d)
            var distance = distances(g)
            var selected = select_edges(g, distance)
            var counts = verify_small(tables, n, d, g, distance, selected)
            assert_true(counts[0] >= 18 and counts[1] > counts[0])
            assert_true(counts[2] >= counts[1] and counts[3] > 0)
            for v in range(len(g.states)):
                var w = g.states[v]
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
            if emit:
                print("PLUS_SMALL_COMPLETE", n, d, counts[0], counts[1], counts[2], counts[3], counts[4], 6000, 20000000)
            print("CLASS_A_PLUS_SMALL_MEMBER_PASS", n, d, counts[0], counts[1], counts[2], counts[3], counts[4])
            members += 1
            states_total += counts[0]
            edges_total += counts[1]
            pairs_total += counts[2]
            maximum_total = max(maximum_total, counts[3])
    assert_equal(members, 70)
    assert_equal(paths_total, states_total)
    # Refusal controls: the theorem's first member, the first non-PIP member,
    # an insufficient state cap, and a mutated certificate.
    var refusals = 0
    assert_true(not upper_small_member(7, 12) and refuses_build(7, 12, 19, 7, 8))
    refusals += 1
    assert_true(not upper_small_member(0, 12) and refuses_build(0, 12, 12, 0, 1))
    refusals += 1
    assert_true(refuses_build(0, 5, 5, 0, 1, 18))
    refusals += 1
    var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, 7, 1, 2))
    var g = build_small(tables, 1, 6)
    var distance = distances(g)
    var selected = select_edges(g, distance)
    var wrong_distance = distance.copy()
    wrong_distance[0] += 1
    var refused = False
    try:
        _ = verify_small(tables, 1, 6, g, wrong_distance, selected)
    except:
        refused = True
    assert_true(refused)
    refusals += 1
    print("CLASS_A_PLUS_UPPER_SMALL_ENTRY_PASS", states_total, edges_total, pairs_total,
          paths_total, path_edges_total, maximum_total, refusals)
    require_contract("ClassAPlusUpperSmallCompleteS18; every original ordered child and every full integral state reached from the eighteen swap sources has an actual typed-zero path; exactly n=0..6,n+5<=d<=2n+11; caps refuse")
