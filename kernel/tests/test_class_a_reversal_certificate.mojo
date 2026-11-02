"""Finite native reversal quotient: checked occurrence lifts and refusal controls."""

from std.testing import assert_true, assert_equal
from std.sys import argv
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import build_seed_overlap_tables_screened
from psc.class_a_x_productivity import IndexedGraph, build_indexed, backwards, terminal
from psc.class_a_boundary_children import BoundaryLabel
from psc.class_a_reversal_certificate import (
    verify_indexed_reversal_quotient, lift_quotient_edge, verify_finite_distance_certificate, verify_shortest_distance_bounds,
)


def main() raises:
    var args = argv()
    var emit = len(args) == 2 and args[1] == "--emit-certificates"
    var members = List[List[Int]]()
    for k in range(4):
        for t in range(4):
            members.append([k, t])
    members.append([0, 4])
    members.append([4, 0])
    members.append([4, 4])
    members.append([0, 8])
    members.append([8, 0])
    members.append([8, 8])
    var checked_lifts = 0
    for z in range(len(members)):
        var k = members[z][0]
        var t = members[z][1]
        var n = k + t + 3
        var d = k + 2 * t + 5
        var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, n + d, n, n - 1))
        var graph = build_indexed(tables, k, t)
        var q = verify_indexed_reversal_quotient(tables, graph, k, t)
        assert_equal(q.original_edges, 2 * sum_quotient_edges(q.adj))
        var terminals = List[Int]()
        var original_terminals = List[Int]()
        for v in range(len(graph.states)):
            if terminal(graph.states[v]):
                original_terminals.append(v)
        for orb in range(len(q.representatives)):
            if terminal(graph.states[q.representatives[orb]]):
                terminals.append(orb)
        assert_equal(len(terminals), 2)
        var distance = backwards(q.adj, terminals)
        var original_distance = backwards(graph.adj, original_terminals)
        var selected = List[Int](length=len(q.representatives), fill=-1)
        for orb in range(len(q.representatives)):
            assert_true(distance[orb] >= 0)
            if distance[orb] == 0:
                continue
            for e in range(len(q.adj[orb])):
                if distance[q.adj[orb][e]] == distance[orb] - 1:
                    selected[orb] = e
                    break
            assert_true(selected[orb] >= 0)
        q = verify_finite_distance_certificate(tables, graph, k, t, original_distance, distance, selected)
        for v in range(len(graph.states)):
            assert_equal(original_distance[v], distance[q.orbit_of[v]])
            checked_lifts += Int(original_distance[v] > 0)
            if emit:
                var w = graph.states[v]
                print("RC_VERTEX", k, t, v, w.top, w.bottom, w.x, w.c, w.y,
                      q.orbit_of[v], original_distance[v], q.occurrence_pairs[v])
                for e in range(len(graph.adj[v])):
                    print("RC_EDGE", k, t, v, graph.adj[v][e], graph.ii[v][e], graph.jj[v][e])
        if emit:
            for orb in range(len(q.representatives)):
                print("RC_ORBIT", k, t, orb, q.representatives[orb], distance[orb], selected[orb])
            print("RC_COMPLETE", k, t, len(graph.states), len(q.representatives),
                  q.original_edges, 20000000, 6000)

    # Mutations are on separately rebuilt small completed native graphs.
    var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, 8, 3, 2))
    var bad = build_indexed(tables, 0, 0)
    bad.ii[0][0] = -1
    var refused = False
    try:
        _ = verify_indexed_reversal_quotient(tables, bad, 0, 0)
    except:
        refused = True
    assert_true(refused)

    bad = build_indexed(tables, 0, 0)
    # Corrupt a recorded ordered occurrence target, without changing
    # either occurrence index. Full typed child transport must reject.
    bad.adj[0][0] = (bad.adj[0][0] + 1) % len(bad.states)
    refused = False
    try:
        _ = verify_indexed_reversal_quotient(tables, bad, 0, 0)
    except:
        refused = True
    assert_true(refused)

    bad = build_indexed(tables, 0, 0)
    # A malformed terminal edge must not be blessed by orbit compression.
    for v in range(len(bad.states)):
        if terminal(bad.states[v]):
            bad.adj[v].append(v)
            break
    refused = False
    try:
        _ = verify_indexed_reversal_quotient(tables, bad, 0, 0)
    except:
        refused = True
    assert_true(refused)

    bad = build_indexed(tables, 0, 0)
    refused = False
    try:
        _ = verify_indexed_reversal_quotient(tables, bad, 0, 1)
    except:
        refused = True
    assert_true(refused)

    refused = False
    try:
        _ = build_indexed(tables, 0, 0, 18)
    except:
        refused = True
    assert_true(refused)

    # Delete both transposed occurrences, preserving reversal symmetry.
    bad = build_indexed(tables, 0, 0)
    var good_q = verify_indexed_reversal_quotient(tables, bad, 0, 0)
    var rv = good_q.partner[0]
    var i = bad.ii[0][0]
    var j = bad.jj[0][0]
    for v in [0, rv]:
        var aa = i if v == 0 else j
        var bb = j if v == 0 else i
        var targets = List[Int]()
        var top_indices = List[Int]()
        var bottom_indices = List[Int]()
        for e in range(len(bad.adj[v])):
            if bad.ii[v][e] != aa or bad.jj[v][e] != bb:
                targets.append(bad.adj[v][e])
                top_indices.append(bad.ii[v][e])
                bottom_indices.append(bad.jj[v][e])
        bad.adj[v] = targets^
        bad.ii[v] = top_indices^
        bad.jj[v] = bottom_indices^
    refused = False
    try:
        _ = verify_indexed_reversal_quotient(tables, bad, 0, 0)
    except:
        refused = True
    assert_true(refused)

    var good = build_indexed(tables, 0, 0)
    var q = verify_indexed_reversal_quotient(tables, good, 0, 0)
    var roots = List[Int]()
    var qroots = List[Int]()
    for v in range(len(good.states)):
        if terminal(good.states[v]):
            roots.append(v)
            qroots.append(q.orbit_of[v])
    var od = backwards(good.adj, roots)
    var qd = backwards(q.adj, qroots)
    var selected = List[Int](length=len(q.representatives), fill=-1)
    for orb in range(len(q.representatives)):
        for e in range(len(q.adj[orb])):
            if qd[q.adj[orb][e]] == qd[orb] - 1:
                selected[orb] = e
                break
    # Bad distance, fake zero terminal, nonexistent selected edge, fabricated
    # terminal path, and independent pair/state verification cap refusal.
    for mutation in range(6):
        var a = od.copy()
        var b = qd.copy()
        var c = selected.copy()
        var cap = 20000000
        var state_cap = 6000
        if mutation == 0:
            a[0] += 1
        elif mutation == 1:
            a[0] = 0
            a[q.partner[0]] = 0
            b[q.orbit_of[0]] = 0
        elif mutation == 2:
            c[q.orbit_of[0]] = len(q.adj[q.orbit_of[0]])
        elif mutation == 3:
            c[qroots[0]] = 0
        elif mutation == 4:
            cap = 1
        else:
            state_cap = len(good.states) - 1
        refused = False
        try:
            _ = verify_finite_distance_certificate(tables, good, 0, 0, a, b, c, cap, state_cap)
        except:
            refused = True
        assert_true(refused)
    # A genuine length-two path exists, but the direct edge makes it NON-shortest.
    var triangle = List[List[Int]]()
    triangle.append([1, 2])
    triangle.append([2])
    triangle.append(List[Int]())
    refused = False
    try:
        verify_shortest_distance_bounds(triangle, [2, 1, 0])
    except:
        refused = True
    assert_true(refused)
    verify_shortest_distance_bounds(triangle, [1, 1, 0])
    var exact_cap = 0
    for pairs in q.occurrence_pairs:
        exact_cap += pairs
    _ = verify_indexed_reversal_quotient(tables, good, 0, 0, exact_cap, len(good.states))
    refused = False
    try:
        _ = verify_indexed_reversal_quotient(tables, good, 0, 0, exact_cap - 1)
    except:
        refused = True
    assert_true(refused)
    var roots_only = List[BoundaryLabel]()
    var empty_rows = List[List[Int]]()
    for root in roots:
        roots_only.append(good.states[root])
        empty_rows.append(List[Int]())
    var missing_seeds = IndexedGraph(roots_only, empty_rows, empty_rows, empty_rows)
    refused = False
    try:
        _ = verify_indexed_reversal_quotient(tables, missing_seeds, 0, 0)
    except:
        refused = True
    assert_true(refused)
    # Strict, absorbing, reversal-fixed c/c coincidence is unrelated to S18.
    var extra = good.copy()
    extra.states.append(BoundaryLabel(1, 1, 0, 0, 0))
    extra.adj.append(List[Int]())
    extra.ii.append(List[Int]())
    extra.jj.append(List[Int]())
    refused = False
    try:
        _ = verify_indexed_reversal_quotient(tables, extra, 0, 0)
    except:
        refused = True
    assert_true(refused)
    print("RC_NEGATIVE_CONTROLS_PASS", 16)

    print("CLASS_A_NATIVE_REVERSAL_QUOTIENT_PASS", checked_lifts)
    require_contract("ClassACompleteS18LiteralOccurrencesAndExactQuotientDistances; finite specimens only; not universal BH")


def sum_quotient_edges(adj: List[List[Int]]) -> Int:
    var n = 0
    for row in adj:
        n += len(row)
    return n
