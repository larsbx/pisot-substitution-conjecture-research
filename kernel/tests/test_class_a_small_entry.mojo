"""Fresh complete outgoing/distance certificates for the six n<6 S18 cases."""

from std.testing import assert_true, assert_equal
from std.sys import argv
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import build_seed_overlap_tables_screened
from psc.class_a_x_productivity import build_indexed, backwards, terminal
from psc.class_a_reversal_certificate import (
    verify_indexed_reversal_quotient, verify_finite_distance_certificate,
)


def main() raises:
    var args = argv()
    var emit = len(args) == 2 and args[1] == "--emit-certificates"
    if len(args) > 1 and not emit:
        raise Error("only --emit-certificates is supported")
    var members: List[List[Int]] = [[0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [2, 0]]
    var expected_states: List[Int] = [784, 1010, 1220, 436, 642, 378]
    var expected_edges: List[Int] = [4788, 7752, 11226, 3142, 5636, 3144]
    var states_total = 0
    var edges_total = 0
    var pairs_total = 0
    for index in range(len(members)):
        var k = members[index][0]
        var t = members[index][1]
        var n = k+t+3
        var d = k+2*t+5
        assert_true(n < 6)
        var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, n+d, n, n-1))
        var graph = build_indexed(tables, k, t)
        var q = verify_indexed_reversal_quotient(tables, graph, k, t)
        var roots = List[Int]()
        var quotient_roots = List[Int]()
        for v in range(len(graph.states)):
            if terminal(graph.states[v]):
                roots.append(v)
        for orbit in range(len(q.representatives)):
            if terminal(graph.states[q.representatives[orbit]]):
                quotient_roots.append(orbit)
        var original_distance = backwards(graph.adj, roots)
        var distance = backwards(q.adj, quotient_roots)
        var selected = List[Int](length=len(q.representatives), fill=-1)
        for orbit in range(len(q.representatives)):
            assert_true(distance[orbit] >= 0)
            if distance[orbit] == 0:
                continue
            for edge in range(len(q.adj[orbit])):
                if distance[q.adj[orbit][edge]] == distance[orbit]-1:
                    selected[orbit] = edge
                    break
            assert_true(selected[orbit] >= 0)
        q = verify_finite_distance_certificate(tables, graph, k, t,
                                                original_distance, distance, selected)
        assert_equal(len(graph.states), expected_states[index])
        assert_equal(q.original_edges, expected_edges[index])
        var pairs = 0
        var maximum = 0
        for v in range(len(graph.states)):
            assert_equal(original_distance[v], distance[q.orbit_of[v]])
            pairs += q.occurrence_pairs[v]
            maximum = max(maximum, original_distance[v])
            if emit:
                var w = graph.states[v]
                print("SMALL_VERTEX", k, t, v, w.top, w.bottom, w.x, w.c, w.y,
                      q.orbit_of[v], original_distance[v], q.occurrence_pairs[v])
                for edge in range(len(graph.adj[v])):
                    print("SMALL_EDGE", k, t, v, graph.adj[v][edge],
                          graph.ii[v][edge], graph.jj[v][edge])
        if emit:
            for orbit in range(len(q.representatives)):
                print("SMALL_ORBIT", k, t, orbit, q.representatives[orbit],
                      distance[orbit], selected[orbit])
            print("SMALL_COMPLETE", k, t, len(graph.states), len(q.representatives),
                  q.original_edges, 20000000, 6000)
        print("CLASS_A_SMALL_MEMBER_PASS", k, t, len(graph.states), q.original_edges,
              pairs, maximum)
        states_total += len(graph.states)
        edges_total += q.original_edges
        pairs_total += pairs
    assert_equal(states_total, 4470)
    assert_equal(edges_total, 35688)
    assert_equal(pairs_total, 351816)
    print("CLASS_A_SIX_SMALL_ENTRY_PASS", states_total, edges_total, pairs_total)
    require_contract("ClassASixSmallCompleteS18EntryCertificates; all actual children and every source zero hit; n<6")
