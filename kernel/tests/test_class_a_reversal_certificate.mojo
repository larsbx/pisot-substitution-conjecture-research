"""Finite native reversal quotient: checked occurrence lifts and refusal controls."""

from std.testing import assert_true, assert_equal
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import build_seed_overlap_tables_screened
from psc.class_a_x_productivity import build_indexed, backwards, terminal
from psc.class_a_reversal_certificate import (
    verify_indexed_reversal_quotient, lift_quotient_edge,
)


def main() raises:
    var members = List[List[Int]]()
    members.append([0, 0])
    members.append([3, 0])
    members.append([0, 3])
    var expected_vertices: List[Int] = [784, 352, 1440]
    var expected_quotients: List[Int] = [393, 177, 721]
    var checked_lifts = 0
    for z in range(len(members)):
        var k = members[z][0]
        var t = members[z][1]
        var n = k + t + 3
        var d = k + 2 * t + 5
        var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, n + d, n, n - 1))
        var graph = build_indexed(tables, k, t)
        var q = verify_indexed_reversal_quotient(tables, graph, k, t)
        assert_equal(len(graph.states), expected_vertices[z])
        assert_equal(len(q.representatives), expected_quotients[z])
        assert_equal(q.original_edges, 2 * sum_quotient_edges(q.adj))
        var terminals = List[Int]()
        for orb in range(len(q.representatives)):
            if terminal(graph.states[q.representatives[orb]]):
                terminals.append(orb)
        assert_equal(len(terminals), 2)
        var distance = backwards(q.adj, terminals)
        for v in range(len(graph.states)):
            var orbit = q.orbit_of[v]
            assert_true(distance[orbit] >= 0)
            if terminal(graph.states[v]):
                assert_equal(distance[orbit], 0)
                continue
            var chosen = -1
            for e in range(len(q.adj[orbit])):
                if distance[q.adj[orbit][e]] == distance[orbit] - 1:
                    chosen = e
                    break
            assert_true(chosen >= 0)
            var dst = lift_quotient_edge(tables, graph, q, v, chosen, k, t)
            assert_equal(q.orbit_of[dst], q.adj[orbit][chosen])
            assert_equal(distance[q.orbit_of[dst]], distance[orbit] - 1)
            checked_lifts += 1

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
    bad.adj[0][0] = 0
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

    print("CLASS_A_NATIVE_REVERSAL_QUOTIENT_PASS", checked_lifts)
    require_contract("ClassAExactFiniteReversalOrbitsAndLiftedSelectedRanks; complete native builder and independent differential coverage required; not universal BH")


def sum_quotient_edges(adj: List[List[Int]]) -> Int:
    var n = 0
    for row in adj:
        n += len(row)
    return n
