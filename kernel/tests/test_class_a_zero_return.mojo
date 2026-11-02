"""Uniform Class-A one-step zero predecessor: actual indexed native controls."""

from std.testing import assert_true, assert_equal
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import build_seed_overlap_tables_screened
from psc.class_a_boundary_children import BoundaryLabel
from psc.class_a_x_productivity import build_indexed, terminal
from psc.class_a_zero_return import (
    zero_return_addresses, one_step_zero_at, zero_return_predecessor,
    independently_check_zero_return,
)


def main() raises:
    var members = List[List[Int]]()
    members.append([0, 0])
    members.append([1, 2])
    members.append([3, 0])
    members.append([0, 3])
    var actual_pairs = 0
    var refused_mixed = 0
    var witnessed_zero = 0
    for params in members:
        var k = params[0]
        var t = params[1]
        var n = k + t + 3
        var d = k + 2 * t + 5
        var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, n+d, n, n-1))
        # Every legal zero-return predecessor must give the zero vector,
        # without assuming that its parent overlap is strict.
        for top in range(3):
            for bottom in range(3):
                for i in range(len(tables.sigma[top])):
                    for j in range(len(tables.sigma[bottom])):
                        if (i == 0) != (j == 0):
                            var failed = False
                            try:
                                _ = zero_return_predecessor(k, t, top, bottom, i, j)
                            except:
                                failed = True
                            assert_true(failed)
                            refused_mixed += 1
                            continue
                        var w = zero_return_predecessor(k, t, top, bottom, i, j)
                        assert_true(independently_check_zero_return(k, t, w, i, j))
                        var interval = zero_return_addresses(k, t, w)
                        assert_true(one_step_zero_at(k, t, w, i, j))
                        if i == 0:
                            assert_true(interval.first_first)
                        else:
                            assert_true(interval.lo <= i and i <= interval.hi)
                            assert_equal(i-j, interval.gap)
                        actual_pairs += 1
                        # Full-offset mutation rejects the same occurrence.
                        var changed = BoundaryLabel(top, bottom, w.x, w.c, w.y+1)
                        assert_true(not independently_check_zero_return(k, t, changed, i, j))

        # Stronger negative control: MANY source vectors checked against
        # actual prefix transport, including mixed FIRST/RUN and LAST.
        for top in range(3):
            for bottom in range(3):
                for p in range(-1, 2):
                    for q in range(-1, 2):
                        for r in range(-1, 2):
                            var w = BoundaryLabel(top, bottom, p, q, r)
                            var interval = zero_return_addresses(k, t, w)
                            var observed = 0
                            for i in range(len(tables.sigma[top])):
                                for j in range(len(tables.sigma[bottom])):
                                    if independently_check_zero_return(k, t, w, i, j):
                                        observed += 1
                            assert_equal(observed, interval.positive_count() +
                                         (1 if interval.first_first else 0))
                            witnessed_zero += observed

    # The canonical X hub is definitely not one literal step from zero,
    # uniformly in k,t. Neither an accepted selected path nor a quotient
    # edge is allowed to override this arithmetic obstruction.
    var x = BoundaryLabel(0, 0, 1, 0, -1)
    var h = zero_return_addresses(0, 0, x)
    assert_equal(h.positive_count(), 0)
    assert_true(not h.first_first)

    # Compare every actual enumerated outgoing edge in one FULL completed
    # S18 finite graph. Typed full-zero coincidence vertices are terminalized.
    var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, 8, 3, 2))
    var graph = build_indexed(tables, 0, 0)
    assert_equal(len(graph.states), 784)
    var zero_edges = 0
    for v in range(len(graph.states)):
        var w = graph.states[v]
        if terminal(w):
            assert_equal(len(graph.adj[v]), 0)
            continue
        var hits = zero_return_addresses(0, 0, w)
        var actual_hits = 0
        for e in range(len(graph.adj[v])):
            var i = graph.ii[v][e]
            var j = graph.jj[v][e]
            var child = graph.states[graph.adj[v][e]]
            var hit = child.x == 0 and child.c == 0 and child.y == 0
            assert_true(hit == one_step_zero_at(0, 0, w, i, j))
            if hit:
                actual_hits += 1
                zero_edges += 1
        assert_equal(actual_hits, hits.positive_count() +
                     (1 if hits.first_first else 0))

    # Impossible address, invalid parameter and false mixed-first
    # predecessor must REFUSE rather than imply a one-step success.
    var refused = False
    try:
        _ = one_step_zero_at(0, 0, x, -1, 0)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = zero_return_predecessor(-1, 0, 0, 0, 1, 1)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = zero_return_predecessor(0, 0, 0, 1, 0, 1)
    except:
        refused = True
    assert_true(refused)

    print("CLASS_A_ZERO_RETURN_INTERVAL_PASS", actual_pairs,
          refused_mixed, witnessed_zero, zero_edges)
    require_contract("uniform exact one-step offset-zero predecessor interval for minus Class A; actual literal Parikh and finite outgoing graph checks; no higher-level hitting or universal BH")
