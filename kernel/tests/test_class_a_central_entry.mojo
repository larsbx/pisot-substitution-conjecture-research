"""Literal-address replay of the exact central recurrence and cycle exits."""

from std.testing import assert_true, assert_equal
from std.sys import argv
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import (
    SeedOverlapTables, build_seed_overlap_tables_screened, interior_overlap,
)
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, geometric_state, member_transport,
    verify_member_edge,
)
from psc.class_a_central_entry import (
    is_central, nearest_run_child, cycle_escape, central_escape,
)
from psc.class_a_x_ladder import reversed_label


def _verify(tables: SeedOverlapTables, k: Int, t: Int,
            source: BoundaryLabel, path: List[BoundaryEdge],
            emit: Bool, kind: String) raises:
    var n = k+t+3
    var d = k+2*t+5
    var w = source
    var row = kind + " " + String(k) + " " + String(t) + " " + (
        String(source.top)) + " " + String(source.bottom) + " " + (
        String(source.x)) + " " + String(source.c) + " " + (
        String(source.y)) + " " + String(len(path))
    assert_true(is_central(tables, source))
    for edge in path:
        assert_true(w.x != 0 or w.c != 0 or w.y != 0)
        verify_member_edge(tables, -1, k, n, d,
                           w, edge.i, edge.j, edge.target)
        w = edge.target
        if emit:
            row += " " + String(edge.i) + " " + String(edge.j) + " " + (
                String(w.top)) + " " + String(w.bottom) + " " + (
                String(w.x)) + " " + String(w.c) + " " + String(w.y)
    assert_equal(w.x, 0)
    assert_equal(w.c, 0)
    assert_equal(w.y, 0)
    if emit:
        print(row)


def main() raises:
    var args = argv()
    var emit = len(args) == 2 and args[1] == "--emit"
    if len(args) > 1 and not emit:
        raise Error("only --emit is supported")
    var members: List[List[Int]] = [
        [0, 3], [1, 2], [2, 1], [3, 0], [0, 4],
        [0, 20], [0, 64], [32, 0], [8, 8],
    ]
    var central_paths = 0
    var cycle_paths = 0
    var checked_edges = 0
    var maximum = 0
    for parameters in members:
        var k = parameters[0]
        var t = parameters[1]
        var n = k+t+3
        var d = k+2*t+5
        var tables = build_seed_overlap_tables_screened(
            class_member(CLASS_A, n+d, n, n-1))

        # These coordinates are specified independently of the old seed graph.
        # The exact central interval contains one integer r for each p,q.
        # rho<1 and h<1/(n+2) give the complete small r search interval.
        for p in [-12, -3, 0, 3, 12]:
            for q in [-30, -9, -1, 0, 1, 9, 30]:
                var base = -2*p-q
                var padding = abs(p) + abs(q)//(n+2) + 2
                var found = 0
                for r in range(base-padding, base+padding+1):
                    var source = BoundaryLabel(2, 2, p, q, r)
                    if not is_central(tables, source):
                        continue
                    found += 1
                    var path = central_escape(tables, k, t, source)
                    _verify(tables, k, t, source, path, emit, "CENTRAL_PATH")
                    central_paths += 1
                    checked_edges += len(path)
                    maximum = max(maximum, len(path))
                assert_equal(found, 1)

        # The bound beta+1<n+4 implies every central positive H is among
        # these candidates. Test every admitted cycle and its true reversal.
        var K = k+1
        for H in range(1, (n+4)//(2*K)+2):
            var source = BoundaryLabel(2, 2, H, 3*H, -6*H)
            if not is_central(tables, source):
                continue
            var automatic = nearest_run_child(tables, k, t, source)
            assert_true(automatic.target == reversed_label(source))
            var back = nearest_run_child(tables, k, t, automatic.target)
            assert_true(back.target == source)
            # The selected two-cycle is nonzero; the escape changes its choice.
            assert_true(source.x != 0)
            for flip in [False, True]:
                var oriented = reversed_label(source) if flip else source
                var path = cycle_escape(tables, k, t, H, flip)
                _verify(tables, k, t, oriented, path, emit, "CYCLE_PATH")
                cycle_paths += 1
                checked_edges += len(path)
                maximum = max(maximum, len(path))
                if k == 0 and t == 3 and H == 3:
                    assert_equal(len(path), 5)
                    # (1,18) uses the original LAST x at n=6.
                    assert_equal(path[3].i, 18 if flip else 1)
                    assert_equal(path[3].j, 1 if flip else 18)
                    assert_equal(path[3].target.top, 0 if flip else 2)
                    assert_equal(path[3].target.bottom, 2 if flip else 0)

    var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, 17, 6, 5))
    var control = BoundaryLabel(2, 2, 0, 1, -1)
    var baseline = nearest_run_child(tables, 0, 3, control)
    assert_equal(baseline.i, 2)
    assert_equal(baseline.j, 1)
    assert_true(baseline.target == BoundaryLabel(2, 2, 0, 0, 0))
    var positive = central_escape(tables, 0, 3, control)
    assert_equal(len(positive), 1)
    var refused = False
    try:
        _ = nearest_run_child(tables, 0, 3, BoundaryLabel(0, 0, 0, 0, 0))
    except:
        refused = True
    assert_true(refused)

    var noncentral = BoundaryLabel(2, 2, 0, 5, -5)
    assert_true(interior_overlap(tables, geometric_state(tables, noncentral)))
    assert_true(not is_central(tables, noncentral))
    refused = False
    try:
        _ = central_escape(tables, 0, 3, noncentral)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        verify_member_edge(tables, -1, 0, 6, 11, control,
                           baseline.j, baseline.i, baseline.target)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        verify_member_edge(tables, -1, 0, 6, 11, control,
                           6, baseline.j, baseline.target)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        verify_member_edge(tables, -1, 0, 6, 11, control,
                           baseline.i, baseline.j, BoundaryLabel(2, 2, 0, 0, 1))
    except:
        refused = True
    assert_true(refused)

    # Successful fixtures are checked before entering any expected-refusal catch.
    var cycle_source = BoundaryLabel(2, 2, 3, 9, -18)
    var cycle_positive = cycle_escape(tables, 0, 3, 3)
    assert_equal(len(cycle_positive), 5)
    refused = False
    try:
        _ = cycle_escape(tables, 0, 3, 3, False, 4)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = central_escape(tables, 0, 3, cycle_source, 0)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = cycle_escape(tables, 0, 3, 0)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = cycle_escape(tables, 0, 3, 5)
    except:
        refused = True
    assert_true(refused)

    var short_tables = build_seed_overlap_tables_screened(class_member(CLASS_A, 8, 3, 2))
    refused = False
    try:
        _ = central_escape(short_tables, 0, 0, BoundaryLabel(2, 2, 0, 0, 0))
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = central_escape(tables, -1, 3, control)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = central_escape(tables, Int.MAX, 0, control)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = cycle_escape(tables, 0, 3, Int.MAX)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = central_escape(tables, 0, 3, BoundaryLabel(2, 2, Int.MIN, 0, 0))
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = central_escape(short_tables, 0, 3, control)
    except:
        refused = True
    assert_true(refused)

    assert_equal(central_paths, 315)
    print("CLASS_A_CENTRAL_ENTRY_PASS", "members=", len(members),
          "central_paths=", central_paths, "cycle_paths=", cycle_paths,
          "checked_edges=", checked_edges, "max_path=", maximum)
    require_contract("exact nearest RUN occurrence selection from central y/y minus-Class-A sources n>=6; original ordered indices, full integral offsets, strict geometry and first-zero terminal policy; canonical cycle exits including every small KH case and the n=6 LAST correction; finite replay is separate from the written all-source entrance and termination proof")
