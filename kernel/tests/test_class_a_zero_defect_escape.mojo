"""Finite literal and physical replay of the strict zero-defect escape table."""

from std.testing import assert_true, assert_equal
from std.sys import argv
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import (
    SeedOverlapTables, build_seed_overlap_tables_screened, interior_overlap,
)
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, _run, geometric_state, verify_member_edge,
)
from psc.class_a_zero_return import _delta
from psc.class_a_x_ladder import reversed_label
from psc.class_a_zero_defect_escape import (
    endpoint_escape, zero_defect_escape, xx5_strict_domain,
)


def _verify_path(tables: SeedOverlapTables, k: Int, t: Int,
                 source: BoundaryLabel, path: List[BoundaryEdge],
                 emit: Bool, kind: String) raises:
    var n = k + t + 3
    var d = k + 2 * t + 5
    var w = source
    var row = String()
    if emit:
        if kind == "endpoint":
            row = "ENDPOINT_PATH " + String(k) + " " + String(t) + " " + (
                String(source.top)) + " " + String(source.bottom) + " " + (
                String(source.y)) + " " + String(len(path))
        else:
            row = "ZERO_DEFECT_PATH " + String(k) + " " + String(t) + " " + (
                String(source.top)) + " " + String(source.bottom) + " " + (
                String(source.x)) + " " + String(source.c) + " " + (
                String(source.y)) + " " + String(len(path))
    for edge in path:
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


def _two_step_run_controls() raises:
    # These sources are outside the zero-defect slice. They exercise the
    # separate Lean two-step RUN/RUN slice using supplied literal addresses,
    # without changing the zero_defect_escape policy or its emitted rows.
    for params in [[0, 0], [0, 2]]:
        var k = params[0]
        var t = params[1]
        var n = k+t+3
        var d = k+2*t+5
        var tables = build_seed_overlap_tables_screened(
            class_member(CLASS_A, n+d, n, n-1))
        var source = BoundaryLabel(0, 1, 0, -n-1, n+2)
        var total = source.x + source.c + source.y
        assert_equal(total, 1)
        assert_equal(source.x + total, _delta(source.top, source.bottom))
        var difference = source.c + (d+1) - (d-n)*total
        assert_equal(difference, 0)
        assert_true(1-n <= difference and difference <= n+d-1)
        assert_true(2*total <= n-1)
        var middle = BoundaryLabel(2, 2, 0, 2, -2)
        var target = BoundaryLabel(1 if n == 3 else 2, 2, 0, 0, 0)
        verify_member_edge(tables, -1, k, n, d, source, 1, 1, middle)
        verify_member_edge(tables, -1, k, n, d, middle, 3, 1, target)
        if t == 0:
            # The sign-reflected sum uses a genuine bottom LAST at n=3.
            source = BoundaryLabel(0, 1, 2, -8, 5)
            total = source.x + source.c + source.y
            assert_equal(total, -1)
            assert_equal(source.x + total, _delta(source.top, source.bottom))
            assert_equal(source.c + (d+1) - (d-n)*total, 0)
            middle = BoundaryLabel(2, 2, 0, -2, 2)
            target = BoundaryLabel(2, 1, 0, 0, 0)
            verify_member_edge(tables, -1, k, n, d, source, 1, 1, middle)
            verify_member_edge(tables, -1, k, n, d, middle, 1, 3, target)
    print("CLASS_A_TWO_STEP_RUN_CONTROLS_PASS", "paths=3 edges=6")


def main() raises:
    var args = argv()
    var emit = len(args) == 2 and args[1] == "--emit"
    if len(args) > 1 and not emit:
        raise Error("only --emit is supported")
    # Exercise each formula branch, including k=0 and k+t=0/1/2 boundaries.
    var members = List[List[Int]]()
    members.append([0, 0])
    members.append([1, 0])
    members.append([0, 1])
    members.append([1, 1])
    members.append([2, 3])
    members.append([3, 2])
    # All xx5 strict-domain/path walls, including LAST versus RUN at D=2.
    members.append([2, 4])
    members.append([3, 5])
    members.append([4, 6])
    members.append([0, 3])
    members.append([0, 4])
    members.append([1, 6])
    members.append([0, 5])
    members.append([0, 8])
    var endpoint_paths = 0
    var slice_paths = 0
    var checked_edges = 0
    var longest = 0
    for parameters in members:
        var k = parameters[0]
        var t = parameters[1]
        var n = k + t + 3
        var d = k + 2 * t + 5
        var tables = build_seed_overlap_tables_screened(
            class_member(CLASS_A, n + d, n, n - 1))
        assert_true(interior_overlap(tables,
            geometric_state(tables, BoundaryLabel(0, 0, -1, 0, 5))) ==
            xx5_strict_domain(k, t))

        # B_ef(s) is the actual LAST/FIRST child, not a quotient label.
        for top in range(2):
            for bottom in range(2):
                var limit = 4 if top == 0 and bottom == 0 else (
                    2 if top == 1 and bottom == 1 else 3)
                if top == 0 and bottom == 0 and xx5_strict_domain(k, t):
                    limit = 5
                for s in range(1, limit + 1):
                    var source = BoundaryLabel(top, bottom,
                        -1 if bottom == 0 else 0,
                        -1 if bottom == 1 else 0, s)
                    var path = endpoint_escape(k, t, top, bottom, s)
                    _verify_path(tables, k, t, source, path, emit, "endpoint")
                    endpoint_paths += 1
                    checked_edges += len(path)

        for top in range(3):
            for bottom in range(3):
                var delta = _delta(top, bottom)
                # The legal one-step target and integral-zero base cases.
                var source = BoundaryLabel(top, bottom, delta,
                    1 - (d + 1) * delta, d * delta - 1)
                var path = zero_defect_escape(k, t, source)
                assert_equal(len(path), 1)
                _verify_path(tables, k, t, source, path, emit, "one_step")
                checked_edges += len(path)
                var zero = BoundaryLabel(top, bottom, 0, 0, 0)
                var zero_path = zero_defect_escape(k, t, zero)
                assert_equal(len(zero_path), 0)
                _verify_path(tables, k, t, zero, zero_path, emit, "zero")

                # Each covered positive gap tail and its genuine reversal.
                var endpoint_top = 1 if top == 2 else 0
                var endpoint_bottom = 1 if bottom == 1 else 0
                var limit = 4 if endpoint_top == 0 and endpoint_bottom == 0 else (
                    2 if endpoint_top == 1 and endpoint_bottom == 1 else 3)
                if endpoint_top == 0 and endpoint_bottom == 0 and xx5_strict_domain(k, t):
                    limit = 5
                for s in range(1, limit + 1):
                    var gap = _run(-1, n, d, top) + s
                    source = BoundaryLabel(top, bottom, delta,
                        gap - (d + 1) * delta, d * delta - gap)
                    for flip in [False, True]:
                        var oriented = reversed_label(source) if flip else source
                        path = zero_defect_escape(k, t, oriented)
                        _verify_path(tables, k, t, oriented, path, emit, "slice")
                        assert_true(len(path) <= 10)
                        longest = max(longest, len(path))
                        slice_paths += 1
                        checked_edges += len(path)

    # X has sum zero but a nonzero first defect, so this slice constructor
    # must not silently turn the remaining BH entry problem into a premise.
    var refused = False
    try:
        _ = zero_defect_escape(0, 0, BoundaryLabel(0, 0, 1, 0, -1))
    except:
        refused = True
    assert_true(refused)

    # The two excluded D=2 walls are genuine non-strict xx5 states.
    for params in [[0, 2], [1, 3]]:
        var k = params[0]
        var t = params[1]
        var n = k+t+3
        var d = k+2*t+5
        var tables = build_seed_overlap_tables_screened(
            class_member(CLASS_A, n+d, n, n-1))
        assert_true(not xx5_strict_domain(k, t))
        assert_true(not interior_overlap(tables,
            geometric_state(tables, BoundaryLabel(0, 0, -1, 0, 5))))
        refused = False
        try:
            _ = endpoint_escape(k, t, 0, 0, 5)
        except:
            refused = True
        assert_true(refused)

    # Original indices remain part of the contract even when the target is
    # zero: a nonexistent first address and a changed zero target both refuse.
    var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, 8, 3, 2))
    var source = BoundaryLabel(1, 0, -1, 0, 1)
    var path = endpoint_escape(0, 0, 1, 0, 1)
    assert_equal(len(path), 1)
    refused = False
    try:
        verify_member_edge(tables, -1, 0, 3, 5, source,
                           len(tables.sigma[source.top]), path[0].j, path[0].target)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        verify_member_edge(tables, -1, 0, 3, 5, source,
                           path[0].i, path[0].j,
                           BoundaryLabel(path[0].target.top, path[0].target.bottom, 0, 0, 1))
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = zero_defect_escape(-1, 0, BoundaryLabel(0, 0, 0, 0, 0))
    except:
        refused = True
    assert_true(refused)
    # Overflow is an inconclusive refusal, never an accepted wrapped path.
    refused = False
    try:
        _ = endpoint_escape(Int.MAX, 0, 0, 0, 1)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = zero_defect_escape(0, 0, BoundaryLabel(0, 0, 0, Int.MAX, -Int.MAX))
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = zero_defect_escape(0, 0, BoundaryLabel(0, 1, 1, Int.MIN, Int.MAX))
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = zero_defect_escape(0, 0, BoundaryLabel(0, 0, 0, 1, 0))
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = endpoint_escape(0, 0, 1, 1, 3)
    except:
        refused = True
    assert_true(refused)

    _two_step_run_controls()
    print("CLASS_A_ZERO_DEFECT_ESCAPE_PASS", "members=", len(members),
          "endpoint_paths=", endpoint_paths, "slice_paths=", slice_paths,
          "checked_edges=", checked_edges, "max_path=", longest)
    require_contract("actual composable integral-zero paths for strict minus-Class-A affine-zero-defect sources; literal-word and strict Perron geometry replay on fourteen branch-boundary members; uniform slice coverage is the separate written theorem, not a finite-sample inference; no all-descendant entry claim")
    require_contract("three supplied two-step RUN/RUN source witnesses with positive and negative total defect, including mixed-letter zero endpoints at n=3; no additional source-cover claim")
