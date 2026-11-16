"""Exact original-address replay in the lower minus-Class-A chamber."""

from std.testing import assert_true, assert_equal
from std.sys import argv
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import (
    SeedOverlapTables, build_seed_overlap_tables_screened, interior_overlap,
)
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, geometric_state
from psc.class_a_x_ladder import reversed_label
from psc.class_a_minus_constant_entry import (
    _bind, _verify_bound_edge, is_central, member_transport, verify_member_edge,
    nearest_run_child, cycle_escape, central_escape,
)
from psc.perron_field3 import CubicElt


def _verify(tables: SeedOverlapTables, n: Int, d: Int,
            source: BoundaryLabel, path: List[BoundaryEdge],
            emit: Bool, kind: String) raises:
    _bind(tables, n, d)
    var w = source
    var row = kind + " " + String(n) + " " + String(d) + " " + (
        String(source.top)) + " " + String(source.bottom) + " " + (
        String(source.x)) + " " + String(source.c) + " " + (
        String(source.y)) + " " + String(len(path))
    assert_true(is_central(tables, source))
    for edge in path:
        assert_true(w.x != 0 or w.c != 0 or w.y != 0)
        _verify_bound_edge(tables, n, d, w, edge.i, edge.j, edge.target)
        assert_true(edge.i >= 1 and edge.i <= n-1)
        assert_true(edge.j >= 1 and edge.j <= n-1)
        w = edge.target
        assert_equal(w.top, 2)
        assert_equal(w.bottom, 2)
        if emit:
            row += " " + String(edge.i) + " " + String(edge.j) + " " + (
                String(w.top)) + " " + String(w.bottom) + " " + (
                String(w.x)) + " " + String(w.c) + " " + String(w.y)
    assert_equal(w.x, 0)
    assert_equal(w.c, 0)
    assert_equal(w.y, 0)
    assert_equal(w.top, w.bottom)
    if emit:
        print(row)


def main() raises:
    var args = argv()
    var emit = len(args) == 2 and args[1] == "--emit"
    if len(args) > 1 and not emit:
        raise Error("only --emit is supported")
    var members = 0
    var central_paths = 0
    var cycle_paths = 0
    var checked_edges = 0
    var maximum = 0
    for d in [5, 7, 11]:
        for n in [d+1, 2*d-1, 2*d, 4*d-1, 4*d, 5*d-1, 5*d, 12*d, 24*d]:
            members += 1
            var tables = build_seed_overlap_tables_screened(
                class_member(CLASS_A, n+d, n, n-1))
            _bind(tables, n, d)
            # All sources are independent of any archived seed-graph cover.
            # Lx<2 and h<1/(n+1) give this complete finite r interval.
            for p in [-12, -3, 0, 3, 12]:
                for q in [-30, -9, -1, 0, 1, 9, 30]:
                    var base = -p-q
                    var padding = abs(p) + abs(q)//(n+1) + 2
                    var found = 0
                    for r in range(base-padding, base+padding+1):
                        var source = BoundaryLabel(2, 2, p, q, r)
                        if not is_central(tables, source):
                            continue
                        found += 1
                        var path = central_escape(tables, n, d, source)
                        _verify(tables, n, d, source, path, emit, "MINUS_CENTRAL_PATH")
                        central_paths += 1
                        checked_edges += len(path)
                        maximum = max(maximum, len(path))
                    assert_equal(found, 1)
            # Integer centrality is exactly 2dH<=n. Include every admitted H
            # and its reversal; the largest fixture height is twelve.
            for H in range(1, n//(2*d)+1):
                var source = BoundaryLabel(2, 2, H, -H, 0)
                assert_true(is_central(tables, source))
                for flip in [False, True]:
                    var oriented = reversed_label(source) if flip else source
                    var automatic = nearest_run_child(tables, n, d, oriented)
                    assert_true(automatic.target == oriented)
                    assert_true(automatic.target.x != 0)
                    var path = cycle_escape(tables, n, d, H, flip)
                    assert_equal(len(path), 3*H)
                    _verify(tables, n, d, oriented, path, emit, "MINUS_CONSTANT_PATH")
                    for index in range(H):
                        var lower = H-index-1
                        var expected = BoundaryLabel(2, 2, lower, -lower, 0)
                        if flip:
                            expected = reversed_label(expected)
                        assert_true(path[3*index+2].target == expected)
                    cycle_paths += 1
                    checked_edges += len(path)
                    maximum = max(maximum, len(path))
            var above = n//(2*d)+1
            assert_true(not is_central(tables, BoundaryLabel(2, 2, above, -above, 0)))

    var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, 15, 10, 9))
    var control = BoundaryLabel(2, 2, 0, 1, -1)
    var baseline = nearest_run_child(tables, 10, 5, control)
    assert_equal(baseline.i, 2)
    assert_equal(baseline.j, 1)
    assert_true(baseline.target == BoundaryLabel(2, 2, 0, 0, 0))
    verify_member_edge(tables, 10, 5, control, baseline.i, baseline.j, baseline.target)
    var positive = central_escape(tables, 10, 5, control)
    assert_equal(len(positive), 1)
    var empty = central_escape(tables, 10, 5, BoundaryLabel(2, 2, 0, 0, 0), 0)
    assert_equal(len(empty), 0)
    var constant = BoundaryLabel(2, 2, 1, -1, 0)
    var constant_positive = cycle_escape(tables, 10, 5, 1)
    assert_equal(len(constant_positive), 3)
    assert_equal(constant_positive[0].i, 7)
    assert_equal(constant_positive[0].j, 1)
    assert_equal(constant_positive[1].i, 1)
    assert_equal(constant_positive[1].j, 7)
    assert_equal(constant_positive[2].i, 1)
    assert_equal(constant_positive[2].j, 3)
    assert_equal(len(central_escape(tables, 10, 5, constant)), 3)

    var refused = False
    try:
        _ = central_escape(tables, 10, 5, BoundaryLabel(0, 0, 0, 0, 0))
    except:
        refused = True
    assert_true(refused)
    var noncentral = BoundaryLabel(2, 2, 0, 6, -6)
    assert_true(interior_overlap(tables, geometric_state(tables, noncentral)))
    assert_true(not is_central(tables, noncentral))
    refused = False
    try:
        _ = nearest_run_child(tables, 10, 5, noncentral)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        verify_member_edge(tables, 10, 5, control, baseline.j, baseline.i, baseline.target)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = member_transport(10, 5, control, 11, 1)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        verify_member_edge(tables, 10, 5, control, baseline.i, baseline.j,
                           BoundaryLabel(2, 2, 0, 0, 1))
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = central_escape(tables, 10, 5, control, 0)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = central_escape(tables, 10, 5, constant, 2)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = cycle_escape(tables, 10, 5, 1, False, 2)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = central_escape(tables, 10, 5, control, -1)
    except:
        refused = True
    assert_true(refused)
    for H in [0, -1, 2, Int.MAX]:
        refused = False
        try:
            _ = cycle_escape(tables, 10, 5, H)
        except:
            refused = True
        assert_true(refused)
    for parameters in [[10, 4], [5, 5], [-1, 5], [Int.MAX, 5], [Int.MAX, Int.MAX]]:
        refused = False
        try:
            _ = central_escape(tables, parameters[0], parameters[1], control)
        except:
            refused = True
        assert_true(refused)
    refused = False
    try:
        _ = central_escape(tables, 10, 5, BoundaryLabel(2, 2, Int.MIN, 0, 0))
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = central_escape(tables, 11, 5, BoundaryLabel(2, 2, 0, 0, 0))
    except:
        refused = True
    assert_true(refused)

    # A zero source cannot bypass full word, field or prefix-cache binding.
    var wrong_words = tables.copy()
    wrong_words.sigma[0][0] = 2
    wrong_words.sigma[0][1] = 0
    refused = False
    try:
        _ = central_escape(wrong_words, 10, 5, BoundaryLabel(2, 2, 0, 0, 0))
    except:
        refused = True
    assert_true(refused)
    var wrong_field = tables.copy()
    wrong_field.field.chi1 += 1
    refused = False
    try:
        _ = central_escape(wrong_field, 10, 5, BoundaryLabel(2, 2, 0, 0, 0))
    except:
        refused = True
    assert_true(refused)
    var wrong_prefix = tables.copy()
    wrong_prefix.prefix_positions[0] = CubicElt(1, 0, 0)
    refused = False
    try:
        _ = central_escape(wrong_prefix, 10, 5, BoundaryLabel(2, 2, 0, 0, 0))
    except:
        refused = True
    assert_true(refused)

    assert_equal(members, 27)
    assert_equal(central_paths, 945)
    assert_equal(cycle_paths, 156)
    print("CLASS_A_MINUS_CONSTANT_ENTRY_PASS", "members=", members,
          "central_paths=", central_paths, "cycle_paths=", cycle_paths,
          "checked_edges=", checked_edges, "max_path=", maximum)
    require_contract("minus-Class-A d>=5,n>=d+1 exact central nearest RUN selector and three-RUN constant-height descent; original ordinal and full Parikh replay, first integral-zero typed endpoint, checked pair/path bounds; word/field/prefix-cache mismatch, noncentral, altered-edge, cap and overflow refusals; finite fixtures do not supply the written all-strict-source density or recurrence proof")
