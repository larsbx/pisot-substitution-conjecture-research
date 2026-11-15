"""Canonical complete eight-case paths, original prefixes and typed refusals."""
from std.testing import assert_equal, assert_true
from std.sys import argv
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import build_seed_overlap_tables_screened
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge
from psc.class_a_plus_upper_cycles import (
    _bind, cycle_source, cycle_escape, member_transport, verify_member_edge,
    verify_cycle_path, original_prefixes,
)
from psc.perron_field3 import CubicElt


def main() raises:
    var args = argv()
    var emit = len(args) == 2 and args[1] == "--emit"
    if len(args) > 1 and not emit:
        raise Error("only --emit is supported")
    var paths = 0
    var edges = 0
    var maximum = 0
    var cases: List[List[Int]] = [[1,1,3],[1,2,3],[1,3,5],[1,4,7],
                                  [2,1,3],[2,2,5],[3,1,2],[4,1,2]]
    for n in [7,8,9,10,11,12,16,31,64,127]:
        for specimen in cases:
            var J = specimen[0]
            var H = specimen[1]
            var d = 2*n+12-J
            var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, n+d, n, n+1))
            for flip in [False, True]:
                var source = cycle_source(J, H, flip)
                var path = cycle_escape(tables, n, J, H, flip)
                assert_equal(len(path), specimen[2])
                verify_cycle_path(tables, n, J, H, flip, source, path)
                var prefixes = original_prefixes(n, J, source, path)
                if emit:
                    var row = String("PLUS_UPPER_PATH ")+String(n)+" "+String(J)+" "+(
                        String(H))+" "+String(Int(flip))+" "+String(source.top)+" "+(
                        String(source.bottom))+" "+String(source.x)+" "+String(source.c)+" "+(
                        String(source.y))+" "+String(len(path))
                    for edge in path:
                        row += " "+String(edge.i)+" "+String(edge.j)+" "+String(edge.target.top)+" "+(
                            String(edge.target.bottom))+" "+String(edge.target.x)+" "+(
                            String(edge.target.c))+" "+String(edge.target.y)
                    for prefix in prefixes:
                        for value in prefix:
                            row += " "+String(value)
                    print(row)
                paths += 1
                edges += len(path)
                maximum = max(maximum, len(path))

    var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, 32, 7, 8))
    var source = cycle_source(1, 4)
    var good = cycle_escape(tables, 7, 1, 4)
    verify_cycle_path(tables, 7, 1, 4, False, source, good)
    var prefix = original_prefixes(7, 1, source, good)
    var expected_top: List[Int] = [180615,150730,1671513]
    var expected_bottom: List[Int] = [1054779,880278,9761413]
    assert_true(prefix[0] == expected_top)
    assert_true(prefix[1] == expected_bottom)
    var nonstrict = BoundaryLabel(2, 2, 0, 0, 2)
    var nonstrict_child = member_transport(7, 1, nonstrict, 0, 0)
    var retired_first = member_transport(7, 1, source, 1, 4)
    var retired_second = member_transport(7, 1, retired_first, 1, 9)
    assert_true(retired_second == BoundaryLabel(2, 1, 3, 11, -20))
    verify_member_edge(tables, 7, 1, retired_first, 1, 9, retired_second)
    # The n=4096 path is valid in every small offset and original address.
    # Its accumulated prefix witnesses exceed the native machine range.
    var large_path = good.copy()
    large_path[5].j = 8201
    var large_source = source
    for edge in large_path:
        assert_true(member_transport(4096, 1, large_source, edge.i, edge.j) == edge.target)
        large_source = edge.target

    var reasons: List[String] = [
        "upper cycle path is incomplete or not typed y/y zero",
        "upper cycle continued after integral zero", "upper cycle source mismatch",
        "upper cycle child type or complete offset mismatch",
        "upper cycle child type or complete offset mismatch", "nonexistent child ordinal",
        "nonexistent child ordinal", "upper cycle child type or complete offset mismatch",
        "upper cycle child type or complete offset mismatch",
        "upper cycle step cap exhausted: no verdict", "upper cycle step cap exhausted: no verdict",
        "outside the eight upper-cycle cases", "outside the eight upper-cycle cases",
        "upper cycles require n>=7 and J in 1..4", "upper cycles require n>=7 and J in 1..4",
        "checked integer multiplication overflow", "upper cycle literal word mismatch",
        "upper cycle field mismatch", "upper cycle original prefix mismatch",
        "upper cycle prefix starts mismatch", "upper cycle parent is not strict",
        "upper cycle child type or complete offset mismatch",
        "checked integer multiplication overflow"]
    var controls = 0
    for kind in range(len(reasons)):
        var bad = good.copy()
        var altered = tables.copy()
        var supplied = source
        if kind == 0:
            _ = bad.pop()
        elif kind == 1:
            bad.append(BoundaryEdge(1, 1, BoundaryLabel(2, 2, 0, 0, 0)))
        elif kind == 2:
            supplied = BoundaryLabel(2, 2, -4, -12, 24)
        elif kind == 3:
            bad[0].target.top = 2
        elif kind == 4:
            bad[0].target.c += 1
        elif kind == 5:
            bad[0].i = -1
        elif kind == 6:
            bad[0].j = 10
        elif kind == 7:
            bad[0].j = 1
        elif kind == 8:
            bad[0].target = BoundaryLabel(0, 2, 0, 0, 0)
        elif kind == 16:
            altered.sigma[0][0] = 2
        elif kind == 17:
            altered.field.chi1 += 1
        elif kind == 18:
            altered.prefix_positions[0] = CubicElt(1, 0, 0)
        elif kind == 19:
            altered.prefix_starts[0] = 1
        var reason = String("")
        try:
            if kind == 9:
                _ = cycle_escape(tables, 7, 1, 4, False, -1)
            elif kind == 10:
                _ = cycle_escape(tables, 7, 1, 4, False, 6)
            elif kind == 11:
                _ = cycle_escape(tables, 7, 1, 0)
            elif kind == 12:
                _ = cycle_escape(tables, 7, 1, 5)
            elif kind == 13:
                _bind(tables, 7, 0)
            elif kind == 14:
                _bind(tables, 6, 1)
            elif kind == 15:
                _bind(tables, Int.MAX, 1)
            elif kind >= 16 and kind <= 19:
                verify_member_edge(altered, 7, 1, BoundaryLabel(2, 2, 0, 0, 0),
                                   0, 0, BoundaryLabel(0, 0, 0, 0, 0))
            elif kind == 20:
                verify_member_edge(tables, 7, 1, nonstrict, 0, 0, nonstrict_child)
            elif kind == 21:
                verify_member_edge(tables, 7, 1, retired_first, 1, 9,
                                   BoundaryLabel(2, 2, 3, 11, -20))
            elif kind == 22:
                _ = original_prefixes(4096, 1, source, large_path)
            else:
                verify_cycle_path(tables, 7, 1, 4, False, supplied, bad, 8)
        except error:
            reason = String(error)
        assert_equal(reason, reasons[kind])
        controls += 1
    assert_equal(paths, 160)
    assert_equal(edges, 600)
    assert_equal(maximum, 7)
    assert_equal(controls, 23)
    print("PLUS_UPPER_TOTAL paths=160 edges=600 max_depth=7 controls=23")
    require_contract("class_a_plus_upper_eight_literal_paths")
