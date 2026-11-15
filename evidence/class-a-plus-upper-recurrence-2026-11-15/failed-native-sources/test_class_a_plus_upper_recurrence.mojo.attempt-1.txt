"""Actual upper central sources, nearest phases, cycle exits and refusals."""
from std.testing import assert_equal, assert_true
from std.sys import argv
from mojo_smoke.claims import require_contract
from finite_exact.exact_decimal import bigz_decimal
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import SeedOverlapTables, build_seed_overlap_tables_screened
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge
from psc.class_a_plus_upper_recurrence import (
    CentralEscape, parameters, bind_upper, central_source, is_central, is_cycle,
    nearest_twice, nearest_edge, reserve, central_escape, verify_central_path,
    original_prefixes, transport,
)
from psc.perron_field3 import CubicElt, cubic_scale_checked


def specimen(tables: SeedOverlapTables, n: Int, J: Int,
             source: BoundaryLabel, emit: Bool) raises -> List[Int]:
    var cert = central_escape(tables, n, J, source)
    var prefixes = original_prefixes(n, J, source, cert.path)
    var digits = 1
    if emit:
        var row = String("PLUS_UPPER_CENTRAL_PATH ")+String(n)+" "+String(J)+" "+(
            String(source.x))+" "+String(source.c)+" "+String(source.y)+" "+(
            String(cert.central_depth))+" "+String(len(cert.path))+" "+String(cert.reserve)
        for edge in cert.path:
            row += " "+String(edge.i)+" "+String(edge.j)+" "+String(edge.target.top)+" "+(
                String(edge.target.bottom))+" "+String(edge.target.x)+" "+(
                String(edge.target.c))+" "+String(edge.target.y)
        for prefix in prefixes:
            for value in prefix:
                var rendered = bigz_decimal(value)
                digits = max(digits, rendered.byte_length())
                row += " "+rendered
        print(row)
    else:
        for prefix in prefixes:
            for value in prefix:
                digits = max(digits, bigz_decimal(value).byte_length())
    return [len(cert.path), cert.central_depth, digits]


def main() raises:
    var args = argv()
    var emit = len(args) == 2 and args[1] == "--emit"
    if len(args) > 1 and not emit:
        raise Error("only --emit is supported")
    var paths = 0
    var edges = 0
    var central_edges = 0
    var maximum = 0
    var maximum_central = 0
    var maximum_digits = 0
    for n in [7, 8, 12, 31]:
        for J in [1, 2, 3, 4, 5, n+7]:
            var d = parameters(n, J)
            var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, n+d, n, n+1))
            var sources = List[BoundaryLabel]()
            for p in range(-2, 3):
                for q in range(-2, 3):
                    sources.append(central_source(tables, n, J, p, q))
            sources.append(central_source(tables, n, J, 100, -83))
            sources.append(central_source(tables, n, J, -100, 83))
            for H in range(1, n+7):
                var cycle = BoundaryLabel(2, 2, H, 3*H, -6*H)
                if is_central(tables, cycle):
                    sources.append(cycle)
                    sources.append(BoundaryLabel(2, 2, -H, -3*H, 6*H))
            for source in sources:
                var results = specimen(tables, n, J, source, emit)
                paths += 1
                edges += results[0]
                central_edges += results[1]
                maximum = max(maximum, results[0])
                maximum_central = max(maximum_central, results[1])
                maximum_digits = max(maximum_digits, results[2])

    # Independent calibration pins the complete finite domain and long path.
    assert_equal(paths, 818)
    assert_equal(maximum, 93)
    assert_equal(maximum_central, 62)
    assert_equal(maximum_digits, 144)
    var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, 32, 7, 8))
    var source = central_source(tables, 7, 1, 100, -83)
    var good = central_escape(tables, 7, 1, source)
    assert_true(good.central_depth > 1)
    verify_central_path(tables, 7, 1, source, good)
    _ = original_prefixes(7, 1, source, good.path)
    var zero = BoundaryLabel(2, 2, 0, 0, 0)
    var zero_cert = central_escape(tables, 7, 1, zero)
    assert_equal(len(zero_cert.path), 0)
    var cycle = BoundaryLabel(2, 2, 4, 12, -24)
    var cyclic = central_escape(tables, 7, 1, cycle)
    assert_equal(cyclic.central_depth, 0)
    assert_equal(len(cyclic.path), 7)
    var cycle_edge = nearest_edge(tables, 7, 1, cycle)
    assert_true(cycle_edge.target == BoundaryLabel(2, 2, -4, -12, 24))
    assert_true(is_cycle(cycle_edge.target))
    # A physical central interval cannot bound the independent integer input.
    assert_true(is_central(tables, source))
    assert_true(reserve(7, source) > reserve(7, cycle))
    var reasons: List[String] = [
        "upper recurrence path is incomplete or not typed y/y zero",
        "upper recurrence continued after integral zero",
        "upper recurrence source is not central y/y",
        "upper recurrence source is not central y/y",
        "upper recurrence source reserve mismatch",
        "upper recurrence central phase mismatch",
        "upper recurrence central phase does not end at cycle",
        "upper recurrence selected nearest edge mismatch",
        "upper recurrence selected nearest edge mismatch",
        "upper recurrence selected nearest edge mismatch",
        "upper recurrence step cap: no verdict",
        "upper recurrence step cap: no verdict",
        "upper recurrence half-integer tie: no verdict",
        "upper recurrence nearest search cap: no verdict",
        "upper recurrence requires n>=7 and 1<=J<=n+7",
        "upper recurrence requires n>=7 and 1<=J<=n+7",
        "upper recurrence requires n>=7 and 1<=J<=n+7",
        "checked integer addition overflow",
        "upper recurrence literal word mismatch",
        "upper recurrence field mismatch",
        "upper recurrence original prefix mismatch",
        "upper recurrence prefix layout mismatch",
        "upper recurrence prefix limb cap: no verdict",
        "upper recurrence prefix limb cap: no verdict",
        "upper recurrence central phase continues past cycle",
        "upper recurrence child type or full offset mismatch",
        "nonexistent child ordinal",
        "nonexistent child ordinal"]
    var controls = 0
    for kind in range(len(reasons)):
        var cert = good.copy()
        var altered = tables.copy()
        var supplied = source
        if kind == 0:
            _ = cert.path.pop()
        elif kind == 1:
            cert.path.append(BoundaryEdge(1, 1, zero))
        elif kind == 2:
            supplied.top = 0
        elif kind == 3:
            supplied = BoundaryLabel(2, 2, 0, 0, 1)
        elif kind == 4:
            cert.reserve = 14
        elif kind == 5:
            cert.central_depth = -1
        elif kind == 6:
            cert.central_depth = 0
        elif kind == 7:
            cert.path[0].target.top = 0
        elif kind == 8:
            cert.path[0].target.c += 1
        elif kind == 9:
            cert.path[0].j += 1
        elif kind == 18:
            altered.sigma[0][0] = 2
        elif kind == 19:
            altered.field.chi1 += 1
        elif kind == 20:
            altered.prefix_positions[0] = CubicElt(1, 0, 0)
        elif kind == 21:
            altered.prefix_starts[0] = 1
        var reason = String("")
        try:
            if kind == 10:
                _ = central_escape(tables, 7, 1, source, -1)
            elif kind == 11:
                _ = central_escape(tables, 7, 1, source, len(good.path)-1)
            elif kind == 12:
                _ = nearest_twice(tables, tables.lengths.l2, -7, 7)
            elif kind == 13:
                _ = nearest_twice(tables, cubic_scale_checked(tables.lengths.l2, 100), -7, 7)
            elif kind == 14:
                bind_upper(tables, 6, 1)
            elif kind == 15:
                bind_upper(tables, 7, 0)
            elif kind == 16:
                bind_upper(tables, 7, 15)
            elif kind == 17:
                _ = parameters(Int.MAX, 1)
            elif kind == 22:
                _ = original_prefixes(7, 1, source, good.path, 0)
            elif kind == 23:
                _ = original_prefixes(7, 1, source, good.path, 1)
            elif kind == 24:
                var late = cyclic.copy()
                late.central_depth = 1
                verify_central_path(tables, 7, 1, cycle, late)
            elif kind == 25:
                var retired_first = transport(7, 4, BoundaryLabel(2,2,1,3,-6), 1, 4)
                var retired_second = transport(7, 4, retired_first, 1, 9)
                assert_true(retired_second.top == 2 and retired_second.bottom == 1)
                var bad = List[BoundaryEdge]()
                bad.append(BoundaryEdge(1, 4, retired_first))
                bad.append(BoundaryEdge(1, 9, BoundaryLabel(2, 2,
                    retired_second.x, retired_second.c, retired_second.y)))
                _ = original_prefixes(7, 4, BoundaryLabel(2,2,1,3,-6), bad)
            elif kind == 26:
                _ = transport(7, 1, source, -1, 1)
            elif kind == 27:
                _ = transport(7, 1, source, 1, 10)
            else:
                verify_central_path(altered, 7, 1, supplied, cert)
        except error:
            reason = String(error)
        assert_equal(reason, reasons[kind])
        controls += 1
    assert_equal(controls, 28)
    print("PLUS_UPPER_CENTRAL_TOTAL paths="+String(paths)+" edges="+String(edges)+
          " central_edges="+String(central_edges)+" max_depth="+String(maximum)+
          " max_central="+String(maximum_central)+" max_prefix_digits="+String(maximum_digits)+
          " controls="+String(controls))
    require_contract("class_a_plus_upper_central_to_zero_paths")
