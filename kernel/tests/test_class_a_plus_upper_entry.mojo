"""Replay original-index upper entry across all ordered pairs and control faces."""
from std.testing import assert_equal, assert_true
from std.sys import argv
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, interior_overlap
from psc.class_a_boundary_children import BoundaryLabel, geometric_state
from psc.class_a_plus_upper_entry import central_entry
from psc.class_a_plus_upper_recurrence import (
    central_source, is_central, original_prefixes, parameters,
)


def main() raises:
    var args = argv()
    var emit = len(args) == 2 and args[1] == "--emit"
    if len(args) > 1 and not emit:
        raise Error("only --emit is supported")
    var paths = 0
    var edges = 0
    for n in [7, 8, 12, 31]:
        for J in [1, 2, 3, 4, 5, n+7]:
            var d = parameters(n, J)
            var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, n+d, n, n+1))
            var control = BoundaryLabel(2, 1, 0, 1, 0)
            var control_path = central_entry(tables, n, J, control)
            assert_equal(len(control_path), 2)
            assert_equal(control_path[0].i, n+2)
            assert_equal(control_path[0].j, 0)
            assert_true(control_path[0].target == BoundaryLabel(1, 1, 0, 1, -1))
            assert_equal(control_path[1].i, 1)
            assert_equal(control_path[1].j, 2)
            assert_true(control_path[1].target == BoundaryLabel(2, 2, 0, 0, 0))
            _ = original_prefixes(n, J, control, control_path)
            var capped = False
            try:
                _ = central_entry(tables, n, J, control, 1)
            except:
                capped = True
            assert_true(capped)
            for p in range(-3, 4):
                for q in range(-3, 4):
                    var center = central_source(tables, n, J, p, q).y
                    for r in range(center-4, center+5):
                        for a in range(3):
                            for b in range(3):
                                var source = BoundaryLabel(a, b, p, q, r)
                                if not interior_overlap(tables, geometric_state(tables, source)):
                                    continue
                                var path = central_entry(tables, n, J, source)
                                var target = source
                                for edge in path:
                                    target = edge.target
                                assert_true(is_central(tables, target))
                                if emit:
                                    var row = String("PLUS_UPPER_ENTRY ")+String(n)+" "+String(J)+" "+(
                                        String(a))+" "+String(b)+" "+String(p)+" "+String(q)+" "+(
                                        String(r))+" "+String(len(path))
                                    for edge in path:
                                        row += " "+String(edge.i)+" "+String(edge.j)+" "+(
                                            String(edge.target.top))+" "+String(edge.target.bottom)+" "+(
                                            String(edge.target.x))+" "+String(edge.target.c)+" "+String(edge.target.y)
                                    print(row)
                                paths += 1
                                edges += len(path)
    assert_true(paths > 10000)
    print("calibrated", paths, "strict sources and", edges, "entry edges")
    require_contract("Upper plus-Class-A original strict entry into the central y/y domain")
