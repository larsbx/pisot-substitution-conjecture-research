"""Actual lower-chamber entry, homogeneous density and terminal policies."""

from std.testing import assert_true, assert_equal
from std.sys import argv
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge
from psc.class_a_minus_constant_entry import verify_member_edge
from psc.class_a_minus_entry_search import entry_escape, coincidence_escape, verify_one_level_density
from psc.class_a_x_productivity import nine_sources
from psc.class_a_x_ladder import reversed_label
from psc.overlap_seed_patch import SeedOverlapTables, build_seed_overlap_tables_screened


def _verify(tables: SeedOverlapTables, n: Int, d: Int, source: BoundaryLabel,
            path: List[BoundaryEdge], emit: Bool, typed: Bool = False) raises:
    var w = source
    var tag = "MINUS_TYPED_ENTRY_PATH" if typed else "MINUS_ENTRY_PATH"
    var row = tag + " " + String(n) + " " + String(d) + " " + (
        String(w.top)) + " " + String(w.bottom) + " " + String(w.x) + " " + (
        String(w.c)) + " " + String(w.y) + " " + String(len(path))
    for edge in path:
        assert_true(w.x != 0 or w.c != 0 or w.y != 0 or (typed and w.top != w.bottom))
        verify_member_edge(tables, n, d, w, edge.i, edge.j, edge.target)
        w = edge.target
        if emit:
            row += " " + String(edge.i) + " " + String(edge.j) + " " + (
                String(w.top)) + " " + String(w.bottom) + " " + String(w.x) + " " + (
                String(w.c)) + " " + String(w.y)
    assert_equal(w.x, 0)
    assert_equal(w.c, 0)
    assert_equal(w.y, 0)
    if typed:
        assert_equal(w.top, w.bottom)
    if emit:
        print(row)


def main() raises:
    var args = argv()
    var emit = len(args) == 2 and args[1] == "--emit"
    if len(args) > 1 and not emit:
        raise Error("only --emit is supported")
    var paths = 0
    var checked_edges = 0
    var maximum = 0
    var typed_paths = 0
    var typed_edges = 0
    var typed_maximum = 0
    for d in [5, 7, 11]:
        for n in [d+1, 2*d-1, 2*d, 4*d-1, 4*d, 5*d-1, 5*d, 12*d, 24*d]:
            var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, n+d, n, n-1))
            verify_one_level_density(tables, n, d)
            var sources = List[BoundaryLabel]()
            for seed in nine_sources():
                sources.append(seed)
                sources.append(reversed_label(seed))
            sources.append(BoundaryLabel(0, 0, -1, -5, 6))
            sources.append(BoundaryLabel(2, 2, 1, -1, 0))
            sources.append(BoundaryLabel(2, 2, -1, 1, 0))
            for source in sources:
                var path = entry_escape(tables, n, d, source)
                _verify(tables, n, d, source, path, emit)
                paths += 1
                checked_edges += len(path)
                maximum = max(maximum, len(path))
            for a in range(3):
                for b in range(3):
                    if a == b:
                        continue
                    var source = BoundaryLabel(a, b, 0, 0, 0)
                    var path = coincidence_escape(tables, n, d, source)
                    assert_true(len(path) > 0)
                    _verify(tables, n, d, source, path, emit, True)
                    typed_paths += 1
                    typed_edges += len(path)
                    typed_maximum = max(typed_maximum, len(path))

    var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, 11, 6, 5))
    var source = BoundaryLabel(0, 0, -1, -5, 6)
    var baseline = entry_escape(tables, 6, 5, source)
    assert_true(len(baseline) > 0)
    _verify(tables, 6, 5, source, baseline, False)
    var refused = 0
    for mode in range(3):
        var caught = False
        try:
            _ = entry_escape(tables, 6, 5, source,
                1 if mode == 0 else 10000,
                1 if mode == 1 else 20000000,
                0 if mode == 2 else 10000)
        except:
            caught = True
        assert_true(caught)
        refused += 1
    for mode in range(5):
        var caught = False
        try:
            if mode == 0:
                _ = entry_escape(tables, 6, 5, BoundaryLabel(2, 2, 0, 0, 2))
            elif mode == 1:
                _ = entry_escape(tables, 7, 5, source)
            elif mode == 2:
                _ = entry_escape(tables, Int.MAX, 5, source)
            elif mode == 3:
                verify_one_level_density(tables, 6, 6)
            else:
                verify_one_level_density(tables, 6, 4)
        except:
            caught = True
        assert_true(caught)
        refused += 1
    assert_equal(paths, 567)
    assert_equal(typed_paths, 162)
    assert_equal(refused, 8)
    print("CLASS_A_MINUS_ENTRY_SEARCH_PASS", "members=27", "paths=" + String(paths),
          "checked_edges=" + String(checked_edges), "max_path=" + String(maximum),
          "density_inequalities=270", "refusals=" + String(refused))
    print("CLASS_A_MINUS_TYPED_ENTRY_PASS", "members=27", "paths=" + String(typed_paths),
          "checked_edges=" + String(typed_edges), "max_path=" + String(typed_maximum))
    require_contract("ClassAMinusActualConstantEntry; d>=5,n>=d+1; original full-offset paths; caps refuse")
    require_contract("ClassAMinusTypedCoincidenceEntry; mixed-letter integral zero is nonterminal")
