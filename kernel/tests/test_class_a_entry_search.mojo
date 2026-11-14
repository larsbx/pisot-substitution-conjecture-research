"""Actual full-source entry paths, finite block densities and cap refusal."""

from std.testing import assert_true, assert_equal
from std.sys import argv
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, verify_member_edge
from psc.class_a_entry_search import entry_escape, coincidence_escape, verify_two_level_density
from psc.class_a_x_productivity import nine_sources
from psc.class_a_x_ladder import reversed_label
from psc.overlap_seed_patch import SeedOverlapTables, build_seed_overlap_tables_screened


def _verify(tables: SeedOverlapTables, k: Int, t: Int, source: BoundaryLabel,
            path: List[BoundaryEdge], emit: Bool, typed: Bool = False) raises:
    var w = source
    var kind = "TYPED_ENTRY_PATH" if typed else "ENTRY_PATH"
    var row = kind + " " + String(k) + " " + String(t) + " " + (
        String(source.top)) + " " + String(source.bottom) + " " + (
        String(source.x)) + " " + String(source.c) + " " + (
        String(source.y)) + " " + String(len(path))
    for edge in path:
        assert_true(w.x != 0 or w.c != 0 or w.y != 0 or (typed and w.top != w.bottom))
        verify_member_edge(tables, -1, k, k+t+3, k+2*t+5,
                           w, edge.i, edge.j, edge.target)
        w = edge.target
        if emit:
            row += " " + String(edge.i) + " " + String(edge.j) + " " + (
                String(w.top)) + " " + String(w.bottom) + " " + (
                String(w.x)) + " " + String(w.c) + " " + String(w.y)
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
    var members: List[List[Int]] = [
        [0, 3], [1, 2], [2, 1], [3, 0], [0, 4],
        [0, 20], [0, 64], [32, 0], [8, 8],
    ]
    var paths = 0
    var checked_edges = 0
    var maximum = 0
    var typed_paths = 0
    var typed_edges = 0
    var typed_maximum = 0
    for member in members:
        var k = member[0]
        var t = member[1]
        var n = k+t+3
        var d = k+2*t+5
        var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, n+d, n, n-1))
        verify_two_level_density(tables, k, t)
        var sources = List[BoundaryLabel]()
        for seed in nine_sources():
            sources.append(seed)
            sources.append(reversed_label(seed))
        # A formal strict source, not an asserted member of any seed graph.
        sources.append(BoundaryLabel(0, 0, -1, -5, 6))
        if k == 0 and t == 20:
            # This defeats the proposed all-strict three-step L1 decrease.
            sources.append(BoundaryLabel(2, 2, 10, -738, 738))
        for source in sources:
            var path = entry_escape(tables, k, t, source)
            _verify(tables, k, t, source, path, emit)
            paths += 1
            checked_edges += len(path)
            maximum = max(maximum, len(path))
        for a in range(3):
            for b in range(3):
                if a == b:
                    continue
                var source = BoundaryLabel(a, b, 0, 0, 0)
                var path = coincidence_escape(tables, k, t, source)
                assert_true(len(path) > 0)
                _verify(tables, k, t, source, path, emit, True)
                typed_paths += 1
                typed_edges += len(path)
                typed_maximum = max(typed_maximum, len(path))

    var tables = build_seed_overlap_tables_screened(class_member(CLASS_A, 17, 6, 5))
    var source = BoundaryLabel(0, 0, -1, -5, 6)
    var baseline = entry_escape(tables, 0, 3, source)
    assert_true(len(baseline) > 0)
    _verify(tables, 0, 3, source, baseline, False)
    var refused = 0
    for mode in range(3):
        var caught = False
        try:
            _ = entry_escape(tables, 0, 3, source,
                1 if mode == 0 else 10000,
                1 if mode == 1 else 20000000,
                0 if mode == 2 else 10000)
        except:
            caught = True
        assert_true(caught)
        refused += 1
    var caught = False
    try:
        _ = entry_escape(tables, 0, 3, BoundaryLabel(2, 2, 0, 0, 2))
    except:
        caught = True
    assert_true(caught)
    refused += 1
    caught = False
    try:
        _ = entry_escape(tables, 0, 4, source)
    except:
        caught = True
    assert_true(caught)
    refused += 1
    caught = False
    try:
        _ = entry_escape(tables, Int.MAX, 0, source)
    except:
        caught = True
    assert_true(caught)
    refused += 1
    var short_tables = build_seed_overlap_tables_screened(class_member(CLASS_A, 8, 3, 2))
    caught = False
    try:
        verify_two_level_density(short_tables, 0, 0)
    except:
        caught = True
    assert_true(caught)
    refused += 1
    assert_equal(paths, 172)
    assert_equal(refused, 7)
    assert_equal(typed_paths, 54)
    print("CLASS_A_ENTRY_SEARCH_PASS", "members=9", "paths=" + String(paths),
          "checked_edges=" + String(checked_edges), "max_path=" + String(maximum),
          "density_inequalities=81", "refusals=" + String(refused))
    print("CLASS_A_TYPED_ENTRY_PASS", "members=9", "paths=" + String(typed_paths),
          "checked_edges=" + String(typed_edges), "max_path=" + String(typed_maximum))
    require_contract("ClassAActualCentralEntryAndFullIntegralZeroWitnesses; n>=6; bounded search refuses caps")
    require_contract("ClassAActualTypedCoincidenceEntry; mixed-letter integral zero is nonterminal")
