"""Ordered differential check against the former exhaustive occurrence loop."""
from std.testing import assert_equal, assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from psc.overlap_seed_patch import (
    OverlapState, SeedOverlapTables, build_seed_overlap_tables_screened,
    build_seed_overlap_graph_from_tables, interior_overlap_cached,
    overlap_children_cached, selected_overlap_child,
)
from psc.perron_field3 import CubicElt
from symbolic_line_certificate import ClassLine
from a1_normal_form_census import CLASS_D


def exhaustive(tables: SeedOverlapTables, state: OverlapState) raises -> List[OverlapState]:
    var cache = Dict[CubicElt, Int]()
    var out = List[OverlapState]()
    for i in range(len(tables.sigma[state.top])):
        for j in range(len(tables.sigma[state.bottom])):
            var child = selected_overlap_child(tables, state, i, j)
            if interior_overlap_cached(tables, cache, child):
                out.append(child)
    return out^


def compare(tables: SeedOverlapTables, state: OverlapState) raises:
    var cache = Dict[CubicElt, Int]()
    var actual = overlap_children_cached(tables, cache, state)
    var expected = exhaustive(tables, state)
    assert_equal(len(actual), len(expected))
    for i in range(len(actual)):
        assert_equal(actual[i], expected[i])


def main() raises:
    var checked = 0
    # Plus/minus and both long-run boundaries. Every reachable typed offset,
    # including coincidence states, is compared as an ordered list.
    for coef in [[3,4,3,3,2,1], [3,6,3,7,2,5], [4,69,4,68,3,53], [4,74,4,73,3,57]]:
        var tables = build_seed_overlap_tables_screened(ClassLine(CLASS_D,List[Int](coef),True).member(0))
        var graph = build_seed_overlap_graph_from_tables(tables, 200000)
        assert_true(not graph.capped)
        for i in range(graph.size()):
            compare(tables, graph.states[i])
            checked += 1
        # Coincident parent partitions have equal child endpoints. Strict
        # tangencies must not become children; multiplicity is retained.
        for a in range(3):
            compare(tables, OverlapState(a,a,CubicElt()))
            var rejected = False
            var cache = Dict[CubicElt, Int]()
            try:
                _ = overlap_children_cached(tables,cache,OverlapState(a,a,tables.lengths.at(a)))
            except:
                rejected = True
            assert_true(rejected)
    print("ORDERED_CHILD_SWEEP_AGREEMENT", checked)
    require_contract("exact child interval sweep equals exhaustive ordered occurrence enumeration, including duplicates and equal endpoints, on plus/minus class-D and both previously unresolved boundary specimens; non-overlap parents refuse")
