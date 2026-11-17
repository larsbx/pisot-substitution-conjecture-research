"""Controls for the phasewise displacement support bound."""

from std.testing import assert_equal, assert_false, assert_true
from mojo_smoke.claims import require_contract
from psc.overlap_phase_displacement import (
    measure_displacement_support,
    overlap_phase_displacements,
)
from psc.overlap_seed_patch import (
    OverlapState,
    SeedOverlapAutomaton,
    build_overlap_graph_from_seeds,
    build_seed_overlap_tables,
    first_coincidence_depths,
)
from psc.perron_field3 import CubicElt, TileLengths3


def test_lattice_controls() raises:
    # Abstract integral supports. Neither graph phase claims literal geometry.
    var e0 = CubicElt(1, 0, 0)
    var e1 = CubicElt(0, 1, 0)
    var e2 = CubicElt(0, 0, 1)
    var lengths = TileLengths3(e0, e1, e2)
    var aligned: List[CubicElt] = [CubicElt(), e0, -e0, e1, -e1, e2, -e2]
    var unaligned: List[CubicElt] = [
        CubicElt(-1, 0, 0), CubicElt(-1, 1, 0), e1,
        CubicElt(1, 1, 0), e0, CubicElt(1, -1, 0),
        CubicElt(1, 0, 1), CubicElt(1, 0, -1),
    ]
    var weights = [6, 1, 1, 1, 1, 3, 1, 1]
    var weighted_sum = CubicElt()
    for i in range(len(unaligned)):
        weighted_sum = weighted_sum + unaligned[i].scale(weights[i])
    assert_true(weighted_sum.is_zero())

    var states = List[OverlapState]()
    for shift in aligned:
        states.append(OverlapState(0, 1, shift))
    # Two labels with the same aligned offset contribute only one offset.
    states.append(OverlapState(1, 0, CubicElt()))
    var split = len(states)
    for shift in unaligned:
        states.append(OverlapState(0, 1, shift))
    var adj = List[List[Int]]()
    var component = List[Int]()
    for source in range(len(states)):
        component.append(source)
        var row = List[Int]()
        for target in range(len(states)):
            if (source < split) != (target < split):
                row.append(target)
        adj.append(row^)
    var graph = SeedOverlapAutomaton(states, adj, False)
    var phases = overlap_phase_displacements(graph, lengths, component)
    assert_equal(len(phases), 2)
    assert_equal(phases[0].distinct_offsets, 7)
    assert_true(phases[0].aligned)
    assert_equal(phases[1].distinct_offsets, 8)
    assert_false(phases[1].aligned)
    for phase in phases:
        assert_equal(phase.widths, [2, 2, 2])
        assert_true(phase.meets_necessary_support())

    # Seven connected offsets with both signs in each coordinate, but
    # all satisfy x <= y. No strictly positive centred average exists.
    var imbalance: List[CubicElt] = [
        CubicElt(-1, -1, 0), -e0, CubicElt(-1, 1, 0), e1,
        CubicElt(1, 1, 0), CubicElt(1, 1, 1), CubicElt(1, 1, -1),
    ]
    var phase = measure_displacement_support(imbalance, lengths)
    assert_equal(phase.distinct_offsets, 7)
    assert_equal(phase.widths, [2, 2, 2])
    assert_false(phase.aligned)
    assert_false(phase.meets_necessary_support())


def test_productive_periodic_overlap() raises:
    var tables = build_seed_overlap_tables([[0, 0, 0, 1, 2, 2], [0, 1], [0]])
    var seed = OverlapState(0, 0, tables.lengths.at(1))
    var signs = Dict[CubicElt, Int]()
    var graph = build_overlap_graph_from_seeds(tables, [seed], signs)
    assert_false(graph.capped)
    assert_true(0 in graph.adj[0])
    var phases = overlap_phase_displacements(graph, tables.lengths, [0])
    assert_equal(len(phases), 1)
    assert_equal(phases[0].distinct_offsets, 1)
    assert_equal(phases[0].widths, [0, 0, 0])
    assert_false(phases[0].aligned)
    assert_false(phases[0].meets_necessary_support())
    var depth = first_coincidence_depths(graph)[0]
    assert_equal(depth, 2)

    var capped = build_overlap_graph_from_seeds(tables, [seed], signs, 1)
    assert_true(capped.capped)
    var refused = False
    try:
        _ = overlap_phase_displacements(capped, tables.lengths, [0])
    except e:
        refused = "complete graph" in String(e)
    assert_true(refused)


def main() raises:
    test_lattice_controls()
    print("Abstract phases: aligned size 7, unaligned size 8, uncentred size 7 refused.")
    test_productive_periodic_overlap()
    print("AAABCC/AB/A: one-offset recurrent subgraph with a depth-two literal exit.")
    require_contract("Phase displacement supports count distinct offsets, check lattice unit steps, and refuse capped graphs. An actual open one-offset cycle remains productive.")
