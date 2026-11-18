"""A reachable productive countercontrol for the two affine defect ranks.

At k=t=0, w=(y,y,0,-4,4) has both target defects zero but no strict
child or two-step strict descendant in the legal one-step-zero target.
Every edge below is replayed with its original literal occurrence indices.
The computation is restricted to these paths and two finite child stars;
it does not build a graph or assert a universal Class-A entry theorem.
"""

from std.testing import assert_true, assert_equal
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import (
    SeedOverlapTables, build_seed_overlap_tables_screened,
    seed_overlap_states, selected_overlap_child, interior_overlap,
)
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, geometric_state,
    member_transport, verify_member_edge,
)
from psc.class_a_zero_return import _delta, zero_return_addresses
from psc.class_a_x_ladder import reversed_label


def _step(tables: SeedOverlapTables, source: BoundaryLabel,
          i: Int, j: Int, target: BoundaryLabel) raises -> BoundaryLabel:
    verify_member_edge(tables, -1, 0, 3, 5, source, i, j, target)
    return target


def _target(w: BoundaryLabel) raises -> Bool:
    # Z is any integral zero offset, without requiring equal tile letters.
    # H consists of nonzero states with a legal one-step zero child.
    var hits = zero_return_addresses(0, 0, w)
    return hits.first_first or hits.positive_count() > 0


def _strict_children(tables: SeedOverlapTables,
                     source: BoundaryLabel) raises -> List[BoundaryEdge]:
    """Complete literal Cartesian star, retaining duplicate occurrences."""
    var geometric_source = geometric_state(tables, source)
    assert_true(interior_overlap(tables, geometric_source))
    var result = List[BoundaryEdge]()
    for i in range(len(tables.sigma[source.top])):
        for j in range(len(tables.sigma[source.bottom])):
            var child = member_transport(-1, 0, 3, 5, source, i, j)
            var actual = selected_overlap_child(tables, geometric_source, i, j)
            assert_true(actual == geometric_state(tables, child))
            if interior_overlap(tables, actual):
                verify_member_edge(tables, -1, 0, 3, 5,
                                   source, i, j, child)
                result.append(BoundaryEdge(i, j, child))
    return result^


def main() raises:
    var tables = build_seed_overlap_tables_screened(
        class_member(CLASS_A, 8, 3, 2))
    var seed = BoundaryLabel(1, 0, 0, 0, 0)
    var seed_found = False
    for actual_seed in seed_overlap_states(tables):
        # S18 retains both orientations of the actual nine swap sources.
        if actual_seed == geometric_state(tables, reversed_label(seed)):
            seed_found = True
    assert_true(seed_found)

    # A concrete S18 source reaches w. No quotient state is substituted.
    var u = _step(tables, seed, 1, 0, BoundaryLabel(2, 0, 0, -1, 0))
    u = _step(tables, u, 3, 9, BoundaryLabel(1, 0, -1, -1, 3))
    u = _step(tables, u, 0, 1, BoundaryLabel(1, 2, 1, 2, -5))
    var w = _step(tables, u, 1, 1, BoundaryLabel(2, 2, 0, -4, 4))

    # w belongs to the recurrent component of X, with both actual paths.
    var x = BoundaryLabel(0, 0, 1, 0, -1)
    u = _step(tables, x, 7, 0, BoundaryLabel(2, 0, 0, -1, 0))
    u = _step(tables, u, 3, 9, BoundaryLabel(1, 0, -1, -1, 3))
    u = _step(tables, u, 0, 1, BoundaryLabel(1, 2, 1, 2, -5))
    u = _step(tables, u, 1, 1, w)
    u = _step(tables, u, 0, 2, BoundaryLabel(0, 2, 1, 0, -3))
    u = _step(tables, u, 0, 3, BoundaryLabel(0, 1, 0, -3, 4))
    u = _step(tables, u, 2, 1, BoundaryLabel(2, 2, 0, 2, -2))
    u = _step(tables, u, 3, 2, BoundaryLabel(1, 2, 0, 0, 1))
    u = _step(tables, u, 4, 0, x)
    assert_true(u == x)

    # Both absolute defects are zero. Their sum and either lexicographic
    # ordering are minimal, but the missing legal-gap condition is real.
    assert_equal(w.x - _delta(w.top, w.bottom), 0)
    assert_equal(w.x + w.c + w.y, 0)
    var hits = zero_return_addresses(0, 0, w)
    assert_equal(hits.gap, -4)
    assert_equal(hits.positive_count(), 0)
    assert_true(not hits.first_first)
    assert_true(not _target(w))

    # Inspect all 16 first-level position pairs and all 90 pairs below
    # the two accepted children. Retain multiplicities at the second level.
    var first = _strict_children(tables, w)
    assert_equal(len(first), 2)
    assert_equal(first[0].i, 0)
    assert_equal(first[0].j, 2)
    assert_true(first[0].target == BoundaryLabel(0, 2, 1, 0, -3))
    assert_equal(first[1].i, 0)
    assert_equal(first[1].j, 3)
    assert_true(first[1].target == BoundaryLabel(0, 1, 1, 0, -2))
    var pairs = len(tables.sigma[w.top]) * len(tables.sigma[w.bottom])
    var second_occurrences = 0
    for edge in first:
        assert_true(not _target(edge.target))
        pairs += (len(tables.sigma[edge.target.top]) *
                  len(tables.sigma[edge.target.bottom]))
        var second = _strict_children(tables, edge.target)
        for child_edge in second:
            assert_true(not _target(child_edge.target))
            second_occurrences += 1
    assert_equal(pairs, 106)
    assert_equal(second_occurrences, 13)

    # The failed rank candidate does not make w a BH obstruction: its first
    # possible H entry is at depth three and zero is reached at depth four.
    u = _step(tables, w, 0, 3, BoundaryLabel(0, 1, 1, 0, -2))
    u = _step(tables, u, 6, 4, BoundaryLabel(2, 0, -1, -1, 2))
    u = _step(tables, u, 0, 7, BoundaryLabel(0, 2, 0, 1, -1))
    assert_true(_target(u))
    assert_true(u.x != 0 or u.c != 0 or u.y != 0)
    u = _step(tables, u, 2, 1, BoundaryLabel(2, 2, 0, 0, 0))
    assert_equal(u.x, 0)
    assert_equal(u.c, 0)
    assert_equal(u.y, 0)

    # The same literal occurrence cannot certify a changed full offset.
    var refused = False
    try:
        verify_member_edge(tables, -1, 0, 3, 5, seed, 1, 0,
                           BoundaryLabel(2, 0, 0, -1, 1))
    except:
        refused = True
    assert_true(refused)

    print("CLASS_A_ENTRY_DEFECT_COUNTERCONTROL_PASS",
          "k=0 t=0", "literal_pairs=", pairs,
          "first_occurrences=", len(first),
          "second_occurrences=", second_occurrences,
          "first_target_depth=3 zero_depth=4")
    require_contract("k=t=0 actual cyclic S18 descendant with both affine defects zero outside H; no H-or-integral-zero entry in one or two steps; productive four-step zero witness; no uniform source-entry claim")
