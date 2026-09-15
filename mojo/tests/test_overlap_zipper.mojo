"""Exact regressions for ordered overlap child occurrences."""

from std.testing import assert_equal, assert_true
from psc.overlap_obstruction import common_child_start_count
from psc.overlap_seed_patch import (
    build_seed_overlap_graph_from_tables,
    build_seed_overlap_tables,
    overlap_children,
)
from psc.overlap_zipper import (
    is_strict_zipper,
    ordered_child_occurrences,
    zero_shift_occurrence_count,
    zipper_steps,
)


def determinant_two_sigma() -> List[List[Int]]:
    var a0: List[Int] = [1]
    var a1: List[Int] = [0, 2, 1]
    var a2: List[Int] = [0, 0, 1]
    var sigma = List[List[Int]]()
    sigma.append(a0^)
    sigma.append(a1^)
    sigma.append(a2^)
    return sigma^


def test_ordered_occurrences_preserve_all_child_occurrences() raises:
    var tables = build_seed_overlap_tables(determinant_two_sigma())
    var graph = build_seed_overlap_graph_from_tables(tables, 20000)
    assert_true(not graph.capped)
    var saw_strict = False
    var saw_boundary_tie = False

    for i in range(graph.size()):
        if graph.states[i].is_coincidence():
            continue
        var occurrences = ordered_child_occurrences(tables, graph.states[i])
        var children = overlap_children(tables, graph.states[i])
        assert_equal(len(occurrences), len(children))

        var steps = zipper_steps(occurrences)
        assert_equal(len(steps), len(occurrences) - 1)
        var diagonal = 0
        for j in range(len(steps)):
            assert_true(steps[j] == 1 or steps[j] == 2 or steps[j] == 3)
            if steps[j] == 3:
                diagonal += 1

        var zero_count = zero_shift_occurrence_count(occurrences)
        assert_equal(zero_count, common_child_start_count(tables, graph.states[i]))
        var first_zero = 1 if occurrences[0].state.shift.is_zero() else 0
        assert_equal(zero_count, first_zero + diagonal)
        assert_equal(is_strict_zipper(occurrences), zero_count == 0)
        if zero_count == 0:
            saw_strict = True
        else:
            saw_boundary_tie = True

    assert_true(saw_strict)
    assert_true(saw_boundary_tie)


def main() raises:
    test_ordered_occurrences_preserve_all_child_occurrences()
    print("[PASS] test_ordered_occurrences_preserve_all_child_occurrences")
    print("1 ordered-overlap-zipper Mojo test passed.")
