"""Witness-only rank theorem with no hidden forward-closure assumption."""
import pytest

from reference.psc_research.selected_rank import (
    BadRankWitness,
    replay_selected,
    verify_selected_rank,
)


def test_exact_selected_rank_graph_and_local_witness():
    adj = [[1, 0], [2], []]
    terminals = [False, False, True]
    ranks = [2, 1, 0]
    selected = [0, 0, -1]
    assert verify_selected_rank(adj, terminals, ranks, selected) == 2
    assert replay_selected(adj, terminals, ranks, selected, 0) == [1, 2]
    assert replay_selected(adj, terminals, ranks, selected, 1) == [2]


def test_reject_selected_cycle_and_forged_child_and_false_terminal():
    bad = [
        ([[0], []], [False, True], [1, 0], [0, -1]),
        ([[2], []], [False, True], [1, 0], [0, -1]),
        ([[1], []], [False, True], [1, 0], [-1, -1]),
        ([[1], []], [False, True], [0, 0], [0, -1]),
        ([[1], []], [False, True], [2, 0], [0, -1]),
        ([[1], []], [False, True], [1, 0], [0, 0]),
        ([[1], []], [False, False], [1, 0], [0, -1]),
        ([[1], []], [False, True], [1, 0], [2, -1]),
        ([[1], []], [False, True], [1, -1], [0, -1]),
    ]
    for args in bad:
        with pytest.raises(BadRankWitness):
            verify_selected_rank(*args)


def test_rank_witness_on_incomplete_universe_has_only_local_scope():
    # Vertex 0 genuinely reaches terminal 1. A separate, as-yet-unlisted
    # overlap 2 could be nonproductive: the two-vertex rank witness has no
    # logical authority about vertex 2 or closure completeness.
    assert verify_selected_rank([[1], []], [False, True], [1, 0], [0, -1]) == 1
    with pytest.raises(BadRankWitness):
        replay_selected([[1], []], [False, True], [1, 0], [0, -1], 2)


def test_malformed_shapes_and_python_bool_as_rank_are_refused():
    with pytest.raises(BadRankWitness):
        verify_selected_rank([], [], [], [])
    with pytest.raises(BadRankWitness):
        verify_selected_rank([[0]], [False], [True], [0])
    with pytest.raises(BadRankWitness):
        verify_selected_rank([[0]], [False], [1], [0, 1])
