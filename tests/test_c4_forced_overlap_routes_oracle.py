"""Independent exact occurrence closure for the C4 forced-overlap controls."""

from collections import deque
from functools import cache
from itertools import product

import pytest

from test_c4_two_generation_rank_oracle import matrix, matvec, p

ROOT = (2, 1, (-1, 0, 0))


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def subtract(a, b):
    return tuple(x - y for x, y in zip(a, b))


def coincidence(state):
    return state[0] == state[1] and state[2] == (0, 0, 0)


def good_alignment(state):
    return set(state[:2]) == {0, 2} and state[2] == (0, 0, 0)


def closure(sigma, cap=128):
    """Enumerate every actual digit choice, with integer endpoint signs."""
    m = matrix(sigma)
    letters = [p(str(i)) for i in range(3)]

    @cache
    def sign(defect):
        if not any(defect):
            return 0
        for _ in range(32):
            if min(defect) >= 0:
                return 1
            if max(defect) <= 0:
                return -1
            defect = matvec(m, defect)
        raise ValueError("endpoint sign budget exhausted")

    def interior(x, y, defect):
        return sign(add(defect, letters[x])) > 0 and sign(subtract(letters[y], defect)) > 0

    assert interior(*ROOT)
    pending = deque([ROOT])
    graph = {}
    while pending:
        state = pending.popleft()
        if state in graph:
            continue
        if len(graph) >= cap:
            raise ValueError("overlap vertex budget exhausted")
        row = graph[state] = []
        if coincidence(state):
            continue
        x, y, defect = state
        transformed = matvec(m, defect)
        for i, j in product(range(len(sigma[x])), range(len(sigma[y]))):
            child = (
                int(sigma[x][i]), int(sigma[y][j]),
                add(transformed, subtract(p(sigma[x][:i]), p(sigma[y][:j]))),
            )
            if interior(*child):
                row.append(((i, j), child))
                pending.append(child)
    return graph


def shortest(graph, start, target, allowed=lambda state: True):
    pending = deque([(start, ())])
    seen = set()
    while pending:
        state, path = pending.popleft()
        if state in seen or not allowed(state):
            continue
        seen.add(state)
        if target(state):
            return path
        pending.extend((child, path + (digits,)) for digits, child in graph[state])
    return None


@pytest.mark.parametrize("sigma,counts,first,remaining,direct,good,via", [
    (("1", "02", "220"), (39, 80, 5), ((0, 0), (0, 1), (1, 1)),
     (4, 5, 2), ((1, 1), (0, 0), (0, 1)), 3, 7),
    (("01", "12", "021"), (68, 146, 6), ((1, 0), (2, 0), (2, 1)),
     (4, 3, 2), ((2, 1), (1, 0), (2, 1)), 4, 5),
])
def test_full_forced_overlap_route(sigma, counts, first, remaining, direct, good, via):
    graph = closure(sigma)
    distance = {}
    for state in graph:
        path = shortest(graph, state, coincidence)
        assert path is not None, state
        distance[state] = len(path)
    assert (len(graph), sum(map(len, graph.values())), max(distance.values())) == counts
    assert tuple(digits for digits, _ in graph[ROOT]) == first
    assert tuple(distance[child] for _, child in graph[ROOT]) == remaining
    assert all(child[2][1] < 0 for _, child in graph[ROOT])
    assert shortest(graph, ROOT, coincidence, lambda state: state[2][1] == 0) is None
    assert shortest(graph, ROOT, coincidence) == direct
    assert shortest(graph, ROOT, coincidence, lambda state: not good_alignment(state)) == direct
    assert len(shortest(graph, ROOT, good_alignment)) == good
    assert min(len(shortest(graph, ROOT, lambda state: state == g)) + distance[g]
               for g in graph if good_alignment(g)) == via


def test_forced_overlap_budget_refuses_partial_result():
    with pytest.raises(ValueError, match="vertex budget"):
        closure(("01", "12", "021"), cap=64)
