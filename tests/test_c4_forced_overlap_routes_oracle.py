"""Independent exact occurrence closure for the C4 forced-overlap controls."""

from collections import deque
from functools import cache
from itertools import product

import pytest

from test_c4_addressed_newborn_oracle import resolve

from test_c4_two_generation_rank_oracle import factor, inflate, matrix, matvec, p

ROOT = (2, 1, (-1, 0, 0))


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def subtract(a, b):
    return tuple(x - y for x, y in zip(a, b))


def coincidence(state):
    return state[0] == state[1] and state[2] == (0, 0, 0)


def good_alignment(state):
    return set(state[:2]) == {0, 2} and state[2] == (0, 0, 0)


def closure(sigma, cap=128, *, root=ROOT):
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

    assert interior(*root)
    pending = deque([root])
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


def test_literal_first_crossing_can_reach_only_the_right_alignment_of_its_good_edge():
    sigma = ("1", "02", "002")
    assert sigma[1][0] == sigma[2][0] == "0"

    pair = ("01", "10")
    for expected in (("102", "021"), ("0210", "1002")):
        pair = factor(*(inflate(sigma, w) for w in pair))[0]
        assert pair == expected
    top, bottom = pair
    legal = "2"
    for _ in range(4):
        legal = inflate(sigma, legal)
    assert (legal.index(top), legal.index(bottom)) == (2, 0)
    row = factor(*(inflate(sigma, w) for w in pair))
    assert row == [("1002021", "0211002")]
    assert factor(*(inflate(sigma, w) for w in row[0]))[1:] == [("0", "0"), ("2", "2")]

    # The second bottom hub starts after the first top hub but before
    # the second top hub, strictly inside top letter 2.
    top_source, bottom_source = 1, 2
    defect = subtract(p(top[:top_source]), p(bottom[:bottom_source]))
    assert defect == (0, -1, 0)
    assert p(top[:top_source])[0] == p(bottom[:bottom_source])[0] == 1
    assert matvec(matrix(sigma), add(defect, p("2"))) == (1, 0, 0)
    top_hubs = [p(top[:i]) for i, a in enumerate(top) if a == "0"]
    bottom_hubs = [p(bottom[:i]) for i, a in enumerate(bottom) if a == "0"]
    differences = [subtract(b, a) for a, b in zip(top_hubs, bottom_hubs, strict=True)]
    assert differences == [(0, 1, 0), (0, 0, -1)]
    assert matvec(matrix(sigma), add(*differences)) == (-1, 0, 0)

    root = (int(top[top_source]), int(bottom[bottom_source]), defect)
    assert root == (2, 0, (0, -1, 0))
    graph = closure(sigma, root=root)
    assert (len(graph), sum(map(len, graph.values()))) == (54, 94)
    aligned = {state[:2] for state in graph if not any(state[2])}
    assert aligned == {(0, 0), (2, 2), (0, 1), (1, 0), (0, 2), (2, 0)}
    assert graph[root] == [((2, 0), (2, 1, (1, 0, -1)))]

    def right_good(state):
        x, y, defect = state
        return {x, y} == {1, 2} and add(defect, subtract(p(str(x)), p(str(y)))) == (0, 0, 0)

    right_path = shortest(graph, root, right_good)
    assert right_path == ((2, 0), (2, 1), (2, 0), (2, 0), (2, 1), (0, 2), (0, 2))
    right_state = root
    for digits in right_path:
        right_state = dict(graph[right_state])[digits]
    assert right_state == (1, 2, (0, -1, 1))
    assert dict(graph[right_state])[(0, 1)] == (0, 0, (0, 0, 0))
    assert dict(graph[right_state])[(1, 2)] == (2, 2, (0, 0, 0))

    path = shortest(graph, root, coincidence)
    assert path == ((2, 0), (2, 1), (2, 0), (1, 0), (0, 0), (1, 0), (2, 1), (1, 0))
    addresses = tuple((source, *(digits[i] for digits in path))
                      for i, source in enumerate((top_source, bottom_source)))
    assert resolve(sigma, pair, addresses) == (
        (0, 0, 1, 0, 0, 0, 1, 1), ("100202021", "020211002"), 5, True,
    )
