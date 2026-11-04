"""Independent word, address, and integer replay of the recurrent exit negative."""
from collections import deque
from itertools import combinations

from test_c4_two_generation_rank_oracle import det, factor, inflate, matvec, p

SIGMA = ("1", "02", "220")
PARENT = ("0222022012", "1220220220")


def children(pair):
    return factor(*(inflate(SIGMA, word) for word in pair))


def normalize(pair):
    return tuple(sorted(pair))


def reachable(root):
    """Complete normalized occurrence graph, with a fail-closed budget."""
    rows = {}
    pending = deque([root])
    while pending:
        state = pending.popleft()
        if state in rows:
            continue
        if len(rows) >= 64 or len(state[0]) > 32:
            raise ValueError("replay budget exhausted")
        rows[state] = [] if state[0] == state[1] else [
            normalize(child) for child in children(state)
        ]
        pending.extend(rows[state])
    return rows


def descendant_digits(word, depth):
    addressed = [(word, ())]
    for _ in range(depth):
        addressed = [
            (letter, address + (digit,))
            for source, address in addressed
            for digit, letter in enumerate(SIGMA[int(source)])
        ]
    return addressed


def test_exact_pisot_and_actual_good_edge():
    columns = [p(word) for word in SIGMA]
    assert columns == [(0, 1, 0), (1, 0, 1), (1, 0, 2)]
    trace = sum(col[j] for j, col in enumerate(columns))
    second = sum(columns[i][i] * columns[j][j] - columns[i][j] * columns[j][i]
                 for i, j in combinations(range(3), 2))
    assert (trace, second, det(*columns)) == (2, -1, -1)
    matrix = list(zip(*columns))
    for column in columns:
        for _ in range(3):
            column = matvec(matrix, column)
        assert min(column) > 0

    def chi(x):
        return x**3 - trace * x**2 + second * x - det(*columns)

    assert (chi(-1), chi(0), chi(1), chi(2), chi(3)) == (-1, 1, -1, -1, 7)
    # The three disjoint sign brackets isolate all roots. ±1 are the
    # only candidates for rational roots of this monic cubic.
    top, bottom = (descendant_digits(letter, 4) for letter in "02")
    assert top[3] == ("2", (0, 1, 0, 1))
    assert bottom[3] == ("2", (0, 0, 1, 0))
    assert p("".join(a for a, _ in top[:3])) == (1, 0, 2)
    assert p("".join(a for a, _ in bottom[:3])) == (1, 0, 2)


def test_complete_recurrent_rows_and_exiting_mass():
    state = ("01", "10")
    for _ in range(5):
        state = normalize(children(state)[0])
    assert state == PARENT
    legal = "".join(a for a, _ in descendant_digits("0", 7))
    assert tuple(legal.index(word) for word in PARENT) == (18, 0)

    row = children(PARENT)
    assert row == [
        PARENT[::-1],
        ("1220220", "2022012"),
        ("102220", "202201"),
    ]
    assert children(PARENT[::-1]) == [pair[::-1] for pair in row]
    assert all(a[0] == "1" and b[0] != "1" for a, b in row)
    assert all(a != b for a, b in row)
    graph = reachable(PARENT)
    assert len(graph) == 18
    assert graph[PARENT] == [PARENT, *(normalize(pair) for pair in row[1:])]
    assert all(PARENT not in reachable(normalize(pair)) for pair in row[1:])

    top, bottom = (inflate(SIGMA, w) for w in PARENT)
    cuts = [i for i in range(len(top) + 1) if p(top[:i]) == p(bottom[:i])]
    assert cuts == [0, 10, 17, 23]
    addresses = [
        [(source, digit) for source, letter in enumerate(word)
         for digit in range(len(SIGMA[int(letter)]))]
        for word in PARENT
    ]
    assert [(addresses[0][i], addresses[1][i]) for i in cuts[1:-1]] == [
        ((4, 0), (4, 1)), ((7, 0), (7, 1)),
    ]
    assert [(top[i - 1] + bottom[i - 1], top[i] + bottom[i])
            for i in cuts[1:-1]] == [("02", "12")] * 2
    # Both endpoint maps are permutations. A distinct pair cannot sync.
    assert sorted(word[0] for word in SIGMA) == list("012")
    assert sorted(word[-1] for word in SIGMA) == list("012")

    parent_mass = p(PARENT[0])
    masses = [p(a) for a, _ in row]
    assert masses == [parent_mass, (2, 1, 4), (2, 1, 3)]
    assert det(*masses) == -1
    exits = tuple(a + b for a, b in zip(*masses[1:]))
    matrix = list(zip(*(p(word) for word in SIGMA)))
    assert exits == (4, 2, 7)
    assert matvec(matrix, parent_mass) == tuple(a + b for a, b in zip(parent_mass, exits))
    assert det(parent_mass, exits, matvec(matrix, exits)) == -1
    assert children(row[2])[1] == ("2", "2")
