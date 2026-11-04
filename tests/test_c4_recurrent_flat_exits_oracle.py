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


def collared_interval(sigma, seed, depth, radius, positions, diagonals):
    """Replay inherited cuts directly from the two physical prefixes."""
    top, bottom = seed
    for _ in range(depth):
        top, bottom = inflate(sigma, top), inflate(sigma, bottom)
    left, right = positions[0]
    masses = []
    for expected_positions, expected_diagonals in zip(positions, diagonals, strict=True):
        assert (left, right) == expected_positions
        assert radius <= left < right <= len(top) - radius
        assert p(top[:left]) == p(bottom[:left])
        assert p(top[:right]) == p(bottom[:right])
        for word in (top, bottom):
            assert word[left - radius:left + radius] == word[right - radius:right + radius]
        row = factor(top[left:right], bottom[left:right])
        assert [i for i, (a, b) in enumerate(row) if a == b] == expected_diagonals
        masses.append(p(top[left:right]))
        left, right = (len(inflate(sigma, top[:cut])) for cut in (left, right))
        top, bottom = inflate(sigma, top), inflate(sigma, bottom)
    return masses


def test_equal_cut_contexts_do_not_force_a_parikh_potential():
    top, bottom = (inflate(SIGMA, word) for word in PARENT)
    assert (top[9:11], bottom[9:11]) == (top[16:18], bottom[16:18]) == ("01", "22")
    assert top[8:12] != top[15:19]
    masses = collared_interval(
        SIGMA, PARENT, 1, 1, [(10, 17), (23, 39), (52, 88)], [[], [], [5, 7]],
    )
    assert masses == [(2, 1, 4), (5, 2, 9), (11, 5, 20)]
    assert det(*masses) == 1


def test_collared_interval_reducible_and_productive_controls():
    masses = collared_interval(
        ("10", "102", "211"), ("102", "210"), 2, 2,
        [(11, 19), (30, 52), (82, 142)], [[], [], []],
    )
    assert masses == [(2, 4, 2), (6, 10, 6), (16, 28, 16)]
    assert det(*masses) == 0
    assert masses[0][0] * masses[1][1] != masses[0][1] * masses[1][0]
    assert all(a == c for a, _, c in masses)

    sigma = ("01", "12", "021")
    top, bottom = (inflate(sigma, inflate(sigma, word)) for word in ("10", "01"))
    assert [i for i in range(1, len(top)) if p(top[:i]) == p(bottom[:i])] == [7]


def hub_profile(pair, hub):
    u, v = pair if pair[0][0] == hub else pair[::-1]
    assert u[0] == hub and v[0] != hub
    prefix = [u[:i].count(hub) - v[:i].count(hub) for i in range(len(u) + 1)]
    assert prefix[1] == 1 and prefix[-1] == 0
    area = sum(prefix)
    pair_counts = [
        sum(word[i] == hub and word[j] != hub for i, j in combinations(range(len(word)), 2))
        for word in (u, v)
    ]
    assert area == pair_counts[0] - pair_counts[1]
    crossing = next((i for i in range(len(u)) if prefix[i + 1] < 0), -1)
    return area, crossing


def test_hub_prefix_crossing_controls_and_actual_offset_cancellation():
    from test_c4_complete_cone_hub_audit_oracle import SIGMA as REDUCIBLE, STATES
    from test_c4_two_generation_rank_oracle import matrix

    assert REDUCIBLE[0][0] == REDUCIBLE[1][0] == "1"
    assert [hub_profile(pair, "2") for pair in STATES] == [(2, -1), (4, -1), (2, -1), (2, -1)]
    assert [hub_profile(pair, "1") for pair in [PARENT, *children(PARENT)]] == [
        (8, -1), (8, -1), (5, -1), (5, -1),
    ]

    sigma = ("01", "12", "021")
    seed = ("10", "01")
    (pair,) = factor(*(inflate(sigma, word) for word in seed))
    row = factor(*(inflate(sigma, word) for word in pair))
    assert [hub_profile(z, "1") for z in (seed, pair, *row)] == [
        (1, -1), (0, 2), (-3, 2), (1, -1),
    ]
    top, bottom = pair
    assert (top[2], bottom[2]) == ("0", "1")
    defect = tuple(a - b for a, b in zip(p(top[:2]), p(bottom[:2])))
    assert defect == (-1, 0, 1)

    def inflate_addressed(letter):
        cells = [(letter, ())]
        for _ in range(3):
            cells = [(b, path + (i,)) for a, path in cells for i, b in enumerate(sigma[int(a)])]
        return cells

    a, b = (inflate_addressed(word[2]) for word in pair)
    assert (a[0], b[7]) == (("0", (0, 0, 0)), ("0", (1, 1, 0)))
    for _ in range(3):
        defect = matvec(matrix(sigma), defect)
    assert defect == p("".join(letter for letter, _ in b[:7])) == (2, 3, 2)

    prefixes = [word[:2] for word in pair]
    for _ in range(3):
        top, bottom = (inflate(sigma, word) for word in (top, bottom))
        prefixes = [inflate(sigma, word) for word in prefixes]
    assert (len(prefixes[0]), len(prefixes[1]) + 7) == (28, 28)
    assert p(top[:28]) == p(bottom[:28]) == (7, 12, 9)
    assert factor(top[28:29], bottom[28:29]) == [("0", "0")]
