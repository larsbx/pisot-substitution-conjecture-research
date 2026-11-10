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


def power_word(sigma, word, depth):
    for _ in range(depth):
        word = inflate(sigma, word)
    return word


def physical_hub_events(sigma, pair, weights):
    from itertools import product

    top, bottom = pair
    endpoints = [[power_word(sigma, word[:i], 2) for i in range(len(word) + 1)]
                 for word in pair]
    assert tuple(len(power_word(sigma, a, 2)) for a in "012") == weights
    for left, right in product(*endpoints):
        difference = tuple(a - b for a, b in zip(p(left), p(right)))
        assert min(difference) >= 0 or max(difference) <= 0

    a, b = (list(map(len, prefixes)) for prefixes in endpoints)
    events = [(i, j) for i, x in enumerate(top) for j, y in enumerate(bottom)
              if x != "1" and y == "1"
              and max(a[i], b[j]) < min(a[i + 1], b[j + 1])
              and top[:i].count("1") == bottom[:j].count("1")]
    top_completions = [a[i + 1] for i, x in enumerate(top) if x == "1"]
    bottom_completions = [b[j + 1] for j, y in enumerate(bottom) if y == "1"]
    end = next(t for t in bottom_completions
               if sum(x <= t for x in top_completions) < bottom_completions.index(t) + 1)
    j = b.index(end) - 1
    i = next(i for i in range(len(top)) if a[i] < b[j] < a[i + 1])
    defect = tuple(x - y for x, y in zip(p(top[:i]), p(bottom[:j])))
    assert (top[i], bottom[j], defect) == ("2", "1", (-1, 0, 0))
    return events, (i, j)


def check_physical_diagonal(sigma, pair, sources, digits, cut, mass, common):
    for word, source, path in zip(pair, sources, digits):
        cells = [(word[source], ())]
        for _ in range(len(path)):
            cells = [(b, address + (i,)) for a, address in cells
                     for i, b in enumerate(sigma[int(a)])]
        local = cells.index((common, path))
        assert len(power_word(sigma, word[:source], len(path))) + local == cut
        inflated = power_word(sigma, word, len(path))
        assert p(inflated[:cut]) == mass and inflated[cut] == common


def test_separated_symbolic_crossing_and_genuine_physical_crossings():
    from test_c4_two_generation_rank_oracle import matrix

    pair = ("01", "10")
    for _ in range(4):
        pair = children(pair)[0]
    pair = pair[::-1]
    assert pair == ("12202202201", "02220220112")
    legal = power_word(SIGMA, "2", 6)
    assert tuple(legal.index(word) for word in pair) == (32, 153)
    top, bottom = pair
    assert hub_profile(pair, "1") == (7, 9)
    assert (top[9], bottom[9]) == ("0", "1")
    assert tuple(a - b for a, b in zip(p(top[:9]), p(bottom[:9]))) == (-1, 0, 1)
    gap = tuple(a - b for a, b in zip(p(top[:9]), p(bottom[:10])))
    assert gap == (-1, -1, 1)
    assert matvec(matrix(SIGMA), gap) == (0, -1, 1)
    assert matvec(matrix(SIGMA), matvec(matrix(SIGMA), gap)) == (0, 0, 1)
    assert children(pair)[-1] == ("02", "20")
    assert physical_hub_events(SIGMA, pair, (2, 4, 7)) == ([(8, 9)], (8, 9))
    check_physical_diagonal(SIGMA, pair, (8, 9), ((1, 0, 0), (1, 0, 1)),
                            104, (32, 14, 58), "2")

    sigma = ("01", "12", "021")
    pair = ("1201", "0112")
    assert physical_hub_events(sigma, pair, (4, 5, 7)) == ([(1, 2), (2, 2)], (1, 2))
    check_physical_diagonal(sigma, pair, (1, 2), ((2, 1, 2), (1, 0, 1)),
                            27, (7, 11, 9), "1")
