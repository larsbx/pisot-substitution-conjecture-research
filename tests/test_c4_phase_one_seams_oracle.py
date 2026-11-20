"""Independent seam enumeration, exact integer lift, and literal witnesses."""

from fractions import Fraction
from itertools import product

from test_c4_strict_period_oracle import expand, graph, periods, row


def mass(word):
    return tuple(word.count(a) for a in "012")


def legal_bigrams(sigma):
    first = {a: w[0] for a, w in zip("012", sigma, strict=True)}
    last = {a: w[-1] for a, w in zip("012", sigma, strict=True)}
    legal = {w[i:i + 2] for w in sigma for i in range(len(w) - 1)}
    while True:
        next_legal = legal | {last[a] + first[b] for a, b in legal}
        if next_legal == legal:
            return legal
        legal = next_legal


def endpoint_pairs(mapping, hub, side, phase):
    result = set()
    for leaf in set("012") - {hub}:
        pair = hub + leaf if side == 0 else leaf + hub
        visited = set()
        a, b = pair
        track = side
        while a != b and (a, b, track) not in visited:
            if (hub not in (a, b) if phase is None else (a, b)[track] != hub):
                break
            visited.add((a, b, track))
            a, b = mapping[int(a)], mapping[int(b)]
            track ^= phase == 1
        if (a, b, track) in visited:
            result.add(pair)
    return result


def integral_lift(columns, shift):
    rows = [[Fraction(column[i]) for column in (*columns, shift)] for i in range(3)]
    for col in range(3):
        pivot = next(j for j in range(col, 3) if rows[j][col])
        rows[col], rows[pivot] = rows[pivot], rows[col]
        scale = rows[col][col]
        rows[col] = [x / scale for x in rows[col]]
        for j in range(3):
            if j != col:
                a = rows[j][col]
                rows[j] = [x - a * y for x, y in zip(rows[j], rows[col], strict=True)]
    return all(r[-1].denominator == 1 for r in rows)


def local_seams(sigma, left, right, side, phase):
    first = endpoint_pairs(tuple(w[0] for w in sigma), left, 0, phase)
    last = endpoint_pairs(tuple(w[-1] for w in sigma), right, side, phase)
    legal = legal_bigrams(sigma)
    columns = [mass(w) for w in sigma]
    if phase == 1:
        parent_first, parent_last = ({ab[::-1] for ab in group} for group in (first, last))
    elif phase is None:
        parent_first, parent_last = (group | {ab[::-1] for ab in group} for group in (first, last))
    else:
        parent_first, parent_last = first, last

    def addresses(before, after):
        for parent, image in zip("012", sigma, strict=True):
            for pos, letter in enumerate(image):
                if letter != after:
                    continue
                preceding = {image[pos - 1]} if pos else {
                    sigma[int(a)][-1] for a in "012" if a + parent in legal
                }
                if before in preceding:
                    yield parent, pos, mass(image[:pos]), mass(image[pos:])

    for l, r in product(last, first):
        if any(a + b not in legal for a, b in zip(l, r, strict=True)):
            continue
        for top, bottom in product(addresses(l[0], r[0]), addresses(l[1], r[1])):
            a, i, p, s = top
            b, j, q, t = bottom
            if i == j == 0 or (p == q and a + b not in parent_first):
                continue
            if s == t and a + b not in parent_last:
                continue
            if integral_lift(columns, tuple(x - y for x, y in zip(p, q, strict=True))):
                yield l, r, a, i, b, j


def check_witness(sigma, root, depth, cut, counts, letter):
    for a in root:
        w = expand(sigma, a, depth)
        assert mass(w[:cut]) == counts and w[cut] == letter


def test_unbounded_family_controls_with_both_witnesses_and_no_phase_premise():
    for r in range(2, 13):
        for k in range(r, r + 7):
            sigma = ("1", "0" + "1" * k + "2", "0" * r + "1")
            check_witness(sigma, "12", 1, 0, (0, 0, 0), "0")
            reversed_sigma = tuple(w[::-1] for w in sigma)
            if k == r:
                check_witness(reversed_sigma, "01", 4, k * k + 4 * k + 2,
                              (2 * k, k * k + k + 1, k + 1), "1")
            else:
                check_witness(reversed_sigma, "01", 3, k + 2 * r + 4,
                              (r + 1, k + r + 1, 2), "1")
            assert legal_bigrams(sigma) == {"00", "01", "10", "11", "12", "20", "21"}
            for side, phase in product((0, 1), (None, 1)):
                assert not list(local_seams(sigma, "0", "2", side, phase))

    exceptional = ("1", "012", "001")
    check_witness(exceptional, "12", 1, 0, (0, 0, 0), "0")
    check_witness(tuple(w[::-1] for w in exceptional), "01", 5, 20, (7, 9, 4), "0")
    for side, phase in product((0, 1), (None, 1)):
        assert not list(local_seams(exceptional, "0", "2", side, phase))


def test_strict_reducible_control_retains_each_literal_newborn():
    sigma = ("1", "012", "101")
    states = (("01", "10"), ("12", "21"), ("1012", "2101"))
    check_witness(sigma, "02", 1, 0, (0, 0, 0), "1")
    check_witness(tuple(w[::-1] for w in sigma), "02", 1, 0, (0, 0, 0), "1")
    assert periods(graph(sigma, states, True)) == [2]
    possible = {(a, b) for a, b, *_ in local_seams(sigma, "1", "1", 1, 1)}
    assert possible == {("01", "10"), ("01", "12"), ("21", "10"), ("21", "12")}
    observed = []
    for u, v in states:
        factors = [factor for _, _, factor in row(sigma, (u, v))]
        for (a, b), (c, d) in zip(factors, factors[1:]):
            l, r = a[-1] + b[-1], c[0] + d[0]
            if r[0] != "1":
                l, r = l[::-1], r[::-1]
            assert r[0] == l[1] == "1" and (l, r) in possible
            observed.append((l, r))
    assert len(observed) == 4


def test_productive_pisot_control_can_pass_local_phase_one_filter():
    sigma = ("1", "012", "21")
    check_witness(sigma, "12", 2, 4, (1, 2, 1), "2")
    check_witness(tuple(w[::-1] for w in sigma), "01", 3, 5, (1, 2, 2), "1")
    assert not list(local_seams(sigma, "0", "2", 0, 1))
    assert list(local_seams(sigma, "0", "2", 1, 1)) == [("12", "01", "1", 0, "2", 1)]
    assert (13, 14, ("2", "2")) in row(sigma, ("01", "10"), 3)
