"""Independent standard-library oracle for a *bounded* literal C4 cut control.

Mojo kernel/psc/c4_cut_alignment.mojo is canonical; these Python tests
independently reconstruct literal words, ordered zero-return children and
source-image digits. No finite test proves the universal C4 theorem.
"""
from collections import Counter
from itertools import accumulate


def infl(sigma, word):
    return "".join(sigma[c] for c in word)


def cuts(top, bottom):
    assert Counter(top) == Counter(bottom)
    return [i for i in range(len(top) + 1) if Counter(top[:i]) == Counter(bottom[:i])]


def children(top, bottom):
    z = cuts(top, bottom)
    return [(top[a:b], bottom[a:b]) for a, b in zip(z, z[1:])]


def addr(sigma, source, cut):
    bounds = [0, *accumulate(map(lambda c: len(sigma[c]), source))]
    i = next(k for k in range(len(source)) if bounds[k] <= cut < bounds[k + 1])
    return i, cut - bounds[i]


def defect(a, b):
    return tuple(a.count(str(i)) - b.count(str(i)) for i in range(3))


def test_tribonacci_recurrent_legal_balanced_cut_has_misaligned_source_flags():
    sigma = {"0": "01", "1": "02", "2": "0"}
    seed = ("01", "10")
    b = ("102", "201")
    p = ("0102", "2010")
    assert children(infl(sigma, seed[0]), infl(sigma, seed[1])) == [("0", "0"), b]
    assert children(infl(sigma, b[0]), infl(sigma, b[1])) == [
        ("0", "0"), (p[1], p[0])
    ]
    top, bottom = infl(sigma, p[0]), infl(sigma, p[1])
    assert (top, bottom) == ("0102010", "0010201")
    assert cuts(top, bottom) == [0, 1, 3, 5, 7]
    assert children(top, bottom) == [
        ("0", "0"), ("10", "01"), ("20", "02"), ("10", "01")
    ]
    t = 3
    assert addr(sigma, p[0], t) == (1, 1)
    assert addr(sigma, p[1], t) == (2, 0)
    assert top[t - 1] != bottom[t - 1] and top[t] != bottom[t]
    i, di = addr(sigma, p[0], t)
    j, dj = addr(sigma, p[1], t)
    assert defect(p[0][:i], p[1][:j]) == (0, 0, -1)
    assert defect(sigma[p[0][i]][:di], sigma[p[1][j]][:dj]) == (1, 0, 0)
    w = "0"
    for _ in range(4):
        w = infl(sigma, w)
    assert all(z in w for z in p)
    # The real recurrent noncoincident source cycle is productive:
    # each source state has an actual (0,0) child.


def test_bilateral_birth_identity_on_bounded_true_irreducibles():
    for sigma in (
        {"0": "01", "1": "02", "2": "0"},
        {"0": "1", "1": "02", "2": "202"},
    ):
        for u, v in [
            ("01", "10"), ("02", "20"), ("12", "21"),
            ("102", "201"), ("0102", "2010"),
        ]:
            if Counter(u) != Counter(v) or cuts(u, v) != [0, len(u)]:
                continue
            a, b = infl(sigma, u), infl(sigma, v)
            for cut in cuts(a, b)[1:-1]:
                iu, du = addr(sigma, u, cut)
                iv, dv = addr(sigma, v, cut)
                assert du > 0 or dv > 0, (sigma, u, v, cut, iu, iv)


def test_strict_nonpisot_has_asynchronous_born_cut():
    sigma = {"0": "1", "1": "012", "2": "1"}
    p = ("01", "10")
    top, bottom = infl(sigma, p[0]), infl(sigma, p[1])
    assert (top, bottom) == ("1012", "0121")
    assert children(top, bottom) == [("10", "01"), ("12", "21")]
    assert addr(sigma, p[0], 2) == (1, 1)
    assert addr(sigma, p[1], 2) == (0, 2)
    assert defect(p[0][:1], p[1][:0]) == (1, 0, 0)
    assert defect("0", "01") == (0, -1, 0)


def test_singular_incidence_breaks_bilateral_birth_rigidity():
    # Essential full-rank hypothesis: sigma(0) = sigma(2).
    sigma = {"0": "1", "1": "012", "2": "1"}
    top, bottom = infl(sigma, "02"), infl(sigma, "20")
    assert (top, bottom) == ("11", "11")
    assert cuts(top, bottom) == [0, 1, 2]
    assert addr(sigma, "02", 1) == (1, 0)
    assert addr(sigma, "20", 1) == (1, 0)


def test_nonunit_image_lattice_digit_filter():
    # M=[[0,1,2],[1,1,1],[0,1,0]], det=2; integrality iff q0-q2 is even.
    sigma = {"0": "1", "1": "021", "2": "001"}
    for a in ("1", "2"):
        first = defect(sigma[a][:1], "")
        second = defect(sigma[a][:2], "")
        assert (first[0] - first[2]) % 2 == 1
        assert (second[0] - second[2]) % 2 == 0

    def lift(q):
        z1 = q[2]
        assert (q[0] - q[2]) % 2 == 0
        z2 = (q[0] - q[2]) // 2
        z0 = q[1] - z1 - z2
        assert (z1 + 2 * z2, z0 + z1 + z2, z1) == q
        return z0, z1, z2

    assert lift(defect(sigma["1"][:2], "")) == (-1, 1, 0)
    assert lift(defect(sigma["2"][:2], "")) == (-1, 0, 1)


def test_fullrank_primitive_nonpip_strict_four_state_realization():
    # Full-rank primitive expanding, but char=(x-1)(x^2-2x-2), not PIP.
    sigma = {"0": "10", "1": "102", "2": "211"}
    states = [
        ("102", "210"),
        ("11102", "21110"),
        ("10210211", "21110210"),
        ("10210210210211", "21110210210210"),
    ]

    def determinant(s):
        (a, b, c), (d, e, f), (g, h, i) = [
            [s[str(j)].count(str(k)) for j in range(3)] for k in range(3)
        ]
        return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)

    assert determinant(sigma) == -2
    M = [[sigma[str(j)].count(str(i)) for j in range(3)] for i in range(3)]

    def product(A, B):
        return [
            [sum(A[i][k] * B[k][j] for k in range(3)) for j in range(3)]
            for i in range(3)
        ]

    assert all(n > 0 for row in product(product(M, M), product(M, M)) for n in row)
    ordered = [children(infl(sigma, u), infl(sigma, v)) for u, v in states]
    labels = {p: k for k, p in enumerate(states)}
    assert all(p in labels for row in ordered for p in row)
    edges = [[labels[p] for p in row] for row in ordered]
    assert edges == [
        [2], [3], [2, 0, 0, 1, 0], [2, 0, 0, 1, 0, 1, 0, 1, 0]
    ]
    for source in range(4):
        reachable = {source}
        while True:
            next_reached = reachable | {dst for i in reachable for dst in edges[i]}
            if next_reached == reachable:
                break
            reachable = next_reached
        assert reachable == set(range(4))
    h = {a: w[0] for a, w in sigma.items()}
    g = {a: w[-1] for a, w in sigma.items()}
    assert h == {"0": "1", "1": "1", "2": "2"}
    assert g == {"0": "0", "1": "2", "2": "1"}
    assert all(
        u[0] == "1" and v[0] == "2" and u[-1] in "12" and v[-1] == "0"
        for u, v in states
    )
    parent = states[2]
    top, bottom = infl(sigma, parent[0]), infl(sigma, parent[1])
    assert cuts(top, bottom) == [0, 8, 11, 14, 19, 22]
    for cut, expected_address, E, correction in (
        (8, (3, 0, 2, 2), (1, 0, 0), (-1, -1, 0)),
        (14, (5, 1, 5, 0), (1, -1, 0), (0, 0, 1)),
    ):
        i, r = addr(sigma, parent[0], cut)
        j, s = addr(sigma, parent[1], cut)
        assert (i, r, j, s) == expected_address
        assert defect(parent[0][:i], parent[1][:j]) == E
        assert defect(sigma[parent[0][i]][:r], sigma[parent[1][j]][:s]) == correction
