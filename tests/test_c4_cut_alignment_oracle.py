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


def test_two_sided_local_residue_and_endpoint_sieve_with_real_escape():
    # This necessary finite calculation is independent of the Mojo driver.
    # Its nonzero result is *not* a strict SCC certificate.
    from itertools import product

    def det(A):
        (a, b, c), (d, e, f), (g, h, i) = A
        return a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

    def sync(f, a, b):
        for _ in range(4):
            if a == b:
                return True
            a, b = f[a], f[b]
        return a == b

    def count(s):
        M = [[word.count(str(i)) for word in s] for i in range(3)]
        determinant = det(M)
        assert determinant != 0

        def integral_lift(q):
            return all(
                det([[q[row] if col == i else M[row][col]
                      for col in range(3)] for row in range(3)]) % determinant == 0
                for i in range(3)
            )

        first = [int(w[0]) for w in s]
        last = [int(w[-1]) for w in s]
        found = []
        for a, b in product(range(3), repeat=2):
            for r, t in product(range(len(s[a])), range(len(s[b]))):
                if r == t == 0:
                    continue
                q = tuple(s[a][:r].count(str(k)) - s[b][:t].count(str(k))
                          for k in range(3))
                if not integral_lift(q) or sync(first, int(s[a][r]), int(s[b][t])):
                    continue
                lefta = [int(s[a][r-1])] if r else last
                leftb = [int(s[b][t-1])] if t else last
                if any(not sync(last, x, y) for x, y in product(lefta, leftb)):
                    found.append((a, r, b, t))
        return found

    assert count(["01", "02", "0"]) == []
    assert count(["1", "02", "202"]) == []
    assert count(["1", "021", "001"]) == []
    assert count(["11", "210", "10"]) == [(1,0,1,1),(1,1,1,0)]
    assert len(count(["10", "102", "211"])) == 8

    # A literal occurrence of the first PIP candidate is reachable directly
    # from swap (01,10), but its child SCC is productive.
    sigma={"0":"11","1":"210","2":"10"}
    parent=("11210","21011")
    assert children(infl(sigma,"01"),infl(sigma,"10")) == [parent]
    top,bottom=infl(sigma,parent[0]),infl(sigma,parent[1])
    assert (top,bottom)==("2102101021011","1021011210210")
    assert cuts(top,bottom)==[0,3,13]
    assert (addr(sigma,parent[0],3),addr(sigma,parent[1],3)) == ((1,0),(1,1))
    assert defect(parent[0][:1],parent[1][:1]) == (0,1,-1)
    assert defect(sigma["1"][:0],sigma["1"][:1]) == (0,0,-1)
    h={a:sigma[a][0] for a in sigma}
    g={a:sigma[a][-1] for a in sigma}
    assert not sync([int(h[str(i)]) for i in range(3)],int(top[3]),int(bottom[3]))
    assert not sync([int(g[str(i)]) for i in range(3)],int(top[2]),int(bottom[2]))


def test_all_twelve_strict_nonpip_literal_newborn_events():
    # Independent literal enumerator: source addresses and adjacent letter
    # pairs are read from the original expanded words, not a signed quotient.
    sigma = {"0": "10", "1": "102", "2": "211"}
    states = [
        ("102", "210"),
        ("11102", "21110"),
        ("10210211", "21110210"),
        ("10210210210211", "21110210210210"),
    ]
    h = {a: w[0] for a, w in sigma.items()}
    g = {a: w[-1] for a, w in sigma.items()}

    def sync(f, a, b):
        for _ in range(4):
            if a == b:
                return True
            a, b = f[a], f[b]
        return a == b

    events = []
    labels = {pair: i for i, pair in enumerate(states)}
    for parent_id, (u, v) in enumerate(states):
        top, bottom = infl(sigma, u), infl(sigma, v)
        zeroes = cuts(top, bottom)
        raw = children(top, bottom)
        assert all(child in labels for child in raw)
        for ordinal, t in enumerate(zeroes[1:-1], start=1):
            i, di = addr(sigma, u, t)
            j, dj = addr(sigma, v, t)
            E = defect(u[:i], v[:j])
            c = defect(sigma[u[i]][:di], sigma[v[j]][:dj])
            M = [[sigma[str(k)].count(str(row)) for k in range(3)]
                 for row in range(3)]
            assert all(sum(M[k][l] * E[l] for l in range(3)) + c[k] == 0
                       for k in range(3))
            left, right = (top[t-1], bottom[t-1]), (top[t], bottom[t])
            assert not sync(g, *left) and not sync(h, *right)
            assert di > 0 or dj > 0
            events.append((parent_id, ordinal, t, labels[raw[ordinal-1]],
                           labels[raw[ordinal]], (i, di), (j, dj), E, c,
                           left, right))
    assert len(events) == 12
    assert [sum(e[0] == i for e in events) for i in range(4)] == [0, 0, 4, 8]
    assert events[0] == (2, 1, 8, 2, 0, (3, 0), (2, 2), (1, 0, 0),
                         (-1, -1, 0), ("1", "0"), ("1", "2"))
    assert events[2][:9] == (2, 3, 14, 0, 1, (5, 1), (5, 0),
                             (1, -1, 0), (0, 0, 1))
    assert events[-1][:7] == (3, 8, 35, 1, 0, (13, 0), (12, 2))


def test_fullrank_nonpip_strict_has_constant_whole_hub_words():
    """Independent literal-word gauge calculation, not a PSC theorem."""
    sigma = {"0": "10", "1": "102", "2": "211"}
    states = [
        ("102", "210"),
        ("11102", "21110"),
        ("10210211", "21110210"),
        ("10210210210211", "21110210210210"),
    ]
    h = {a: w[0] for a, w in sigma.items()}
    assert h == {"0": "1", "1": "1", "2": "2"}
    idx = {state: i for i, state in enumerate(states)}
    images = []
    signs = []
    for top, bottom in states:
        raw = children(infl(sigma, top), infl(sigma, bottom))
        images.append([idx[z] if z in idx else idx[(z[1], z[0])] for z in raw])
        signs.append([1 if z in idx else -1 for z in raw])
    assert images == [[2], [3], [2, 0, 0, 1, 0], [2, 0, 0, 1, 0, 1, 0, 1, 0]]
    assert all(all(sign == 1 for sign in row) for row in signs)
    # Complete Parikh intertwining is exact despite the rank-two
    # obstruction: row_0(P)=row_2(P). PIP irreducibility would force
    # rank three, so this is a precise excluded-template mechanism.
    P = [[u.count(str(a)) for u, _ in states] for a in range(3)]
    M = [[sig.count(str(a)) for sig in sigma.values()] for a in range(3)]
    N = [[sum(dst == row for dst in images[col]) for col in range(4)]
         for row in range(4)]
    assert P == [[1, 1, 2, 4], [1, 3, 4, 6], [1, 1, 2, 4]]
    assert N == [[0, 0, 3, 5], [0, 0, 1, 3],
                 [1, 0, 1, 1], [0, 1, 0, 0]]
    assert P[0] == P[2]
    assert P[0][0] * P[1][1] - P[0][1] * P[1][0] == 2
    for a in range(3):
        for col in range(4):
            assert sum(P[a][j] * N[j][col] for j in range(4)) == (
                sum(M[a][j] * P[j][col] for j in range(3))
            )
    masks = []
    for pair in ((0, 1), (0, 2), (1, 2)):
        # A compatible good pair must not be the first pair of any
        # strict state (nor occur along the deterministic endpoint orbit).
        good = set(str(c) for c in pair)
        candidate = all(set((u[0], v[0])) != good for u, v in states)
        if candidate:
            masks.append(pair)
    assert masks == [(0, 1), (0, 2)]
    for hub in "12":
        xs = [0 if u[0] == hub else 1 for u, v in states]
        assert xs == ([0] * 4 if hub == "1" else [1] * 4)
        word_bits = [
            [int(sign == -1) ^ xs[src] ^ xs[dst]
             for dst, sign in zip(images[src], signs[src])]
            for src in range(len(states))
        ]
        assert word_bits == [[0], [0], [0, 0, 0, 0, 0], [0] * 9]
    # The prefix-fixed pair (1,2) remains bad forever; left pairs
    # (2,0)/(1,0) also do not synchronize under suffix map.
    suffix = {a: w[-1] for a, w in sigma.items()}
    for u, v in states:
        x, y = u[0], v[0]
        for _ in range(4):
            assert x != y
            x, y = h[x], h[y]
        x, y = u[-1], v[-1]
        for _ in range(4):
            assert x != y
            x, y = suffix[x], suffix[y]
