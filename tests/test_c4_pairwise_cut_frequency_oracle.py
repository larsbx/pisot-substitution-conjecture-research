"""Independent bounded, exact combinatorial oracle for each strict cut-pair frequency.

No measured Rauzy areas or general PSC conclusion.
"""
from collections import Counter
from fractions import Fraction


SIGMA = ("012", "120", "201")
STATES = (("012", "120"), ("120", "201"), ("201", "012"))


def inflate(word):
    return "".join(SIGMA[int(c)] for c in word)


def irreducible_factors(top, bottom):
    if len(top) != len(bottom) or Counter(top) != Counter(bottom):
        raise ValueError("not a balanced word pair")
    a, b = Counter(), Counter()
    factors, start = [], 0
    for t, (x, y) in enumerate(zip(top, bottom), 1):
        a[x] += 1
        b[y] += 1
        if a == b:
            factors.append((top[start:t], bottom[start:t]))
            start = t
            a.clear()
            b.clear()
    if start != len(top):
        raise AssertionError("unmatched final cut")
    return tuple(factors)


def exact_child_matrix(states):
    index = {state: i for i, state in enumerate(states)}
    N = [[0 for _ in states] for _ in states]
    for j, (u, v) in enumerate(states):
        for child in irreducible_factors(inflate(u), inflate(v)):
            if child[0] == child[1]:
                raise ValueError("strictness violated by a diagonal")
            if child not in index:
                raise ValueError("incomplete closure: escaped literal child")
            N[index[child]][j] += 1
    return N


def mv(N, counts):
    return [sum(row[j] * counts[j] for j in range(len(counts))) for row in N]


def pf_pair_frequency(N, beta, v, L, types):
    """delta_e = h * max_k sum_{i in I_e and C_k} v_i / D, computed from N.

    Verifies the supplied Perron data exactly (N v = beta v, L^T N = beta L^T),
    derives the period h and cyclic classes from the support of N by BFS, and
    checks that every class carries PF mass D/h.  Returns {type: delta}.
    """
    n = len(N)
    edges = [(i, j) for j in range(n) for i in range(n) if N[i][j]]  # child i of j
    if [sum(N[i][j] * v[j] for j in range(n)) for i in range(n)] != [beta * x for x in v]:
        raise ValueError("v is not a right Perron vector")
    if [sum(L[i] * N[i][j] for i in range(n)) for j in range(n)] != [beta * x for x in L]:
        raise ValueError("L is not a left Perron vector")
    dist = {0: 0}
    frontier = [0]
    while frontier:
        nxt = []
        for j in frontier:
            for i in range(n):
                if N[i][j] and i not in dist:
                    dist[i] = dist[j] + 1
                    nxt.append(i)
        frontier = nxt
    if len(dist) != n:
        raise ValueError("N is not irreducible from state 0")
    from math import gcd
    h = 0
    for i, j in edges:
        h = gcd(h, dist[j] + 1 - dist[i])
    h = abs(h)
    classes = [[i for i in range(n) if dist[i] % h == k] for k in range(h)]
    D = sum(Fraction(L[i]) * v[i] for i in range(n))
    for cls in classes:
        if sum(Fraction(L[i]) * v[i] for i in cls) * h != D:
            raise ValueError("unequal cyclic-class PF mass")
    out = {}
    for e in set(types):
        best = max(sum(Fraction(v[i]) for i in cls if types[i] == e) for cls in classes)
        out[e] = h * best / D
    return h, out


def test_complete_strict_rotation_and_each_first_pair_frequency():
    N = exact_child_matrix(STATES)
    assert N == [[1, 1, 1]] * 3
    pairs = {frozenset((a[0], b[0])) for a, b in STATES}
    assert pairs == {frozenset("01"), frozenset("02"), frozenset("12")}
    lengths = [len(u) for u, _ in STATES]
    assert lengths == [3] * 3
    assert [sum(lengths[i] * N[i][j] for i in range(3))
            for j in range(3)] == [9] * 3
    for root in range(3):
        u, v = STATES[root]
        counts = [int(i == root) for i in range(3)]
        for level in range(1, 7):
            u, v = inflate(u), inflate(v)
            factors = irreducible_factors(u, v)
            counts = mv(N, counts)
            observed = [factors.count(state) for state in STATES]
            assert observed == counts == [3**(level - 1)] * 3
            assert len(u) == len(v) == 3**(level + 1)
            assert len(factors) == 3**level
            for count in observed:
                assert Fraction(count, len(u)) == Fraction(1, 9)


def test_imprimitive_matrix_requires_class_subsequence():
    N = [[0, 2], [2, 0]]
    counts = [1, 0]
    ratios = []
    for n in range(20):
        assert sum(counts) == 2**n
        if n % 2 == 0:
            assert counts == [2**n, 0]
        else:
            assert counts == [0, 2**n]
        ratios.append(Fraction(counts[0], 2**n))
        counts = mv(N, counts)
    assert ratios == [Fraction(int(n % 2 == 0)) for n in range(20)]
    assert sum(ratios, Fraction()) / len(ratios) == Fraction(1, 2)
    h, delta = pf_pair_frequency(N, 2, [1, 1], [1, 1], ["e0", "e1"])
    assert h == 2 and delta == {"e0": Fraction(1), "e1": Fraction(1)}


def test_uniform_control_pf_frequency_matches_literal_ratio():
    N = [[1] * 3 for _ in range(3)]
    types = ["{0,1}", "{1,2}", "{0,2}"]  # first pairs of STATES
    assert [frozenset(a[0] + b[0]) for a, b in STATES] == [frozenset("01"), frozenset("12"), frozenset("02")]
    h, delta = pf_pair_frequency(N, 3, [1, 1, 1], [3, 3, 3], types)
    assert h == 1 and set(delta.values()) == {Fraction(1, 9)}


def test_selected_path_or_incomplete_state_set_fails_closed():
    try:
        exact_child_matrix((STATES[0],))
    except ValueError as exc:
        assert "escaped literal child" in str(exc)
    else:
        raise AssertionError("selected one-state subset was accepted")


def test_productive_pisot_control_contains_real_diagonal():
    sigma = ("01", "121", "012")
    top, bottom = "01", "10"
    for _ in range(3):
        top = "".join(sigma[int(c)] for c in top)
        bottom = "".join(sigma[int(c)] for c in bottom)
    factors = irreducible_factors(top, bottom)
    assert any(len(u) == len(v) == 1 and u == v for u, v in factors)
