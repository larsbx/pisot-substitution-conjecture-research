"""Independent finite exact C4 cone/rank/flat-hub certificate.

Reconstruct every actual ordered balanced child word from source letters;
not a graph-only or synthetic factorization test. A primitive irreducible
Pisot conclusion is NOT certified by this finite diagnostic.
"""
from collections import Counter
from itertools import combinations


SIGMA = ("10", "102", "211")
STATES = (
    ("102", "210"),
    ("11102", "21110"),
    ("10210211", "21110210"),
    ("10210210210211", "21110210210210"),
)


def inflate(sigma, word):
    return "".join(sigma[int(x)] for x in word)


def ordered_children(u, v):
    if Counter(u) != Counter(v):
        raise ValueError("unbalanced input")
    top, bottom = Counter(), Counter()
    start, result = 0, []
    for i, (a, b) in enumerate(zip(u, v), 1):
        top[a] += 1
        bottom[b] += 1
        if top == bottom:
            result.append((u[start:i], v[start:i]))
            start = i
            top.clear()
            bottom.clear()
    if start != len(u) or start != len(v):
        raise ValueError("missing terminal cut")
    return result


def parikh(u):
    return tuple(u.count(str(a)) for a in range(3))


def det(a, b, c):
    return (a[0] * (b[1] * c[2] - b[2] * c[1])
            - b[0] * (a[1] * c[2] - a[2] * c[1])
            + c[0] * (a[1] * b[2] - a[2] * b[1]))


def rank(vectors):
    if not vectors:
        return 0
    if any(det(*triple) for triple in combinations(vectors, 3)):
        return 3
    if any(any(x != 0 for x in (a[1]*b[2]-a[2]*b[1],
                                 a[2]*b[0]-a[0]*b[2],
                                 a[0]*b[1]-a[1]*b[0]))
           for a, b in combinations(vectors, 2)):
        return 2
    return 1 if any(any(v) for v in vectors) else 0


def literal_system(sigma, states):
    labels = {p: i for i, p in enumerate(states)}
    if len(labels) != len(states):
        raise ValueError("duplicate states")
    ids, raw = [], []
    for u, v in states:
        parts = ordered_children(inflate(sigma, u), inflate(sigma, v))
        if any(a == b for a, b in parts):
            raise ValueError("productive/diagonal child")
        if any(a != b and (a, b) not in labels for a, b in parts):
            raise ValueError("strict component not completely child-closed")
        ids.append([labels[p] for p in parts])
        raw.append(parts)
    return ids, raw


def test_closed_strict_two_generation_ranks_and_intertwiner():
    ids, raw = literal_system(SIGMA, STATES)
    assert ids == [[2], [3], [2, 0, 0, 1, 0],
                   [2, 0, 0, 1, 0, 1, 0, 1, 0]]
    assert [len(v) for v in raw] == [1, 1, 5, 9]
    P = [[u.count(str(k)) for u, _ in STATES] for k in range(3)]
    M = [[w.count(str(k)) for w in SIGMA] for k in range(3)]
    N = [[sum(child == row for child in ids[col]) for col in range(4)]
         for row in range(4)]
    assert P == [[1, 1, 2, 4], [1, 3, 4, 6], [1, 1, 2, 4]]
    assert M == [[1, 1, 0], [1, 1, 2], [0, 1, 1]]
    assert N == [[0, 0, 3, 5], [0, 0, 1, 3],
                 [1, 0, 1, 1], [0, 1, 0, 0]]
    for row in range(3):
        for col in range(4):
            assert sum(P[row][i] * N[i][col] for i in range(4)) == (
                sum(M[row][i] * P[i][col] for i in range(3))
            )
    masses = list(map(lambda p: parikh(p[0]), STATES))
    assert rank(masses) == 2
    assert rank(masses[:2]) == 2
    for root in range(4):
        cone_ids = [root, *ids[root]]
        for first in ids[root]:
            cone_ids.extend(ids[first])  # all *ordered* occurrences
        assert rank([masses[i] for i in cone_ids]) == 2
        assert len(cone_ids) >= 3
    # Exact primitive integral annihilator, a left eigenvector.
    normal = (1, 0, -1)
    assert all(sum(normal[i] * p[i] for i in range(3)) == 0
               for p in masses)
    assert tuple(sum(normal[row] * M[row][col] for row in range(3))
                 for col in range(3)) == normal


def test_both_compatible_hubs_are_flat_on_every_occurrence():
    ids, raw = literal_system(SIGMA, STATES)
    h = [w[0] for w in SIGMA]
    assert h == ["1", "1", "2"]
    # Good edge {0,1}, {0,2} only *compatible*, not verified good.
    for hub in ("1", "2"):
        bits = []
        for (u, v), row in zip(STATES, raw):
            assert hub in (u[0], v[0])
            source_side = int(v[0] == hub)
            bits.append([])
            for a, b in row:
                assert hub in (a[0], b[0])
                child_side = int(b[0] == hub)
                bits[-1].append(source_side ^ child_side)
        assert bits == [[0], [0], [0]*5, [0]*9]
        assert sum(map(len, bits)) == 16


def test_incomplete_or_productive_sources_are_not_strict_evidence():
    # A missing full child is not permitted to be silently quotiented.
    try:
        literal_system(SIGMA, STATES[:3])
        assert False, "partial strict support accepted"
    except ValueError:
        pass
    # Tribonacci source swap with a diagonal first child: productive.
    try:
        literal_system(("01", "02", "0"), (("01", "10"),))
        assert False, "productive graph accepted as strict"
    except ValueError:
        pass
