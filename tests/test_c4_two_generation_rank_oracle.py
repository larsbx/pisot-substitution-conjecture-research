"""Independent exact literal-word oracle for the C4 depth-two Parikh span.

No Mojo or graph-cache imports. Finite regression does not prove the
universal irreducible-cyclic-vector statement in the accompanying note.
"""
from collections import Counter
from itertools import product, permutations


def inflate(sigma, word):
    return "".join(sigma[int(c)] for c in word)


def factor(top, bottom):
    assert Counter(top) == Counter(bottom)
    a, b = Counter(), Counter()
    start, out = 0, []
    for i, (x, y) in enumerate(zip(top, bottom), 1):
        a[x] += 1
        b[y] += 1
        if a == b:
            out.append((top[start:i], bottom[start:i]))
            start = i
            a.clear()
            b.clear()
    assert start == len(top) == len(bottom)
    return out


def p(word):
    return tuple(word.count(str(i)) for i in range(3))


def det(a, b, c):
    return (a[0] * (b[1] * c[2] - b[2] * c[1])
            - b[0] * (a[1] * c[2] - a[2] * c[1])
            + c[0] * (a[1] * b[2] - a[2] * b[1]))


def cross(a, b):
    return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2],
            a[0]*b[1]-a[1]*b[0])


def literal_descendants(sigma, root):
    assert Counter(root[0]) == Counter(root[1]) and root[0]
    out = [(0, -1, -1, root, p(root[0]))]
    first = factor(inflate(sigma, root[0]), inflate(sigma, root[1]))
    out += [(1, i, -1, z, p(z[0])) for i, z in enumerate(first)]
    for i, (a, b) in enumerate(first):
        for j, z in enumerate(factor(inflate(sigma, a), inflate(sigma, b))):
            out.append((2, i, j, z, p(z[0])))
    return out


def pivot_ids(desc):
    ids = []
    for i, (*_, v) in enumerate(desc):
        if not ids and v != (0, 0, 0):
            ids.append(i)
        elif len(ids) == 1 and cross(desc[ids[0]][4], v) != (0, 0, 0):
            ids.append(i)
        elif len(ids) == 2 and det(desc[ids[0]][4], desc[ids[1]][4], v):
            ids.append(i)
    return ids


def matrix(sigma):
    return [[sigma[j].count(str(i)) for j in range(3)] for i in range(3)]


def matvec(m, v):
    return tuple(sum(row[j] * v[j] for j in range(3)) for row in m)


def assert_krylov_span(sigma, root):
    desc = literal_descendants(sigma, root)
    ids = pivot_ids(desc)
    a = p(root[0]); b = matvec(matrix(sigma), a)
    c = matvec(matrix(sigma), b)
    assert det(a, b, c) != 0
    assert len(ids) == 3
    for level, rhs in ((0, a), (1, b), (2, c)):
        rows = [rec[4] for rec in desc if rec[0] == level]
        assert tuple(sum(v[k] for v in rows) for k in range(3)) == rhs
    return desc, ids


def test_real_secondary_depth_two_is_sharp():
    sigma = ["1", "02", "202"]
    desc, ids = assert_krylov_span(sigma, ("01", "10"))
    assert [r[3] for r in desc] == [
        ("01", "10"), ("102", "021"),
        ("021", "120"), ("2", "2"), ("0", "0"), ("2", "2")]
    assert ids == [0, 1, 4]
    assert det(*(desc[i][4] for i in ids)) == 1
    assert len(set(r[4] for r in desc[:2])) == 2


def test_tribonacci_rank_is_visible_at_level_one():
    sigma = ["01", "02", "0"]
    desc, ids = assert_krylov_span(sigma, ("01", "10"))
    assert ids == [0, 1, 2]
    assert [r[3] for r in desc[:3]] == [
        ("01", "10"), ("0", "0"), ("102", "201")]


def test_primitive_fullrank_reducible_strict_rank_two():
    sigma = ["10", "102", "211"]
    root = ("102", "210")
    desc = literal_descendants(sigma, root)
    assert len(desc) == 7
    assert pivot_ids(desc) == [0, 1]
    assert all(q[0] == q[2] for _, _, _, _, q in desc)
    a = p(root[0]); b = matvec(matrix(sigma), a)
    c = matvec(matrix(sigma), b)
    assert det(a, b, c) == 0
    assert cross(a, b) != (0, 0, 0)


def test_all_short_balanced_sources_on_two_named_pip_substitutions():
    for sigma in (["1", "02", "202"], ["01", "02", "0"]):
        count = 0
        for n in (2, 3):
            for letters in product("012", repeat=n):
                word = "".join(letters)
                for perm in set(permutations(word)):
                    other = "".join(perm)
                    if other != word:
                        _, ids = assert_krylov_span(sigma, (word, other))
                        assert len(ids) == 3
                        count += 1
        assert count > 0
