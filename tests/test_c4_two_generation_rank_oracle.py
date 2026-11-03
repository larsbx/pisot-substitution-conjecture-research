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


def test_phase_zero_flat_rank_three_PIP_cone_needs_a_later_escape():
    """Strong negative: rank three + genuine good edge + flat whole words to depth 2.

    Every displayed edge is an actual literal ordered child, not a
    synthetic graph transition. The cone is PRODUCTIVE after depth two,
    so it does not refute strict PIP C4.
    """
    sigma = ["01", "12", "021"]
    root = ("10", "01")
    M = matrix(sigma)
    assert M == [[1, 0, 1], [1, 1, 1], [0, 1, 1]]
    # det M = 1, chi_M = x^3 - 3x^2 + 2x - 1, discriminant -23.
    assert det((1, 1, 0), (0, 1, 1), (1, 1, 1)) == 1
    assert all(
        sum(M[i][k] * M[k][j] for k in range(3)) > 0
        for i in range(3) for j in range(3)
    )
    assert [1**3 - 3 * 1**2 + 2 * 1 - 1,
            (-1)**3 - 3 * (-1)**2 + 2 * (-1) - 1] == [-1, -7]

    level1 = factor(inflate(sigma, root[0]), inflate(sigma, root[1]))
    assert level1 == [("1201", "0112")]
    level2 = factor(inflate(sigma, level1[0][0]),
                    inflate(sigma, level1[0][1]))
    assert level2 == [("1202101", "0112120"), ("12", "21")]
    desc, pivots = assert_krylov_span(sigma, root)
    assert len(desc) == 4 and pivots == [0, 1, 2]
    assert [x[4] for x in desc] == [
        (1, 1, 0), (1, 2, 1), (2, 3, 2), (0, 1, 1)
    ]
    assert det(*(desc[i][4] for i in pivots)) == 1

    # Genuine Barge-Diamond-good prefix edge {0,2}: both images start 0.
    first = [w[0] for w in sigma]
    last = [w[-1] for w in sigma]
    assert first == ["0", "1", "0"] and last == ["1", "2", "1"]
    assert first[0] == first[2]
    # Physical hub 1 is TOP on root, first child and both second-level
    # children. Thus each actual *ordered* hub word is all-zero.
    assert all(top[0] == "1" and bottom[0] != "1"
               for top, bottom in [root, *level1, *level2])

    def synchronizes(f, x, y):
        for _ in range(4):
            if x == y:
                return True
            x, y = f[int(x)], f[int(y)]
        return x == y

    parent = level1[0]
    top, bottom = inflate(sigma, parent[0]), inflate(sigma, parent[1])
    zero_returns = [i for i in range(len(top)+1)
                    if Counter(top[:i]) == Counter(bottom[:i])]
    assert zero_returns == [0, 7, 9]
    assert (top[6], bottom[6]) == ("1", "0")
    assert (top[7], bottom[7]) == ("1", "2")
    assert not synchronizes(last, top[6], bottom[6])
    assert not synchronizes(first, top[7], bottom[7])
    # Literal source addresses at this newborn cut:
    # top: source index 3, digit 0; bottom: index 3, digit 1.
    assert (sum(map(len, [sigma[int(a)] for a in parent[0][:3]])),
            sum(map(len, [sigma[int(a)] for a in parent[1][:3]]))) == (7, 6)
    E = tuple(parent[0][:3].count(str(i))-parent[1][:3].count(str(i))
              for i in range(3))
    c = tuple(sigma[1][:0].count(str(i))-sigma[2][:1].count(str(i))
              for i in range(3))
    assert E == (0, -1, 1) and c == (-1, 0, 0)
    assert tuple(x+y for x, y in zip(matvec(M, E), c)) == (0, 0, 0)

    # The next depth destroys flatness: a genuinely prefix-good 0/2
    # child is born at global depth 3. Its next inflation gives 0/0.
    level3 = factor(inflate(sigma, level2[0][0]),
                    inflate(sigma, level2[0][1]))
    assert level3 == [
        ("1202101", "0112120"), ("02112", "21120"),
        ("0112", "2101")
    ]
    assert level3[1][0][0] == "0" and level3[1][1][0] == "2"
    assert first[0] == first[2]
    level4_exit = factor(inflate(sigma, level3[1][0]),
                         inflate(sigma, level3[1][1]))
    assert level4_exit[0] == ("0", "0")
    # Actual selected ordered child ordinals: 0,0,1,0.
