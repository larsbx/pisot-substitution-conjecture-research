"""Independent exact replay: a six-state periodic lattice template is not realizable.

All 1,296 child orders for sigma=(01,121,012), P=[M^2,M^2] and
N=[[0,M],[M,0]] are exhausted. 1,291 force a nonintegral mean-area;
the five integral cases cannot supply an irreducible noncoincident first
state of mass (1,3,1). This is ONE template, not general C4 or PSC.
No floating-point or third-party dependencies are used.
"""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations, product
from math import gcd, lcm
import json

PAIRS = ((0, 1), (0, 2), (1, 2))
SIGMA = ((0, 1), (1, 2, 1), (0, 1, 2))


def mm(a, b):
    if not a or not b or any(len(row) != len(b) for row in a):
        raise ValueError("matrix shape")
    if any(len(row) != len(b[0]) for row in b):
        raise ValueError("ragged matrix")
    return [[sum(x * b[k][j] for k, x in enumerate(row))
             for j in range(len(b[0]))] for row in a]


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def counts(w):
    if any(type(a) is not int or a not in (0, 1, 2) for a in w):
        raise ValueError("invalid letter")
    return tuple(w.count(a) for a in range(3))


def area(w):
    counts(w)  # Validate before indexing.
    return tuple(sum((int(a == i and b == j) - int(a == j and b == i))
                     for k, a in enumerate(w) for b in w[k + 1:])
                 for i, j in PAIRS)


def wedge(a, b):
    return tuple(a[i] * b[j] - a[j] * b[i] for i, j in PAIRS)


def det_bareiss(a):
    if not a or any(len(row) != len(a) for row in a):
        raise ValueError("square matrix required")
    b = [list(row) for row in a]
    previous, sign, n = 1, 1, len(b)
    for k in range(n - 1):
        pivot = next((i for i in range(k, n) if b[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            b[k], b[pivot] = b[pivot], b[k]
            sign = -sign
        q = b[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                value = q * b[i][j] - b[i][k] * b[k][j]
                if value % previous:
                    raise ArithmeticError("Bareiss exact division failed")
                b[i][j] = value // previous
            b[i][k] = 0
        previous = q
    return sign * b[-1][-1]


def inverse(a):
    n = len(a)
    if n < 1 or n > 24 or any(len(row) != n for row in a):
        raise ValueError("inverse size/shape budget")
    rows = [[Fraction(x) for x in a[i] + eye(n)[i]] for i in range(n)]
    for k in range(n):
        pivot = next((i for i in range(k, n) if rows[i][k]), None)
        if pivot is None:
            raise ValueError("singular operator: inconclusive, not an exclusion")
        rows[k], rows[pivot] = rows[pivot], rows[k]
        q = rows[k][k]
        rows[k] = [x / q for x in rows[k]]
        for i in range(n):
            if i != k:
                q = rows[i][k]
                rows[i] = [x - q * y for x, y in zip(rows[i], rows[k])]
    return [row[n:] for row in rows]


def certify_inverse(operator, numerator, denominator):
    n = len(operator)
    if type(denominator) is not int or denominator <= 0 or n not in range(1, 25):
        raise ValueError("inverse certificate dimensions/sign")
    for mat in (operator, numerator):
        if len(mat) != n or any(len(row) != n for row in mat):
            raise ValueError("inverse certificate shape")
        if any(type(x) is not int or abs(x) > 10**6 for row in mat for x in row):
            raise ValueError("inverse certificate integer budget")
    expected = [[denominator * int(i == j) for j in range(n)] for i in range(n)]
    if mm(operator, numerator) != expected or mm(numerator, operator) != expected:
        raise ValueError("invalid two-sided exact inverse certificate")


@lru_cache(maxsize=1)
def packet():
    m = [[SIGMA[j].count(i) for j in range(3)] for i in range(3)]
    p0 = mm(m, m)
    p = [row + row for row in p0]
    n = [[m[i % 3][j % 3] if i // 3 != j // 3 else 0
          for j in range(6)] for i in range(6)]
    exterior = [[m[i][k] * m[j][l] - m[i][l] * m[j][k]
                 for k, l in PAIRS] for i, j in PAIRS]
    operator = [[(exterior[a][b] if i == j else 0)
                 - (n[j][i] if a == b else 0)
                 for j in range(6) for b in range(3)]
                for i in range(6) for a in range(3)]
    inv = inverse(operator)
    denominator = lcm(*(v.denominator for row in inv for v in row))
    numerator = [[int(denominator * v) for v in row] for row in inv]
    certify_inverse(operator, numerator, denominator)
    c = [[area(SIGMA[j])[i] for j in range(3)] for i in range(3)]
    cp = mm(c, p)
    rows = []
    for parent in range(6):
        multiset = tuple(child for child in range(6) for _ in range(n[child][parent]))
        rows.append(tuple(sorted(set(permutations(multiset)))))
    return m, p, n, exterior, operator, numerator, denominator, cp, rows


def right_hand_column(p, cp, parent, child_row):
    total = [0, 0, 0]
    for r, child in enumerate(child_row):
        for other in child_row[r + 1:]:
            value = wedge([p[i][child] for i in range(3)], [p[i][other] for i in range(3)])
            total = [a + b for a, b in zip(total, value)]
    return [total[i] - cp[i][parent] for i in range(3)]


@lru_cache(maxsize=1)
def census():
    m, p, n, exterior, operator, numerator, denominator, cp, row_options = packet()
    contributions = []
    for parent, options in enumerate(row_options):
        contributions.append([])
        for child_row in options:
            rhs = right_hand_column(p, cp, parent, child_row)
            contributions[-1].append(tuple(sum(numerator[i][3 * parent + k] * rhs[k]
                                                for k in range(3)) for i in range(18)))
    histogram = Counter()
    survivors = []
    for choices in product(*(range(len(options)) for options in row_options)):
        vector = tuple(sum(contributions[j][choice][i] for j, choice in enumerate(choices))
                       for i in range(18))
        actual_denominator = lcm(*(denominator // gcd(denominator, value) for value in vector))
        histogram[actual_denominator] += 1
        if actual_denominator == 1:
            survivors.append((choices, tuple(value // denominator for value in vector)))
    return dict(sorted(histogram.items())), tuple(survivors)


def irreducible_noncoincident(u, v):
    if u == v or counts(u) != counts(v) or not u:
        return False
    defect = [0, 0, 0]
    for k, (a, b) in enumerate(zip(u, v), 1):
        defect[a] += 1
        defect[b] -= 1
        if not any(defect) and k != len(u):
            return False
    return not any(defect)


def first_state_pairs(mean):
    words = sorted(set(permutations((0, 1, 1, 1, 2))))
    values = {w: area(w) for w in words}
    return [(u, v) for u in words for v in words
            if irreducible_noncoincident(u, v)
            and all(values[u][i] + values[v][i] == 2 * mean[i] for i in range(3))]


def test_signature_identity_and_literal_pair_controls():
    m, p, n, a, _, _, _, _, _ = packet()
    c = [[area(SIGMA[j])[i] for j in range(3)] for i in range(3)]
    for word in sorted(set(permutations((0, 1, 1, 1, 2)))):
        image = tuple(z for letter in word for z in SIGMA[letter])
        expected = [sum(a[i][j] * area(word)[j] + c[i][j] * counts(word)[j]
                        for j in range(3)) for i in range(3)]
        assert area(image) == tuple(expected)
    assert irreducible_noncoincident((0, 1), (1, 0))
    assert not irreducible_noncoincident((0, 1, 2), (0, 2, 1))


def test_lattice_packet_and_exact_inverse():
    m, p, n, a, operator, numerator, denominator, cp, rows = packet()
    assert mm(p, n) == mm(m, p)
    assert mm(n, n) == [[mm(m, m)[i % 3][j % 3] if i // 3 == j // 3 else 0
                         for j in range(6)] for i in range(6)]
    assert all(x > 0 for row in p for x in row)
    assert det_bareiss(m) == 2
    assert det_bareiss([row[:3] for row in p]) == 4
    assert det_bareiss([row[3:] for row in p]) == 4
    assert det_bareiss(operator) == -596288
    certify_inverse(operator, numerator, denominator)
    assert tuple(map(len, rows)) == (2, 3, 6, 2, 3, 6)


def test_all_orders_and_every_integral_survivor():
    histogram, survivors = census()
    assert histogram == {1: 5, 7: 31, 11: 8, 77: 90, 121: 168, 847: 994}
    assert sum(histogram.values()) == 1296
    assert [choice for choice, _ in survivors] == [
        (0, 0, 2, 0, 0, 2), (0, 1, 0, 0, 1, 0), (1, 0, 5, 1, 0, 5),
        (1, 1, 4, 1, 1, 4), (1, 2, 2, 1, 2, 2)]
    assert [j[:3] for _, j in survivors] == [
        (7, 3, 3), (3, 1, 1), (1, 1, 3), (-3, -1, 1), (-3, -3, -1)]
    for _, mean in survivors:
        assert first_state_pairs(mean[:3]) == []


def test_malformed_inverse_and_letters_refuse():
    _, _, _, _, op, num, den, _, _ = packet()
    broken = [row.copy() for row in num]
    broken[0][0] += 1
    for cert in ((op, broken, den), (op, num, 0), (op, num[:-1], den)):
        try:
            certify_inverse(*cert)
        except ValueError:
            pass
        else:
            raise AssertionError("bad exact inverse was accepted")
    for word in ((3,), (-1,), (True,)):
        try:
            area(word)
        except ValueError:
            pass
        else:
            raise AssertionError("bad letter was accepted")


def test_native_fixture_matches_recomputed_inverse():
    import ast
    from pathlib import Path
    root = Path(__file__).resolve().parents[1]
    fixture = root / "kernel/tests/c4_periodic_lift_fixture.mojo"
    supplied = ast.literal_eval(fixture.read_text().split("return ", 1)[1].strip())
    _, _, _, _, operator, computed, denominator, _, _ = packet()
    assert supplied == computed
    certify_inverse(operator, supplied, denominator)


def test_periodic_operator_determinants_equal_return_operator():
    m, _, _, a, _, _, _, _, _ = packet()
    mh, ah = eye(3), eye(3)
    expected = (-56, -596288, -628178432, -341820903424)
    for h in range(1, 5):
        mh, ah = mm(mh, m), mm(ah, a)
        r = 3 * h
        n = [[m[i % 3][j % 3] if i // 3 == (j // 3 + 1) % h else 0
              for j in range(r)] for i in range(r)]
        operator = [[(a[x][y] if i == j else 0) - (n[j][i] if x == y else 0)
                     for j in range(r) for y in range(3)]
                    for i in range(r) for x in range(3)]
        returned = [[(ah[x][y] if i == j else 0) - (mh[j][i] if x == y else 0)
                     for j in range(3) for y in range(3)]
                    for i in range(3) for x in range(3)]
        assert det_bareiss(operator) == det_bareiss(returned) == expected[h - 1]


if __name__ == "__main__":
    histogram, survivors = census()
    m, p, n, a, op, num, den, cp, rows = packet()
    print(json.dumps({
        "scope": "one synthetic six-state period-two template; not general C4/PSC",
        "sigma": [list(w) for w in SIGMA], "M": m, "P": p, "N": n,
        "operator_determinant": det_bareiss(op), "inverse_denominator": den,
        "inverse_numerator": num, "order_count": sum(histogram.values()),
        "denominator_histogram": histogram,
        "integral_survivors": [{"choices": c, "first_state_mean_area": j[:3],
                               "irreducible_pair_count": len(first_state_pairs(j[:3]))}
                              for c, j in survivors]}, indent=2))
