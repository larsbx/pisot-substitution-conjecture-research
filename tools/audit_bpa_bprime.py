#!/usr/bin/env python3
"""Independent deterministic B′ arithmetic/child-closure controls.

No external dependencies; finite exploration does NOT prove nontermination.
"""
from collections import Counter
import json

SUB = {"0": "01", "1": "2", "2": "00"}
M = ((1, 0, 2), (1, 0, 0), (0, 1, 0))


def mmul(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(3))
                       for j in range(3)) for i in range(3))


def matvec(m, v):
    return tuple(sum(m[i][j] * v[j] for j in range(3)) for i in range(3))


def det3(a):
    return (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
            - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
            + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0]))


def incidence(sub):
    return tuple(tuple(sub[str(j)].count(str(i)) for j in range(3))
                 for i in range(3))


def substitute(word):
    return "".join(SUB[c] for c in word)


def reduction(u, v):
    assert len(u) == len(v) and Counter(u) == Counter(v)
    difference, children, start = Counter(), [], 0
    for pos, (a, b) in enumerate(zip(u, v), 1):
        difference[a] += 1
        difference[b] -= 1
        if all(z == 0 for z in difference.values()):
            children.append((u[start:pos], v[start:pos]))
            start = pos
    assert start == len(u)
    assert all(Counter(a) == Counter(b) for a, b in children)
    assert all(not any(Counter(a[:k]) == Counter(b[:k])
                       for k in range(1, len(a))) for a, b in children)
    return children


def main():
    assert incidence(SUB) == M
    power = M
    for _ in range(4):
        power = mmul(power, M)
    assert all(v > 0 for row in power for v in row)  # M^5 > 0
    trace = sum(M[i][i] for i in range(3))
    minors = sum(M[i][i] * M[j][j] - M[i][j] * M[j][i]
                 for i in range(3) for j in range(i + 1, 3))
    assert (trace, minors, det3(M)) == (1, 0, 2)
    p = lambda x: x**3 - x**2 - 2
    assert all(p(r) != 0 for r in (-2, -1, 1, 2))
    assert p(1) < 0 < p(2)
    # p'=x(3x-2), p(0)<0, p(2/3)<0: only one real beta in (1,2).
    # The conjugate pair then satisfies |alpha|^2 = 2/beta > 1.
    v, columns = (1, 0, 0), []
    for _ in range(3):
        columns.append(v)
        v = matvec(M, v)
    krylov = tuple(tuple(columns[j][i] for j in range(3))
                   for i in range(3))
    assert det3(krylov) == 1
    frontier, seen, sizes = {("01", "10")}, {("01", "10")}, [1]
    for depth in range(12):
        children = set()
        for a, b in sorted(frontier):
            children.update(reduction(substitute(a), substitute(b)))
        frontier = children - seen
        seen |= frontier
        sizes.append(len(seen))
    assert sizes == [1, 2, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16]
    assert len(frontier) == 1
    print(json.dumps({
        "substitution": SUB,
        "primitive_positive_power": 5,
        "characteristic": "x^3-x^2-2",
        "irreducible_rational_roots_tested": [-2, -1, 1, 2],
        "non_pisot_exact": "beta in (1,2), |alpha|^2=2/beta>1",
        "krylov_det_W_0": det3(krylov),
        "swap_closure_unique_states_after_each_generation": sizes,
        "note": "finite regression, NOT proof of nontermination"
    }, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
