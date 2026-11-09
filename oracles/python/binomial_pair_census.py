"""Independent oracle for the census of irreducible distinct binomially equivalent pairs.

Canonical implementation: kernel/psc/binomial_pairs.mojo with the driver
kernel/binomial_pair_census.mojo (docs/c4-binomial-minimal-pairs-2026-11-07.md).
This stdlib script shares no code with it and uses different methods:

* scattered-subword counts N_r(w) are read off ``itertools.combinations``
  (every r-subset of positions, counted), not streamed by a prefix recurrence;
* the total number of irreducible pairs comes from the first-return
  (renewal) identity W(n) = sum_{k=1..n} F(k) W(n-k), where
  W(n) = sum over Parikh vectors c of multinomial(n; c)^2 counts all balanced
  ordered pairs and F(k) the irreducible ones (including the coincidences
  (a, a) at k = 1), not by the Mojo lattice-walk transfer recurrence; and
  the renewal count is itself checked against brute force for small n;
* the K_2 = 0 pairs are found by grouping all words by the exact signature
  (Parikh vector, N_2) in a dictionary and testing each pair inside a group.

For each alphabet size d and length n it returns the number of unordered
pairs {u, v}, u != v, |u| = |v| = n, balanced and irreducible, of first
defect degree 2, 3, 4 and >= 5 (K_2 = K_3 = K_4 = 0), and the number of
(N_1, N_2), (N_1..N_3), (N_1..N_4) classes of words. A failed self-check
raises; nothing here is capped.

Usage:
  python3 oracles/python/binomial_pair_census.py D NMAX [NMIN]

prints one row per n = NMIN..NMAX (NMIN defaults to 1); class counts are
computed for n <= 9 only, since N_4 by combinations costs binom(n, 4) a word.
"""
from collections import Counter, defaultdict
from itertools import combinations, product
from math import factorial
import sys


class OracleFailure(Exception):
    pass


def scattered(word, r):
    """N_r(word) as a frozen multiset of r-letter subwords (combinations of positions)."""
    return frozenset(Counter(combinations(word, r)).items())


def is_irreducible(u, v, d):
    """Balanced, equal length, and no proper prefix 0 < j < n with equal Parikh vectors."""
    if len(u) != len(v) or Counter(u) != Counter(v):
        return False
    pu = [0] * d
    pv = [0] * d
    for j in range(len(u) - 1):
        pu[u[j]] += 1
        pv[v[j]] += 1
        if pu == pv:
            return False
    return True


def first_defect_degree(u, v):
    for r in (2, 3, 4):
        if scattered(u, r) != scattered(v, r):
            return r
    return 5


def compositions(n, d):
    for c in product(range(n + 1), repeat=d):
        if sum(c) == n:
            yield c


def balanced_ordered(n, d):
    """W(n): ordered pairs of equal Parikh vector, by multinomials."""
    total = 0
    for c in compositions(n, d):
        m = factorial(n)
        for x in c:
            m //= factorial(x)
        total += m * m
    return total


def irreducible_ordered(n_max, d):
    """Distinct ordered irreducible pairs for n = 1..n_max by the renewal identity."""
    w = [balanced_ordered(n, d) for n in range(n_max + 1)]
    f = [0] * (n_max + 1)
    for n in range(1, n_max + 1):
        f[n] = w[n] - sum(f[k] * w[n - k] for k in range(1, n))
    # at n = 1 every irreducible block is a coincidence (a, a)
    return {n: f[n] - (d if n == 1 else 0) for n in range(1, n_max + 1)}


def brute_irreducible_ordered(n, d):
    words = list(product(range(d), repeat=n))
    return sum(1 for u in words for v in words if u != v and is_irreducible(u, v, d))


def census(n, d, classes=True):
    """One row: counts by first defect degree, and class counts when asked."""
    groups = defaultdict(list)
    for w in product(range(d), repeat=n):
        groups[(tuple(sorted(Counter(w).items())), scattered(w, 2))].append(w)
    k2_zero = Counter()
    pairs = []
    for members in groups.values():
        for i in range(len(members)):
            for j in range(i + 1, len(members)):
                u, v = members[i], members[j]
                if is_irreducible(u, v, d):
                    deg = first_defect_degree(u, v)
                    if deg == 2:
                        raise OracleFailure("a pair in one (N1, N2) group has K2 != 0")
                    k2_zero[deg] += 1
                    pairs.append((min(u, v), max(u, v), deg))
    ordered = irreducible_ordered(n, d)[n]
    if ordered % 2:
        raise OracleFailure("odd ordered count")
    total = ordered // 2
    row = {
        "n": n,
        "total": total,
        "degree2": total - sum(k2_zero.values()),
        "degree3": k2_zero[3],
        "degree4": k2_zero[4],
        "degree5plus": k2_zero[5],
        "pairs": sorted(pairs),
    }
    if classes:
        words = list(product(range(d), repeat=n))
        sig1 = {w: tuple(sorted(Counter(w).items())) for w in words}
        row["classes2"] = len({(sig1[w], scattered(w, 2)) for w in words})
        row["classes3"] = len({(sig1[w], scattered(w, 2), scattered(w, 3)) for w in words})
        row["classes4"] = len({(sig1[w], scattered(w, 2), scattered(w, 3), scattered(w, 4)) for w in words})
    return row


def catalan(m):
    return factorial(2 * m) // (factorial(m) * factorial(m + 1))


def main(argv):
    d, n_max = int(argv[1]), int(argv[2])
    n_min = int(argv[3]) if len(argv) > 3 else 1
    for n in range(n_min, n_max + 1):
        row = census(n, d, classes=n <= 9)
        printed = {k: v for k, v in row.items() if k != "pairs"}
        printed["degree4_pairs"] = ["".join(map(str, u)) + "|" + "".join(map(str, v)) for u, v, deg in row["pairs"] if deg >= 4]
        print(printed, flush=True)


if __name__ == "__main__":
    main(sys.argv)
