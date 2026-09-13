"""Exact swap-walk discrepancy kernels (bounded discrepancy, G1b-1).

For a seed `(ab, ba)` and a level `n` the *swap walk* is the prefix-difference
walk of the inflated pair `(sigma^n(ab), sigma^n(ba))`:

    Delta_n(j) = parikh(sigma^n(ab)[:j]) - parikh(sigma^n(ba)[:j]).

Every state of `B_sigma` is a zero-return block of some such pair, so its own
prefix-difference walk is a segment of a swap walk starting at `0` and

    Disc(T) <= max_j ||Delta_n(j)||_inf.

The bounded-discrepancy theorem
(docs/source-imports/issue-45/g1b1-bounded-discrepancy-reconstruction.md)
proves that this supremum is uniformly bounded in `n`; this module only
evaluates it exactly, with a fixed three-coordinate accumulator and no
floating point.
"""

from psc.bpa import Automaton, apply_substitution
from psc.words import Pair


def discrepancy(p: Pair) -> Int:
    """`max_k ||parikh(u[:k]) - parikh(v[:k])||_inf` over the prefixes of a balanced pair."""
    var diff: List[Int] = [0, 0, 0]
    var best = 0
    for i in range(len(p.u)):
        var x = p.u[i]
        var y = p.v[i]
        diff[x] = diff[x] + 1
        diff[y] = diff[y] - 1
        for j in range(3):
            var a = diff[j] if diff[j] >= 0 else -diff[j]
            if a > best:
                best = a
    return best


def iterate(sigma: List[List[Int]], w: List[Int], level: Int) -> List[Int]:
    """`sigma^level(w)`."""
    var out = w.copy()
    for _ in range(level):
        out = apply_substitution(sigma, out)
    return out^


def swap_walk_sup(sigma: List[List[Int]], a: Int, b: Int, level: Int) -> Int:
    """`max_j ||Delta_level(j)||_inf` for the seed `(ab, ba)`."""
    var ab: List[Int] = [a, b]
    var ba: List[Int] = [b, a]
    var u = iterate(sigma, ab, level)
    var v = iterate(sigma, ba, level)
    return discrepancy(Pair(u, v))


def swap_walk_profile(sigma: List[List[Int]], max_level: Int) -> List[Int]:
    """Entry `n` is the maximum over the three seeds of the level-`n` swap-walk supremum."""
    var out = List[Int]()
    for n in range(max_level + 1):
        var best = 0
        for a in range(3):
            for b in range(a + 1, 3):
                var s = swap_walk_sup(sigma, a, b, n)
                if s > best:
                    best = s
        out.append(best)
    return out^


def max_reachable_discrepancy(a: Automaton) -> Int:
    """Largest discrepancy over the vertices of a reachable balanced-pair graph."""
    var best = 0
    for i in range(a.size()):
        var d = discrepancy(a.states[i])
        if d > best:
            best = d
    return best


def max_state_length(a: Automaton) -> Int:
    var best = 0
    for i in range(a.size()):
        var n = a.states[i].length()
        if n > best:
            best = n
    return best


def common_tile_count(sigma: List[List[Int]], a: Int, b: Int, level: Int) -> List[Int]:
    """[common tiles, all tiles] of the level-`level` swap pair `(ab, ba)`.

    A common tile is a position with equal letters on both sides and a zero
    prefix difference before it (a coincidence block of the reduction)."""
    var ab: List[Int] = [a, b]
    var ba: List[Int] = [b, a]
    var u = iterate(sigma, ab, level)
    var v = iterate(sigma, ba, level)
    var diff: List[Int] = [0, 0, 0]
    var common = 0
    for i in range(len(u)):
        if u[i] == v[i] and diff[0] == 0 and diff[1] == 0 and diff[2] == 0:
            common += 1
        diff[u[i]] = diff[u[i]] + 1
        diff[v[i]] = diff[v[i]] - 1
    var out: List[Int] = [common, len(u)]
    return out^
