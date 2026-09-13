"""Exploratory: types of the Sirvent--Solomyak overlap graph G_O(T, x(W))
for the pair (T, T - beta^n x(W)), n >= 0, where T is the tiling of a fixed
point u of a prolongable power tau = sigma^q and W is a prefix of u, compared
with the vertex types of the seed-patch graph O_sigma.

Level-0 overlap types of (u, S^k u), k = |W|, are enumerated from the factors
of u found in a long prefix (an exploratory, not certified, factor set), then
closed under the exact inflation of `OverlapGraph`.  Productivity of an
overlap depends only on its type, so
    types(G_O) subset of types(O_sigma)
would transfer seed-patch productivity to the literature graph.
"""
from __future__ import annotations

from collections import deque

from .bpa import apply_substitution_n
from .overlap_graph import Elt, OverlapGraph


def prolongable_power(sigma) -> tuple[int, int]:
    """(q, c) with sigma^q(c) starting with c, q minimal (first-letter map cycle)."""
    first = {a: sigma[a][0] for a in sigma}
    for q in range(1, len(sigma) + 1):
        for c in sorted(sigma):
            x = c
            for _ in range(q):
                x = first[x]
            if x == c:
                return q, c
    raise ValueError("no prolongable power found")


def fixed_point_prefix(sigma, q: int, c: int, min_len: int) -> tuple[int, ...]:
    u = (c,)
    while len(u) < min_len:
        u = apply_substitution_n(sigma, u, q)
    return u


def oa_types(g: OverlapGraph, u: tuple[int, ...], k: int, window: int) -> set[tuple[int, int, Elt]]:
    """Closure under inflation of the level-0 overlap types of (u, S^k u).

    Level 0: top tile i (letter u[i]) at g(u[:i]); bottom tile m (letter u[m])
    at g(u[:m]) - g(u[:k]); the offset is <l, w> with the integer vector
    w = pi(u[i:m]) - pi(W) (m >= i) or -pi(u[m:i]) - pi(W) (m < i).  Only tiles
    within `window` letters of each other can overlap; `window` must exceed
    (g(W) + l_max)/l_min.  Distinct integer keys (a, b, w) are collected first
    with prefix sums, so the exact sign tests run once per key."""
    F = g.F
    d = 3
    n = len(u)
    pref = [[0] * d]
    for a in u:
        row = pref[-1][:]
        row[a - 1] += 1
        pref.append(row)
    pW = pref[k]
    keys = set()
    for i in range(window, n - window):
        for m in range(i - window, i + window):
            w = tuple(pref[m][c] - pref[i][c] - pW[c] for c in range(d))
            keys.add((u[i], u[m], w))
    seeds = set()
    for a, b, w in keys:
        t = F.zero
        for c in range(d):
            if w[c]:
                t = F.add(t, tuple(x * w[c] for x in g.l[c]))
        s = (a, b, t)
        if g.overlaps(s):
            seeds.add(s)
    types = set()
    queue = deque(seeds)
    while queue:
        s = queue.popleft()
        if s in types:
            continue
        types.add(s)
        if OverlapGraph.is_coincidence(s):
            continue
        queue.extend(g.children(s))
    return types


def type_inclusion_report(sigma, k: int = 1, prefix_len: int = 20000, window: int = 12):
    q, c = prolongable_power(sigma)
    u = fixed_point_prefix(sigma, q, c, prefix_len)
    g = OverlapGraph(sigma)
    seed_types = set(g.states)
    oa = oa_types(g, u, k, window)
    noncoinc = lambda s: not OverlapGraph.is_coincidence(s)
    missing = [s for s in oa if s not in seed_types and noncoinc(s)]
    extra = [s for s in seed_types if s not in oa and noncoinc(s)]
    # productivity of the missing types inside the closed set `oa`
    good = {s for s in oa if OverlapGraph.is_coincidence(s)}
    changed = True
    while changed:
        changed = False
        for s in oa:
            if s not in good and any(c in good for c in g.children(s)):
                good.add(s); changed = True
    return {"q": q, "c": c, "W": u[:k], "oa_types": len(oa), "seed_types": len(seed_types),
            "oa_minus_seed_noncoincidence": len(missing), "seed_minus_oa_noncoincidence": len(extra),
            "missing_all_productive": all(s in good for s in missing),
            "oa_all_productive": all(s in good for s in oa),
            "missing_examples": [(s[0], s[1], tuple(str(x) for x in s[2])) for s in missing[:6]]}
