"""Independent exact replay of the named Mojo box-graph exports.

PYTHONPATH=reference python oracles/python/omega_box_audit.py EXPORT

The reference field uses rational interval refinement, not the canonical
Sturm--Tarski sign kernel. Recompute all children, the complete start set,
reverse-BFS depths and Kosaraju SCCs. No floating values enter a decision.
The canonical implementation remains kernel/psc/vertex_coincidence.mojo.
"""
from __future__ import annotations

import hashlib
import json
import sys
from collections import deque
from fractions import Fraction
from pathlib import Path
from types import SimpleNamespace

from psc_research.formal_overlap import _inverse
from psc_research.overlap_graph import Field, charpoly, left_perron_lengths
from psc_research.overlap_obstruction import sccs


SPECIMENS = {
    "tribonacci": ((0, 1), (0, 2), (0,)),
    "cube": ((1,), (2, 2, 2), (0, 2, 2, 2)),
    "golden": ((1,), (0, 2, 1), (0, 0, 1)),
    "plastic": ((1,), (2,), (1, 0)),
    "real-secondary": ((1,), (0, 2), (2, 0, 2)),
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def exported(path):
    current = None
    for line in path.read_text().splitlines():
        items = line.split()
        require(bool(items), "empty export line")
        tag = items[0]
        if tag == "specimen":
            require(current is None, "unterminated specimen")
            current = {"name": items[1], "chi": tuple(map(int, items[2:])),
                       "lengths": [], "states": [], "adj": [], "coin": [], "zero": []}
        elif tag == "radii":
            current["radii"] = tuple(map(int, items[1:]))
        elif tag == "length":
            require(int(items[1]) == len(current["lengths"]), "length index drift")
            current["lengths"].append(tuple(map(int, items[2:])))
        elif tag == "vertex":
            v, top, bottom, a0, a1, a2, coin, zero, *adj = map(int, items[1:])
            require(v == len(current["states"]), "vertex index drift")
            current["states"].append((top, bottom, (a0, a1, a2)))
            current["adj"].append(adj)
            current["coin"].append(coin)
            current["zero"].append(zero)
        elif tag == "end":
            require(int(items[1]) == len(current["states"]), "vertex count drift")
            yield current
            current = None
        else:
            raise RuntimeError(f"unknown export line: {tag}")
    require(current is None, "truncated export")


def replay(g):
    images = SPECIMENS[g["name"]]
    sigma = {a + 1: tuple(x + 1 for x in image) for a, image in enumerate(images)}
    T, U, D = charpoly(sigma)
    require(g["chi"] == (-D, U, -T), "independent incidence polynomial differs")
    F = Field(T, U, D)
    lengths = g["lengths"]
    normalized = left_perron_lengths(sigma, F)
    require(all(F.mul(lengths[0], normalized[a]) == lengths[a] for a in range(3)),
            "independent left Perron vector differs")

    signs = {}

    def sign(x):
        if x not in signs:
            signs[x] = F.sign(x)
        return signs[x]

    def overlap(state):
        i, j, t = state
        return sign(F.add(t, lengths[j])) > 0 and sign(F.sub(t, lengths[i])) < 0

    def coincidence(state):
        return state[0] == state[1] and not any(state[2])

    prefixes = []
    for a, image in enumerate(images):
        p = []
        t = F.zero
        for child in image:
            p.append(t)
            t = F.add(t, lengths[child])
        require(t == F.mul(F.beta, lengths[a]), "prefix scaling failure")
        prefixes.append(p)

    states, adj = g["states"], g["adj"]
    index = {state: v for v, state in enumerate(states)}
    n = len(states)
    require(len(index) == n, "duplicate state")
    for v, state in enumerate(states):
        require(overlap(state), f"invalid overlap {v}")
        expected = []
        if not coincidence(state):
            i, j, t = state
            bt = F.mul(F.beta, t)
            for p, a in enumerate(images[i]):
                for q, b in enumerate(images[j]):
                    child = (a, b, F.sub(F.add(bt, prefixes[j][q]), prefixes[i][p]))
                    if overlap(child):
                        require(child in index, f"missing child of {v}")
                        expected.append(index[child])
            require(bool(expected), f"noncoincidence sink {v}")
        require(sorted(expected) == sorted(adj[v]), f"edge multiset differs at {v}")

    # Independently enumerate the complete projected start set. Divide the
    # slab inequalities by a positive tile length, enclose the two algebraic
    # endpoints with rational intervals, then filter every candidate exactly.
    radii = g["radii"]
    z = max(range(3), key=lambda a: radii[a])
    x, y = [a for a in range(3) if a != z]
    longest = lengths[0]
    for l in lengths[1:]:
        if sign(F.sub(l, longest)) > 0:
            longest = l
    inv_lz = F.inv(lengths[z])

    def interval(a):
        lo, hi = F.lo, F.hi
        return (a[0] + min(a[1] * lo, a[1] * hi) + min(a[2] * lo * lo, a[2] * hi * hi),
                a[0] + max(a[1] * lo, a[1] * hi) + max(a[2] * lo * lo, a[2] * hi * hi))

    seeds = set()
    for wx in range(-radii[x], radii[x] + 1):
        for wy in range(-radii[y], radii[y] + 1):
            base = F.add(tuple(wx * c for c in lengths[x]), tuple(wy * c for c in lengths[y]))
            lower = F.mul(F.sub(F.sub(F.zero, longest), base), inv_lz)
            upper = F.mul(F.sub(longest, base), inv_lz)
            lo = interval(lower)[0]
            hi = interval(upper)[1]
            for wz in range(lo.numerator // lo.denominator - 1, hi.numerator // hi.denominator + 2):
                t = F.add(base, tuple(wz * c for c in lengths[z]))
                if sign(F.add(t, longest)) <= 0 or sign(F.sub(t, longest)) >= 0:
                    continue
                for i in range(3):
                    for j in range(3):
                        state = (i, j, t)
                        if overlap(state):
                            require(state in index, "missing start-set overlap")
                            seeds.add(index[state])
    reached = set(seeds)
    queue = deque(seeds)
    while queue:
        for child in adj[queue.popleft()]:
            if child not in reached:
                reached.add(child)
                queue.append(child)
    require(len(reached) == n, "export contains vertices outside start closure")

    parents = [[] for _ in states]
    for v, children in enumerate(adj):
        for child in children:
            parents[child].append(v)

    def depths(target):
        dist = [-1] * n
        queue = deque()
        for v, state in enumerate(states):
            if target(state):
                dist[v] = 0
                queue.append(v)
        while queue:
            child = queue.popleft()
            for parent in parents[child]:
                if dist[parent] < 0:
                    dist[parent] = dist[child] + 1
                    queue.append(parent)
        return dist

    coin = depths(coincidence)
    zero = depths(lambda state: not any(state[2]))
    require(coin == g["coin"] and zero == g["zero"], "independent shortest depths differ")
    require(all(d >= 0 for d in coin), "nonproductive exported vertex")
    components = sccs(SimpleNamespace(states=states, adj=adj, capped=False))
    recurrent = [v for comp in components if len(comp) > 1 or comp[0] in adj[comp[0]] for v in comp]
    # Offset coefficients -> integral length coordinates, by rational inversion.
    inverse = _inverse([[lengths[a][r] for a in range(3)] for r in range(3)])
    max_w = [0, 0, 0]
    for v in recurrent:
        t = states[v][2]
        for a in range(3):
            w = sum(inverse[a][r] * t[r] for r in range(3))
            require(w.denominator == 1, "nonintegral recurrent offset")
            require(abs(w) <= radii[a], "cycle offset outside certified coordinate box")
            max_w[a] = max(max_w[a], abs(w.numerator))
    aligned = [coin[v] for v, state in enumerate(states) if not any(state[2]) and not coincidence(state)]
    require(len(aligned) == 6, "aligned-pair coverage differs")
    return {"specimen": g["name"], "states": n, "edges": sum(map(len, adj)),
            "starts": len(seeds), "recurrent": len(recurrent), "productive": True,
            "D": max(coin), "S": max(aligned), "K_V": max((zero[v] for v in recurrent), default=-1),
            "radii": radii, "max_abs_cycle_w": max_w, "det_M": D,
            "checks": ["all-overlaps", "all-child-multisets", "start-coverage", "closure",
                       "all-shortest-depths", "cycle-containment", "six-aligned-pairs"]}


def main():
    path = Path(sys.argv[1])
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    names = []
    for g in exported(path):
        require(g["name"] not in names, "duplicate specimen")
        names.append(g["name"])
        result = replay(g)
        result["export_sha256"] = digest
        print(json.dumps(result, sort_keys=True), flush=True)
    require(set(names) == set(SPECIMENS), "missing specimen export")


if __name__ == "__main__":
    main()
