"""Independent Python oracle for the formal-overlap carrier census.

A potential overlap is a state (i, j, t) of ``overlap_graph.OverlapGraph``
with t = sum_a w_a l_a, w in Z^3, not required to be reachable from a seed.
The formal graph closes every potential overlap of a box |w_a| <= R_a under
inflation; a carrier is a recurrent SCC of it with coincidences deleted.

Every recurrent state satisfies |t(z)| <= max_c |c(z)| / (1 - |z|) for each
contracting conjugate z (c ranging over prefix-position differences) and
|t(beta)| < l_max, so a box covering that region contains every carrier.
The box is chosen in floating point with its own slack, independently of the
canonical kernel; carriers do not depend on the box once it covers the
region, so agreement with a differently sized canonical box is a check of
that independence. Seeds are further restricted to the forward-closed region
|t(z)| <= T_z (1 + eps), again with a tolerance of its own. Every predicate is exact over Q(beta).

Canonical implementation: mojo/psc/formal_overlap.mojo.
"""
from __future__ import annotations

import cmath
import itertools
import math
from collections import deque
from dataclasses import dataclass
from typing import Mapping, Sequence

from psc_research.overlap_graph import Elt, OverlapGraph

IMPLEMENTATION_ROLE = "independent-oracle"
CANONICAL_IMPLEMENTATION = "mojo/psc/formal_overlap.mojo"

BOX_SLACK = 1.25
REGION_TOLERANCE = 1e-5


def _roots(T: int, U: int, D: int) -> list[complex]:
    """Roots of x^3 - T x^2 + U x - D by Durand--Kerner iteration."""
    f = lambda x: ((x - T) * x + U) * x - D
    zs = [complex(0.4, 0.9) ** k for k in range(3)]
    for _ in range(500):
        zs = [z - f(z) / math.prod(z - w for w in zs if w is not z) for z in zs]
    return zs


def _at(x: Elt, z: complex) -> complex:
    return float(x[0]) + float(x[1]) * z + float(x[2]) * z * z


def _box_bounds(m: list[list[float]], b: list[float]) -> list[float]:
    """`sum_k |inv(m)[a][k]| b_k` per coordinate `a`, the inverse by Cramer's rule."""
    det = lambda a: (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
                     - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
                     + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0]))
    d = det(m)
    out = []
    for a in range(3):
        total = 0.0
        for k in range(3):
            col = [[(float(r == k) if c == a else m[r][c]) for c in range(3)] for r in range(3)]
            total += abs(det(col) / d) * b[k]
        out.append(total)
    return out


class FormalGraph(OverlapGraph):
    """The inflation closure of every potential overlap in a covering box."""

    def __init__(self, sigma: Mapping[int, Sequence[int]], slack: float = BOX_SLACK, max_states: int = 400000):
        self.slack = slack
        super().__init__(sigma, max_states=max_states)

    def box(self) -> list[int]:
        F = self.F
        zs = _roots(F.T, F.U, F.D)
        beta = max(zs, key=lambda z: z.real if abs(z.imag) < 1e-9 else -math.inf).real
        contracting = [z for z in zs if abs(z - beta) > 1e-9 and z.imag >= -1e-12]
        digits = {F.sub(self.prefix[(j, b)], self.prefix[(i, a)])
                  for i in (1, 2, 3) for j in (1, 2, 3)
                  for a in range(len(self.sigma[i])) for b in range(len(self.sigma[j]))}
        rows = [[_at(l, beta).real for l in self.l]]
        bounds = [max(_at(l, beta).real for l in self.l)]
        self.region = []
        for z in contracting:
            assert abs(z) < 1, "formal box requires contracting conjugates"
            threshold = max(abs(_at(d, z)) for d in digits) / (1 - abs(z))
            self.region.append((z, threshold * (1 + REGION_TOLERANCE)))
            rows.append([_at(l, z).real for l in self.l]); bounds.append(threshold)
            if abs(z.imag) > 1e-9:
                rows.append([_at(l, z).imag for l in self.l]); bounds.append(threshold)
        assert len(rows) == 3
        return [math.ceil(self.slack * r) + 1 for r in _box_bounds(rows, bounds)]

    def seeds(self) -> list[tuple[int, int, Elt]]:
        F = self.F
        self.box_radii = self.box()
        out = []
        for w in itertools.product(*(range(-r, r + 1) for r in self.box_radii)):
            t = F.zero
            for a in range(3):
                t = F.add(t, tuple(w[a] * c for c in self.l[a]))
            if any(abs(_at(t, z)) > bound for z, bound in self.region):
                continue
            out.extend(s for s in ((i, j, t) for i in (1, 2, 3) for j in (1, 2, 3)) if self.overlaps(s))
        self.seed_set = set(out)
        return out


def _sccs(adj: list[list[int]]) -> list[list[int]]:
    """Kosaraju: forward finishing order, then the reversed graph."""
    n = len(adj)
    seen, order = [False] * n, []
    for root in range(n):
        if seen[root]:
            continue
        seen[root] = True
        stack = [(root, iter(adj[root]))]
        while stack:
            v, it = stack[-1]
            w = next(it, None)
            if w is None:
                stack.pop(); order.append(v)
            elif not seen[w]:
                seen[w] = True; stack.append((w, iter(adj[w])))
    radj = [[] for _ in range(n)]
    for v in range(n):
        for w in adj[v]:
            radj[w].append(v)
    comp = [-1] * n
    out = []
    for root in reversed(order):
        if comp[root] >= 0:
            continue
        comp[root] = len(out); members = [root]; queue = [root]
        while queue:
            v = queue.pop()
            for u in radj[v]:
                if comp[u] < 0:
                    comp[u] = comp[root]; members.append(u); queue.append(u)
        out.append(members)
    return out


def _death_depths(g: OverlapGraph) -> list[int]:
    radj = [[] for _ in g.states]
    for v, ws in enumerate(g.adj):
        for w in ws:
            radj[w].append(v)
    depth = [0 if g.is_coincidence(s) else -1 for s in g.states]
    queue = deque(v for v, d in enumerate(depth) if d == 0)
    while queue:
        v = queue.popleft()
        for u in radj[v]:
            if depth[u] < 0:
                depth[u] = depth[v] + 1; queue.append(u)
    return depth


@dataclass(frozen=True)
class Carrier:
    size: int
    cyclomatic: int
    realized: bool
    closed: bool
    aligned: bool
    direct: bool
    death: int


def carriers(sigma: Mapping[int, Sequence[int]], slack: float = BOX_SLACK) -> tuple[list[Carrier], int]:
    """The formal carriers of sigma, sorted, and the formal nonproductive-state count."""
    f = FormalGraph(sigma, slack)
    r = OverlapGraph(sigma)
    if f.capped or r.capped:
        raise RuntimeError("capped graph: no verdict")
    coin = [f.is_coincidence(s) for s in f.states]
    free = [[] if coin[v] else [w for w in f.adj[v] if not coin[w]] for v in range(len(f.states))]
    depth = _death_depths(f)
    realized = set(r.states)
    out = []
    for comp in _sccs(free):
        members = set(comp)
        if len(comp) == 1 and comp[0] not in free[comp[0]]:
            continue
        assert members <= {f.index[s] for s in f.seed_set}, "carrier outside the box"
        real = {f.states[v] in realized for v in comp}
        assert len(real) == 1, "carrier partly realized"
        exits = [w for v in comp for w in f.adj[v] if w not in members]
        out.append(Carrier(
            size=len(comp),
            cyclomatic=sum(1 for v in comp for w in f.adj[v] if w in members) - len(comp) + 1,
            realized=real.pop(),
            closed=not exits,
            aligned=any(not any(f.states[v][2]) for v in comp),
            direct=any(coin[w] for w in exits),
            death=min(depth[v] for v in comp),
        ))
    return sorted(out, key=lambda c: tuple(vars(c).values())), sum(1 for d in depth if d < 0)
