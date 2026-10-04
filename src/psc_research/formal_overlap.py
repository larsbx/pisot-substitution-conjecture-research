"""Independent Python oracle for the formal-overlap carrier census.

A potential overlap is a state (i, j, t) of ``overlap_graph.OverlapGraph``
with t = sum_a w_a l_a, w in Z^3, not required to be reachable from a seed.
The formal graph closes the potential overlaps of a contraction region under
inflation; a carrier is a recurrent SCC of it with coincidences deleted.

With q(t) the sum of |sigma_k(t)|^2 over the two contracting embeddings and
rho the largest contracting modulus, the region q(t) <= T^2 is forward closed
and contains every cycle once T >= max_c sqrt q(c) / (1 - rho). This oracle
bounds the digits by the triangle inequality, q(c) <= 2 (sum_i |c_i| rho^i)^2,
a looser bound than the canonical kernel's; carriers do not depend on T once
the region covers every cycle, so agreement is also a check of that. Every
quantity is an exact rational: rho from Sturm bisection, T rounded up to a
multiple of 1/64, membership as an exact sign in Q(beta), and the w-box from
the trace-dual basis by Cauchy--Schwarz.

Canonical implementation: mojo/psc/formal_overlap.mojo.
"""
from __future__ import annotations

import itertools
import math
from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from typing import Mapping, Sequence

from psc_research.overlap_graph import Elt, OverlapGraph
from psc_research.pip_screen import _changes, _sturm

IMPLEMENTATION_ROLE = "independent-oracle"
CANONICAL_IMPLEMENTATION = "mojo/psc/formal_overlap.mojo"

DENOMINATOR = 64


def _ceil(x: Fraction) -> int:
    return -((-x.numerator) // x.denominator)


def _ceil_sqrt(x: Fraction) -> int:
    """The least integer n >= 0 with n^2 >= x."""
    n = math.isqrt(max(_ceil(x), 0))
    return n if n * n >= x else n + 1


class FormalGraph(OverlapGraph):
    """The inflation closure of every genuine potential overlap of the region."""

    def __init__(self, sigma: Mapping[int, Sequence[int]], max_states: int = 400000):
        super().__init__(sigma, max_states=max_states)

    # -- exact field quantities -------------------------------------------
    def _trace(self, x: Elt) -> Fraction:
        T, U = self.F.T, self.F.U
        return 3 * x[0] + T * x[1] + (T * T - 2 * U) * x[2]

    def _norm(self, x: Elt) -> Fraction:
        F = self.F
        cols = [x, F.mul(F.beta, x), F.mul(F.beta, F.mul(F.beta, x))]
        m = [[cols[c][r] for c in range(3)] for r in range(3)]
        return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
                - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
                + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))

    def _beta_box(self, width: Fraction = Fraction(1, 2 ** 40)) -> tuple[Fraction, Fraction]:
        F = self.F
        lo, hi = F.lo, F.hi
        while hi - lo > width:
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if F.f(mid) < 0 else (lo, mid)
        return lo, hi

    def _abs_upper(self, x: Elt) -> Fraction:
        lo, hi = self.beta
        return abs(x[0]) + abs(x[1]) * hi + abs(x[2]) * hi * hi

    def _q(self, x: Elt) -> Elt:
        """q(x) as an element of Q(beta)."""
        F = self.F
        if not any(x):
            return F.zero
        if self.complex_pair:
            n = self._norm(x)
            return F.mul((2 * n, Fraction(0), Fraction(0)), F.inv(x))
        x2 = F.mul(x, x)
        return F.sub((self._trace(x2), Fraction(0), Fraction(0)), x2)

    def _rho_upper(self) -> Fraction:
        F = self.F
        if self.complex_pair:
            rho2 = abs(Fraction(F.D)) / self.beta[0]
        else:
            chain = _sturm([Fraction(-F.D), Fraction(F.U), Fraction(-F.T), Fraction(1)])
            count = lambda a, b: _changes(chain, a) - _changes(chain, b)
            boxes, rho2 = [(Fraction(-1), Fraction(1))], Fraction(0)
            assert count(Fraction(-1), Fraction(1)) == 2, "two contracting real roots expected"
            while boxes:
                a, b = boxes.pop()
                n = count(a, b)
                if n == 0:
                    continue
                if n == 1 and max(a * a, b * b) < 1:
                    rho2 = max(rho2, a * a, b * b)
                    continue
                m = (a + b) / 2
                assert F.f(m) != 0
                boxes += [(a, m), (m, b)]
        k = _ceil_sqrt(rho2 * 2 ** 40)
        assert k < 2 ** 20, "contracting modulus bound is not below one"
        return Fraction(k, 2 ** 20)

    def region(self) -> None:
        F = self.F
        T, U, D = F.T, F.U, F.D
        b, c, d = -T, U, -D
        self.complex_pair = 18 * b * c * d - 4 * b ** 3 * d + b * b * c * c - 4 * c ** 3 - 27 * d * d < 0
        self.beta = self._beta_box()
        rho = self._rho_upper()
        digits = {F.sub(self.prefix[(j, y)], self.prefix[(i, x)])
                  for i in (1, 2, 3) for j in (1, 2, 3)
                  for x in range(len(self.sigma[i])) for y in range(len(self.sigma[j]))}
        dmax = max(abs(e[0]) + abs(e[1]) * rho + abs(e[2]) * rho * rho for e in digits)
        self.a = _ceil_sqrt(2 * dmax * dmax * DENOMINATOR ** 2 / (1 - rho) ** 2)
        self.t2 = Fraction(self.a * self.a, DENOMINATOR ** 2)
        gram = [[self._trace(F.mul(li, lj)) for lj in self.l] for li in self.l]
        inv = _inverse(gram)
        lmax = max(self._abs_upper(l) for l in self.l)
        self.radii = []
        for a in range(3):
            dual = F.zero
            for k in range(3):
                dual = F.add(dual, tuple(inv[a][k] * e for e in self.l[k]))
            q_dual = 2 * (abs(dual[0]) + abs(dual[1]) * rho + abs(dual[2]) * rho * rho) ** 2
            self.radii.append(_ceil(lmax * self._abs_upper(dual)) + _ceil_sqrt(self.t2 * q_dual) + 1)

    def in_region(self, t: Elt) -> bool:
        F = self.F
        return F.sign(F.sub((self.t2, Fraction(0), Fraction(0)), self._q(t))) >= 0

    def seeds(self) -> list[tuple[int, int, Elt]]:
        F = self.F
        self.region()
        out = []
        for w in itertools.product(*(range(-r, r + 1) for r in self.radii)):
            t = F.zero
            for a in range(3):
                t = F.add(t, tuple(w[a] * c for c in self.l[a]))
            genuine = [s for s in ((i, j, t) for i in (1, 2, 3) for j in (1, 2, 3)) if self.overlaps(s)]
            if genuine and self.in_region(t):
                out += genuine
        self.seed_set = set(out)
        return out


def _inverse(m: list[list[Fraction]]) -> list[list[Fraction]]:
    """Gauss--Jordan inverse of a 3x3 rational matrix."""
    a = [[Fraction(x) for x in row] + [Fraction(int(i == j)) for j in range(3)] for i, row in enumerate(m)]
    for c in range(3):
        p = next(r for r in range(c, 3) if a[r][c] != 0)
        a[c], a[p] = a[p], a[c]
        a[c] = [x / a[c][c] for x in a[c]]
        for r in range(3):
            if r != c and a[r][c] != 0:
                a[r] = [x - a[r][c] * y for x, y in zip(a[r], a[c])]
    return [row[3:] for row in a]


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


def carriers(sigma: Mapping[int, Sequence[int]]) -> tuple[list[Carrier], int]:
    """The formal carriers of sigma, sorted, and the formal nonproductive-state count."""
    f = FormalGraph(sigma)
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
