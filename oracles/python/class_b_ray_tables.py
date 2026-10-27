"""Generate kernel/psc/class_b_ray_tables.mojo: class-B ray carriers and potentials.

A proof *target*, not evidence. Carriers are copied from the finite label-ray
packet (evidence/class-b-label-rays-2026-10-23/carriers.json). Each ray's
potential constants b(top, bottom, u, d, sign k), with X = |k| + b, are the
least fixed point of

    b[P] = max over non-target labels v in P of (1 + min_child X(child) - |k_v|),

iterated from b = 0 on two complete seed graphs of the ray (q = q0 + 2g and
q0 + 3g). The graphs are rebuilt here in floating point; only the Mojo
certificate psc.class_b_ray_certificate (and its Python twin
oracles/python/class_b_ray_certificate.py) decides anything.

    python oracles/python/class_b_ray_tables.py            # write
    python oracles/python/class_b_ray_tables.py --check    # refuse on drift
"""
import collections
import json
import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CARRIERS = ROOT / "evidence/class-b-label-rays-2026-10-23/carriers.json"
OUT = ROOT / "kernel/psc/class_b_ray_tables.mojo"
# The fitted floors of carriers.json, except minus g=3, whose closure first
# decides at the floors below (affine comparisons refuse below them).
FLOORS = {(-1, 3, 0): 21, (-1, 3, 1): 22, (-1, 3, 2): 20}


class Graph:
    """Complete canonical swap-seed overlap graph, floating-point strictness."""

    def __init__(self, eps, g, q):
        r = q + eps
        p = 3 * q + 6 + 6 * eps - g
        self.runs = [p, q, r]
        self.m = [[2, 1, 1], [0, 1, 1], [p, q, r]]
        lo, hi = float(q + 1), float(q + 7)
        chi = lambda t: (t - 2) * (t - 1) * (t - r) - q * (t - 2) - p * t
        for _ in range(200):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if chi(mid) < 0 else (lo, mid)
        b = (lo + hi) / 2
        self.lengths = [3 * b * b + (3 + 3 * eps - g) * b + 3 * eps, (b + 1) * (b - eps), b * b + b]
        self.tol = 1e-7 * self.lengths[0]
        first = [0, 1, 1]
        self.segments = []
        for t in range(3):
            px = 1 if t == 0 else 0
            m = self.runs[t]
            self.segments.append([(first[t], 0, 0, 0, 0), (2, px, 1 - px, 0, m - 1), (0, px, 1 - px, m, m)])

    def disp(self, w):
        return sum(a * b for a, b in zip(self.lengths, w))

    def strict(self, top, bottom, w):
        t = self.disp(w)
        return min(self.lengths[top] - t, t + self.lengths[bottom]) > self.tol

    def children(self, v):
        top, bottom, w = v
        if top == bottom and w == (0, 0, 0):
            return []
        mw = [sum(self.m[i][j] * w[j] for j in range(3)) for i in range(3)]
        out = set()
        for ct, px1, pc1, lo1, hi1 in self.segments[top]:
            for cb, px2, pc2, lo2, hi2 in self.segments[bottom]:
                base = (mw[0] + px2 - px1, mw[1] + pc2 - pc1, mw[2])
                t0, ly = self.disp(base), self.lengths[2]
                dlo = max(lo2 - hi1, math.floor((-self.lengths[cb] - t0) / ly) - 1)
                dhi = min(hi2 - lo1, math.ceil((self.lengths[ct] - t0) / ly) + 1)
                for dy in range(dlo, dhi + 1):
                    nw = (base[0], base[1], base[2] + dy)
                    if self.strict(ct, cb, nw):
                        out.add((ct, cb, nw))
        return sorted(out)

    def build(self):
        seeds = []
        for a in range(3):
            for b in range(a + 1, 3):
                for which in range(4):
                    top, bottom = (a if which < 2 else b), (b if which % 2 == 0 else a)
                    w = [0, 0, 0]
                    if which in (1, 3):
                        w[b] += 1
                    if which in (2, 3):
                        w[a] -= 1
                    if self.strict(top, bottom, w):
                        seeds.append((top, bottom, tuple(w)))
        self.edges = {s: None for s in seeds}
        stack = list(seeds)
        while stack:
            v = stack.pop()
            self.edges[v] = self.children(v)
            for c in self.edges[v]:
                if c not in self.edges:
                    self.edges[c] = None
                    stack.append(c)
        return self


def key(v):
    top, bottom, (k, c, y) = v
    return (top, bottom, 3 * k + c + y, c - 3 * k, (k > 0) - (k < 0))


def potentials(graphs):
    b = collections.defaultdict(int)
    for _ in range(1000):
        changed = False
        for g in graphs:
            for v, cs in sorted(g.edges.items()):
                if v[2] == (0, 0, 0):
                    continue
                need = 1 + min(abs(c[2][0]) + b[key(c)] for c in cs) - abs(v[2][0])
                if need > b[key(v)]:
                    b[key(v)] = need
                    changed = True
        if not changed:
            for g in graphs:
                for v in g.edges:
                    b.setdefault(key(v), 0)
            return sorted(b.items())
    raise SystemExit("potential iteration did not converge")


def rays():
    out = []
    for entry in json.loads(CARRIERS.read_text()):
        eps = 1 if entry["branch"] == "plus" else -1
        g, r = entry["gap"], entry["residue"]
        q0 = FLOORS.get((eps, g, r), entry["floor"])
        graphs = [Graph(eps, g, q0 + i * g).build() for i in (2, 3)]
        out.append((eps, g, r, q0, entry["slope"], entry["carrier"], potentials(graphs)))
    return out


def flat(rows):
    return " ".join(" ".join(str(x) for x in row) for row in rows)


def render():
    specs, bodies = [], []
    for i, (eps, g, r, q0, slope, carrier, pot) in enumerate(rays()):
        specs.append(f"        List[Int]([{eps}, {g}, {r}, {q0}, {slope}, {len(carrier)}, {len(pot)}]),")
        bodies.append(f'comptime ROWS_{i} = "{flat(carrier)}"\n'
                      f'comptime POT_{i} = "{flat([list(k) + [v] for k, v in pot])}"\n')
    cases_rows = "\n".join(f"    if i == {i}:\n        return _parse(ROWS_{i}, 8)" for i in range(len(specs)))
    cases_pot = "\n".join(f"    if i == {i}:\n        return _parse(POT_{i}, 6)" for i in range(len(specs)))
    return f'''"""Class-B top-layer residue-ray carriers and potentials (generated; do not edit).

Generated by `oracles/python/class_b_ray_tables.py` from
evidence/class-b-label-rays-2026-10-23/carriers.json. A proof *target*: evidence
only through `psc.class_b_ray_certificate.certify_ray_rows`.
Carrier rows `top bottom u d lo_a lo_b hi_a hi_b` (`a l + b <= k`, `q = g l + r`);
potential rows `top bottom u d sign(k) b` (`X = |k| + b`).
Source note: docs/class-b-ray-certificate-2026-10-27.md.
"""


def ray_specs() -> List[List[Int]]:
    """`[eps, g, r, floor q0, labels per l-step, carrier rows, potential rows]`."""
    return List[List[Int]]([
{chr(10).join(specs)}
    ])


{chr(10).join(bodies)}

def _parse(text: String, width: Int) raises -> List[List[Int]]:
    var out = List[List[Int]]()
    var row = List[Int]()
    for tok in text.split(" "):
        row.append(Int(String(tok)))
        if len(row) == width:
            out.append(row^)
            row = List[Int]()
    if len(row) != 0:
        raise Error("class-B ray table is not a whole number of rows")
    return out^


def ray_rows(i: Int) raises -> List[List[Int]]:
{cases_rows}
    raise Error("no class-B ray table with this index")


def ray_potentials(i: Int) raises -> List[List[Int]]:
{cases_pot}
    raise Error("no class-B ray table with this index")
'''


def main():
    text = render()
    if "--check" in sys.argv:
        if OUT.read_text() != text:
            raise SystemExit(f"{OUT} differs from its generator")
        print("class-B ray tables up to date")
        return
    OUT.write_text(text)
    print("wrote", OUT)


if __name__ == "__main__":
    main()
