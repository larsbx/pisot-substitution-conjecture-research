"""Bounded synthesis prototype for a class-B piecewise rank. Never a verdict.

Searches, on native `edges` exports of one residue ray over a training window,
for a certificate in the format checked by kernel/class_b_rank_certificate.mojo.
Its output is accepted only by that exact checker and by the independent oracle;
floating LP/MILP solutions (scipy/HiGHS) only propose candidates.

1. Pieces: maximal typed k-intervals (target intervals split at k=0), endpoints
   exactly affine in q on the window.
2. Symbolic edges (P -> Q, dx): actual edges grouped by parent piece, child piece
   and dx = k' - s + k; parent sets must be contiguous with affine endpoints.
3. Segments: each piece is cut at every edge-domain endpoint (cut order must be
   stable for all q >= floor); one affine potential per segment.
4. Policy: per segment, an edge whose child has smaller first-hit depth at every
   training point, fixed first; the rest are then chosen greedily while the LP
   stays feasible.
   Each chosen edge is split along the child's segments (sub-edges).
5. Integer potentials for the fixed policy by MILP, coefficients within BOUND.
Refusals (unstable cut order, a segment empty at the floor, no uniform or
LP-feasible option) are reported, not hidden.
"""
import collections
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp
from scipy.sparse import coo_matrix

BOUND = 60


def typ(v):
    t, b, k, c, y = v
    return (t, b, 3*k + c + y, c - 3*k)


def label(T, k):
    return (T[0], T[1], k, 3*k + T[3], T[2] - 6*k - T[3])


def le_always(f, g):
    """f(q) <= g(q) for all q >= floor; f, g = (slope, value at floor)."""
    return f[1] <= g[1] and f[0] <= g[0]


def load(path):
    V, E = {}, []
    for line in Path(path).read_text().splitlines():
        p = line.split()
        if p[0] == 'V':
            V[tuple(map(int, p[1:6]))] = int(p[6])
        elif p[0] == 'E':
            x = tuple(map(int, p[1:]))
            E.append((x[:5], x[5:]))
    return V, E


def pieces_of(labels):
    groups = collections.defaultdict(set)
    for v in labels:
        groups[typ(v)].add(v[2])
    out = []
    for T, ks in sorted(groups.items()):
        ks = sorted(ks)
        start = ks[0]
        for a, b in zip(ks, ks[1:] + [None]):
            if b == a + 1:
                continue
            runs = [(start, -1), (0, 0), (1, a)] if T[2:] == (0, 0) and start <= 0 <= a else [(start, a)]
            out += [(T, lo, hi) for lo, hi in runs if lo <= hi]
            start = b
    return out


class Synthesis:
    def __init__(self, directory, branch, gap, q0, q1):
        self.branch, self.gap, self.q0 = branch, gap, q0
        self.qs = range(q0, q1 + 1, gap)
        self.graphs = {q: load(Path(directory) / f'{branch}-g{gap}-q{q}.edges') for q in self.qs}
        self._pieces()
        self._edges()
        self._segments()

    def at(self, f, q):
        return f[1] + f[0]*(q - self.q0) // self.gap

    def affine(self, vals):
        q0, q1 = self.qs[0], self.qs[1]
        f = (vals[q1] - vals[q0], vals[q0])
        if any(self.at(f, q) != v for q, v in vals.items()):
            raise ValueError('REFUSED: endpoint not affine on the window')
        return f

    def _pieces(self):
        per_q = {q: pieces_of(V) for q, (V, _) in self.graphs.items()}
        first = per_q[self.q0]
        if any([p[0] for p in rows] != [p[0] for p in first] for rows in per_q.values()):
            raise ValueError('REFUSED: piece topology changes on the window')
        self.pieces = [dict(T=T, lo=self.affine({q: per_q[q][i][1] for q in self.qs}),
                            hi=self.affine({q: per_q[q][i][2] for q in self.qs}))
                       for i, (T, _, _) in enumerate(first)]
        self.target = {i for i, p in enumerate(self.pieces) if p['T'][2:] == (0, 0) and p['lo'] == p['hi'] == (0, 0)}
        self.pid = {}
        for q in self.qs:
            for i, p in enumerate(self.pieces):
                for k in range(self.at(p['lo'], q), self.at(p['hi'], q) + 1):
                    self.pid[q, p['T'], k] = i

    def _edges(self):
        dom = collections.defaultdict(lambda: collections.defaultdict(set))
        for q, (_, E) in self.graphs.items():
            for a, b in E:
                i, j = self.pid[q, typ(a), a[2]], self.pid[q, typ(b), b[2]]
                dom[i, j, b[2] - typ(a)[2] + a[2]][q].add(a[2])
        self.edges = []
        for (i, j, dx), byq in sorted(dom.items()):
            if i in self.target or set(byq) != set(self.qs):
                continue
            if any(len(ks) != max(ks) - min(ks) + 1 for ks in byq.values()):
                continue
            try:
                lo, hi = self.affine({q: min(ks) for q, ks in byq.items()}), self.affine({q: max(ks) for q, ks in byq.items()})
            except ValueError:
                continue
            self.edges.append(dict(P=i, Q=j, dx=dx, lo=lo, hi=hi))

    def _segments(self):
        self.segs, self.seg_of = [], {}
        for i, p in enumerate(self.pieces):
            top = (p['hi'][0], p['hi'][1] + 1)
            cuts = {p['lo'], top} | {f for e in self.edges if e['P'] == i for f in (e['lo'], (e['hi'][0], e['hi'][1] + 1))}
            cuts = sorted(cuts, key=lambda f: (f[1], f[0]))
            if not all(le_always(f, g) for f, g in zip(cuts, cuts[1:])):
                raise ValueError('REFUSED: unstable cut order')
            self.seg_of[i] = []
            for f, g in zip(cuts, cuts[1:]):
                if le_always(p['lo'], f) and le_always(g, top):
                    if f[1] >= g[1]:
                        raise ValueError('REFUSED: a segment is empty at the floor; raise the floor')
                    self.seg_of[i].append(len(self.segs))
                    self.segs.append(dict(P=i, T=p['T'], lo=f, hi=(g[0], g[1] - 1), target=i in self.target))

    def subedges(self, j, e):
        """Edge e restricted to segment j, split along the child's segments; None if not uniform."""
        S, E_ = self.segs[j], self.edges[e]
        base, out = S['T'][2] + E_['dx'], []
        for cj in self.seg_of[E_['Q']]:
            C = self.segs[cj]
            los = [S['lo'], (-C['hi'][0], base - C['hi'][1])]
            his = [S['hi'], (-C['lo'][0], base - C['lo'][1])]
            lo, hi = max(los, key=lambda f: (f[1], f[0])), min(his, key=lambda f: (f[1], f[0]))
            if not any(self.at(lo, q) <= self.at(hi, q) for q in self.qs):
                continue
            if not (all(le_always(f, lo) for f in los) and all(le_always(hi, f) for f in his) and le_always(lo, hi)):
                return None
            out.append(dict(S=j, C=cj, dx=E_['dx'], lo=lo, hi=hi))
        return out

    def options(self, j):
        """Uniform options for segment j, most depth-decreasing training points first."""
        S, out = self.segs[j], []
        for e, E_ in enumerate(self.edges):
            if E_['P'] != S['P'] or not (le_always(E_['lo'], S['lo']) and le_always(S['hi'], E_['hi'])):
                continue
            se = self.subedges(j, e)
            if not se:
                continue
            CT = self.pieces[E_['Q']]['T']
            pts = [(self.graphs[q][0][label(S['T'], k)], self.graphs[q][0][label(CT, S['T'][2] + E_['dx'] - k)])
                   for q in self.qs for k in range(self.at(S['lo'], q), self.at(S['hi'], q) + 1)]
            good = sum(1 for dp, dc in pts if dc < dp)
            out.append((good == len(pts), good, -e, se))
        out.sort(key=lambda t: t[:3], reverse=True)
        return bool(out) and out[0][0], [se for *_, se in out]

    def rows(self, sub):
        """Linear constraints (coefficients, rhs), meaning sum >= rhs; variables 3*segment + (a,b,c)."""
        def X(j, k):
            return {3*j: self.q0, 3*j + 1: k, 3*j + 2: 1}
        out = []
        if sub is None:
            for j, S in enumerate(self.segs):
                for sl, v0 in (S['lo'], S['hi']):
                    out += [(X(j, v0), 0), ({3*j: self.gap, 3*j + 1: sl}, 0)]
            return out
        base = self.segs[sub['S']]['T'][2] + sub['dx']
        for sl, v0 in (sub['lo'], sub['hi']):
            f = X(sub['S'], v0)
            for key, v in X(sub['C'], base - v0).items():
                f[key] = f.get(key, 0) - v
            r = {3*sub['S']: self.gap, 3*sub['S'] + 1: sl}
            r[3*sub['C']] = r.get(3*sub['C'], 0) - self.gap
            r[3*sub['C'] + 1] = r.get(3*sub['C'] + 1, 0) + sl
            out += [(f, 1), (r, 0)]
        return out

    def matrix(self, rows):
        I, J, V = zip(*[(r, key, v) for r, (d, _) in enumerate(rows) for key, v in d.items() if v])
        return coo_matrix((V, (I, J)), shape=(len(rows), 3*len(self.segs))).tocsr(), np.array([rhs for _, rhs in rows])

    def feasible(self, rows):
        A, b = self.matrix(rows)
        c = np.zeros(3*len(self.segs)); c[0::3] = 1.0
        return linprog(c, A_ub=-A, b_ub=-b, bounds=(-1000, 1000), method='highs').status == 0

    def run(self):
        chosen, rows, refused = {}, self.rows(None), []
        free = []
        for j, S in enumerate(self.segs):
            if S['target']:
                continue
            guided, opts = self.options(j)
            if not opts:
                refused.append(j)
            else:
                free.append((not guided, j, opts))
        if refused:
            raise ValueError(f'REFUSED: segments without a uniform option {refused[:5]}')
        # Depth-guided segments first, so a greedy completion never blocks a guided choice.
        for _, j, opts in sorted(free, key=lambda t: t[:2]):
            for se in opts:
                trial = rows + [r for s in se for r in self.rows(s)]
                if self.feasible(trial):
                    rows, chosen[j] = trial, se
                    break
            else:
                raise ValueError(f'REFUSED: no LP-feasible option for segment {j}')
        A, b = self.matrix(rows)
        n = 3*len(self.segs)
        c = np.zeros(n); c[0::3] = 1.0; c[2::3] = 0.001
        res = milp(c, constraints=LinearConstraint(A, b, np.inf), integrality=np.ones(n),
                   bounds=Bounds([-BOUND, -BOUND, -60*BOUND]*len(self.segs), [BOUND, BOUND, 60*BOUND]*len(self.segs)),
                   options=dict(time_limit=900))
        if res.x is None:
            raise ValueError('REFUSED: no integer potential within the coefficient budget')
        x = [int(round(v)) for v in res.x]
        lines = [f'C {self.branch} {self.gap} {self.q0 % self.gap} {self.q0}']
        for j, S in enumerate(self.segs):
            lines.append('P ' + ' '.join(map(str, [*S['T'], *S['lo'], *S['hi'], *x[3*j:3*j + 3], int(S['target'])])))
        for s in sorted((s for se in chosen.values() for s in se), key=lambda s: (s['S'], s['lo'][1])):
            lines.append('E ' + ' '.join(map(str, [s['S'], s['C'], s['dx'], *s['lo'], *s['hi']])))
        return '\n'.join(lines) + '\n'


if __name__ == '__main__':
    if len(sys.argv) != 7:
        raise SystemExit('usage: EDGES_DIR plus|minus GAP Q_FLOOR Q_LAST OUT')
    d, branch, gap, q0, q1, out = sys.argv[1:]
    syn = Synthesis(d, branch, int(gap), int(q0), int(q1))
    Path(out).write_text(syn.run())
    print('RANK_SYNTHESIS_CANDIDATE pieces', len(syn.pieces), 'segments', len(syn.segs), 'symbolic edges', len(syn.edges),
          '; unverified until kernel/class_b_rank_certificate.mojo check')
