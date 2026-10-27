"""Exploratory class-B step-2b carriers: the forward closure of the strict core.

FLOATING POINT, one member at a time. A scratch probe for the 2b stop/go, never a
certificate: strictness is decided in double precision with a 1e-7 margin, and
the closure is capped. The certificate this probe argues for must decide every
sign exactly (Lemmas 1-2 of class-b-ray-certificate-2026-10-27.md).

Model (class-b-ray-certificate-2026-10-27.md, "Setting"): letters (x, c, y) =
(0, 1, 2), sigma(x) = x y^p x, sigma(c) = c y^q x, sigma(y) = c y^r x with
r = q + eps, p = 3q + 6 + 6eps - g. A state is (top, bottom, w), w the integral
bottom-minus-top offset; T(w) = L.w and the state is strict iff
-L_bottom < T < L_top. Children: w' = M w + prefix_bottom(j) - prefix_top(i).

Modes:
  carrier BRANCH G Q OUT   write C_q = closure(strict core) as a .labels file
  contains BRANCH G Q NATIVE_LABELS
                           does C_q contain the native Mojo graph's labels?
  window BRANCH G Q U D    negative control: the window strict set
                           {|u| <= U, |d| <= D} is not closed and does not
                           reach offset zero
"""
from collections import deque
from pathlib import Path
import sys

import numpy as np

CORE = dict(u=3, d=6, k=2)  # |u| <= 3, |d| <= 6, |k| <= 2
CAP = 100000


class Member:
    def __init__(self, branch, g, q):
        self.eps = 1 if branch == 'plus' else -1
        p, r = 3 * q + 6 + 6 * self.eps - g, q + self.eps
        self.words = [[0] + [2] * p + [0], [1] + [2] * q + [0], [1] + [2] * r + [0]]
        self.M = np.array([[2, 1, 1], [0, 1, 1], [p, q, r]])
        self.beta = max(np.linalg.eigvals(self.M).real)
        b, e = self.beta, self.eps
        self.L = np.array([3 * b * b + (3 + 3 * e - g) * b + 3 * e, (b + 1) * (b - e), b * (b + 1)])
        if not np.allclose(self.L @ self.M, b * self.L):
            raise ValueError('L is not a left Perron eigenvector')
        self.pref = []
        for w in self.words:
            acc, rows = np.zeros(3, int), []
            for a in w:
                rows.append(acc.copy())
                acc[a] += 1
            self.pref.append(rows)
        self.pos = [np.array([self.L @ v for v in rows]) for rows in self.pref]

    def strict(self, t, b, w):
        T = self.L @ np.asarray(w)
        return -self.L[b] + 1e-7 < T < self.L[t] - 1e-7

    def children(self, t, b, w):
        """Strict children; the child displacement increases in the bottom index."""
        w = np.asarray(w)
        mw, bt = self.M @ w, self.beta * (self.L @ w)
        out = []
        for i, ai in enumerate(self.pos[t]):
            ti = self.words[t][i]
            lo = np.searchsorted(self.pos[b], ai - bt - self.L.max() - 1)
            for j in range(max(lo - 1, 0), len(self.words[b])):
                if bt + self.pos[b][j] - ai >= self.L[ti]:
                    break
                w2 = mw + self.pref[b][j] - self.pref[t][i]
                if self.strict(ti, self.words[b][j], w2):
                    out.append((ti, self.words[b][j], tuple(int(x) for x in w2)))
        return out

    def slice_states(self, U, D, K):
        """Strict states with |u| <= U, |d| <= D, |k| <= K; u = 3k+c+y, d = c-3k."""
        return {(t, b, (k, d + 3 * k, u - 6 * k - d))
                for t in range(3) for b in range(3) for u in range(-U, U + 1)
                for d in range(-D, D + 1) for k in range(-K, K + 1)
                if self.strict(t, b, (k, d + 3 * k, u - 6 * k - d))}


def closure(member, start):
    seen, dq, adj = set(start), deque(start), {}
    while dq:
        s = dq.popleft()
        adj[s] = [] if s[2] == (0, 0, 0) else member.children(*s)
        for c in adj[s]:
            if c not in seen:
                seen.add(c)
                dq.append(c)
        if len(seen) > CAP:
            raise RuntimeError('CLOSURE_BUDGET_EXHAUSTED: no verdict')
    return adj


def first_hit_depths(adj):
    rev = {}
    for s, ks in adj.items():
        for c in ks:
            rev.setdefault(c, []).append(s)
    depth = {s: 0 for s in adj if s[2] == (0, 0, 0)}
    dq = deque(depth)
    while dq:
        c = dq.popleft()
        for s in rev.get(c, []):
            if s not in depth:
                depth[s] = depth[c] + 1
                dq.append(s)
    return depth


def main():
    mode, branch, g, q = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    member = Member(branch, g, q)
    if mode == 'carrier':
        adj = closure(member, member.slice_states(CORE['u'], CORE['d'], CORE['k']))
        depth = first_hit_depths(adj)
        if len(depth) != len(adj):
            sys.exit(f'{branch} {g} {q}: closure state without offset-zero descendant')
        rows = sorted((t, b, *w, depth[(t, b, w)]) for t, b, w in adj)
        Path(sys.argv[5]).write_text(f'M {q} {len(rows)} {max(r[5] for r in rows)}\n'
                                     + ''.join('V ' + ' '.join(map(str, r)) + '\n' for r in rows))
    elif mode == 'window':
        U, D = int(sys.argv[5]), int(sys.argv[6])
        S = member.slice_states(U, D, 200)
        escapes, adj = 0, {}
        for s in S:
            kids = [] if s[2] == (0, 0, 0) else member.children(*s)
            adj[s] = [c for c in kids if c in S]
            escapes += len(kids) - len(adj[s])
        print('window strict states', len(S), 'strict children leaving the window', escapes,
              'reach offset zero', len(first_hit_depths(adj)))
    elif mode == 'contains':
        graph = {(int(t), int(b), (int(k), int(c), int(y)))
                 for t, b, k, c, y, _ in (line.split()[1:] for line in Path(sys.argv[5]).read_text().splitlines()[1:])}
        adj = closure(member, member.slice_states(CORE['u'], CORE['d'], CORE['k']))
        print('closure(core)', len(adj), 'native graph', len(graph), 'graph states outside closure', len(graph - set(adj)),
              'reach offset zero', len(first_hit_depths(adj)))
    else:
        sys.exit('usage: carrier BRANCH G Q OUT | window BRANCH G Q U D | contains BRANCH G Q NATIVE_LABELS')


if __name__ == '__main__':
    main()
