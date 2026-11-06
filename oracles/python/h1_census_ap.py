#!/usr/bin/env python3
"""Independent oracle for the dim H^1 census: the Anderson-Putnam 1-collared
complex (Anderson-Putnam 1998, Thm 4.3 / 6.1), sharing no construction with
kernel/psc/h1_census.mojo (which uses the Barge-Diamond vertex-edge graph).

  * language: legal words of length <= 4 as the closure of the letters under
    w -> {factors of sigma(w) of length <= 4}; sound and complete by induction
    on the inflation level because every image is non-empty.
  * collared tiles = legal 3-words [b a c]; each is a 1-cell oriented left to
    right. Two vertex presentations are computed and must agree:
      A: endpoint nodes R[bac] ~ L[acd] for every legal 4-word bacd (the
         Anderson-Putnam quotient);
      B: vertex = legal 2-word; [bac] runs from ba to ac.
  * f on 1-cells: [b a c] with sigma(a) = a_1..a_n, u = last(sigma b),
    v = first(sigma c) maps to [u a_1 a_2][a_1 a_2 a_3]...[a_{n-1} a_n v].
  * H_1(K_1; Q) = ker(boundary); dim H^1(Omega; Q) = eventual rank of the
    induced map (transpose over a field).

Exact integers and Fractions only. The script prints the census tables when
run with the repository root; the pytest wrapper tests/test_h1_census_oracle.py
pins them. It certifies no pure discrete spectrum and changes no claim.
"""
import collections
import sys
from fractions import Fraction


# ---------------------------------------------------------------- exact linear algebra
def rref(rows, ncols):
    rows = [list(r) for r in rows]
    pivots, r = [], 0
    for c in range(ncols):
        p = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        inv = Fraction(1) / rows[r][c]
        rows[r] = [x * inv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        pivots.append(c)
        r += 1
        if r == len(rows):
            break
    return rows[:r], pivots


def rank(matrix_rows, ncols):
    if not matrix_rows:
        return 0
    return len(rref([[Fraction(x) for x in row] for row in matrix_rows], ncols)[1])


def nullspace(matrix_rows, ncols):
    red, piv = rref([[Fraction(x) for x in row] for row in matrix_rows], ncols)
    basis = []
    for fcol in (c for c in range(ncols) if c not in piv):
        v = [Fraction(0)] * ncols
        v[fcol] = Fraction(1)
        for prow, pcol in zip(red, piv):
            v[pcol] = -prow[fcol]
        basis.append(v)
    return basis


def matmul_int(A, B):
    n, k, m = len(A), len(B), len(B[0]) if B else 0
    out = [[0] * m for _ in range(n)]
    for i in range(n):
        for t in range(k):
            a = A[i][t]
            if a:
                Bt = B[t]
                oi = out[i]
                for j in range(m):
                    oi[j] += a * Bt[j]
    return out


def eventual_rank(A):
    n = len(A)
    P = A
    for _ in range(n - 1):
        P = matmul_int(P, A)
    return rank(P, n)


def det_int(A):
    n = len(A)
    M = [[Fraction(x) for x in row] for row in A]
    d = Fraction(1)
    for c in range(n):
        p = next((i for i in range(c, n) if M[i][c] != 0), None)
        if p is None:
            return 0
        if p != c:
            M[c], M[p] = M[p], M[c]
            d = -d
        d *= M[c][c]
        for i in range(c + 1, n):
            if M[i][c] != 0:
                f = M[i][c] / M[c][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[c])]
    assert d.denominator == 1
    return int(d)


def _gcd(a, b):
    while b:
        a, b = b, a % b
    return a


# ---------------------------------------------------------------- substitution data
def image(sigma, w):
    out = []
    for a in w:
        out.extend(sigma[a])
    return tuple(out)


def legal_words(sigma, n):
    if any(len(img) == 0 for img in sigma):
        raise ValueError("erasing substitution")
    S = {(a,) for a in range(len(sigma))}
    frontier = list(S)
    while frontier:
        new = []
        for w in frontier:
            img = image(sigma, w)
            for L in range(1, n + 1):
                for i in range(len(img) - L + 1):
                    v = img[i:i + L]
                    if v not in S:
                        S.add(v)
                        new.append(v)
        frontier = new
    return S


def incidence(sigma):
    d = len(sigma)
    return [[sigma[j].count(i) for j in range(d)] for i in range(d)]


def is_primitive(M):
    n = len(M)
    Q = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    for _ in range((n - 1) ** 2 + 1):
        Q = matmul_int(Q, M)
    return all(x > 0 for row in Q for x in row)


class UnionFind:
    def __init__(self, n):
        self.p = list(range(n))

    def find(self, x):
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x

    def union(self, a, b):
        a, b = self.find(a), self.find(b)
        if a != b:
            self.p[a] = b


def edge_path(sigma, e):
    b, a, c = e
    x = (sigma[b][-1],) + tuple(sigma[a]) + (sigma[c][0],)
    return [x[i:i + 3] for i in range(len(x) - 2)]


def ap_h1(sigma, variant):
    words = legal_words(sigma, 4)
    L2 = sorted(w for w in words if len(w) == 2)
    L3 = sorted(w for w in words if len(w) == 3)
    L4 = sorted(w for w in words if len(w) == 4)
    E = len(L3)
    eidx = {e: i for i, e in enumerate(L3)}
    if variant == "A":
        uf = UnionFind(2 * E)
        for (b, a, c, d) in L4:
            uf.union(2 * eidx[(b, a, c)] + 1, 2 * eidx[(a, c, d)])
        node_class, tail, head = {}, [], []
        for i in range(E):
            for node in (2 * i, 2 * i + 1):
                r = uf.find(node)
                if r not in node_class:
                    node_class[r] = len(node_class)
            tail.append(node_class[uf.find(2 * i)])
            head.append(node_class[uf.find(2 * i + 1)])
        V = len(node_class)

        def f_node(node):
            i, side = divmod(node, 2)
            path = edge_path(sigma, L3[i])
            return 2 * eidx[path[0] if side == 0 else path[-1]] + side
        for (b, a, c, d) in L4:
            assert uf.find(f_node(2 * eidx[(b, a, c)] + 1)) == uf.find(f_node(2 * eidx[(a, c, d)]))
    elif variant == "B":
        vidx = {w: i for i, w in enumerate(L2)}
        V = len(L2)
        tail = [vidx[(b, a)] for (b, a, c) in L3]
        head = [vidx[(a, c)] for (b, a, c) in L3]
        for (a, c) in L2:
            assert (sigma[a][-1], sigma[c][0]) in vidx
    else:
        raise ValueError(variant)
    F = [[0] * E for _ in range(E)]
    for j, e in enumerate(L3):
        path = edge_path(sigma, e)
        for p in path:
            assert p in eidx
            F[eidx[p]][j] += 1
        for p, q in zip(path, path[1:]):
            assert head[eidx[p]] == tail[eidx[q]]
    B = [[0] * E for _ in range(V)]
    for j in range(E):
        B[head[j]][j] += 1
        B[tail[j]][j] -= 1
    uf2 = UnionFind(V)
    for j in range(E):
        uf2.union(tail[j], head[j])
    c = len({uf2.find(v) for v in range(V)})
    Z = nullspace(B, E)
    N = len(Z)
    assert N == E - V + c
    cols = []
    for z in Z:
        den = 1
        for x in z:
            den = den * x.denominator // _gcd(den, x.denominator)
        cols.append([int(x * den) for x in z])
    P = [[cols[k][i] for k in range(N)] for i in range(E)]
    for _ in range(N):
        P = matmul_int(F, P) if N else P
    return dict(E=E, V=V, c=c, h1K=N, dimH1=rank(P, N) if N else 0, L2=len(L2))


def analyse(sigma):
    """sigma: list of tuples/lists over letters 0..d-1."""
    M = incidence(sigma)
    if not is_primitive(M):
        raise ValueError("not primitive")
    rA, rB = ap_h1(sigma, "A"), ap_h1(sigma, "B")
    assert rA["dimH1"] == rB["dimH1"], ("variants disagree", sigma, rA, rB)
    return dict(det=det_int(M), evrank=eventual_rank(M), A=rA, B=rB, dimH1=rA["dimH1"])


# ---------------------------------------------------------------- endpoint types (A..G = 0..6)
def endpoint_type(h):
    fixed = sum(1 for a in range(3) if h[a] == a)
    two = any(h[h[a]] == a and h[a] != a for a in range(3))
    if fixed == 3:
        return 3
    if fixed == 2:
        return 2
    if fixed == 0:
        return 5 if two else 6
    if two:
        return 4
    return 0 if len(set(h)) == 1 else 1


def endpoint_cell(sigma):
    return 7 * endpoint_type([w[0] for w in sigma]) + endpoint_type([w[-1] for w in sigma])


# ---------------------------------------------------------------- census
def corpus_sigmas(repo_root):
    sys.path.insert(0, repo_root + "/reference")
    from psc_research.pip_screen import pip_corpus
    return [[tuple(x - 1 for x in spec[a + 1]) for a in range(3)] for spec in pip_corpus()]


def census(sigmas):
    tables = dict(dimensions=collections.Counter(), unimodular=collections.Counter(),
                  det_dimension=collections.Counter(), endpoint_dimension=collections.Counter(),
                  shapes_bd=None, disconnected=0, total=0)
    for sig in sigmas:
        r = analyse(sig)
        d = r["dimH1"]
        tables["dimensions"][d] += 1
        if abs(r["det"]) == 1:
            tables["unimodular"][d] += 1
        tables["det_dimension"][(r["det"], d)] += 1
        tables["endpoint_dimension"][(endpoint_cell(sig) // 7, endpoint_cell(sig) % 7, d)] += 1
        tables["total"] += 1
    return tables


def main():
    if len(sys.argv) < 2:
        print("usage: h1_census_ap.py REPO_ROOT")
        return 2
    t = census(corpus_sigmas(sys.argv[1]))
    print("total", t["total"])
    print("dimensions", dict(sorted(t["dimensions"].items())))
    print("unimodular", dict(sorted(t["unimodular"].items())))
    print("det_dimension", sorted(t["det_dimension"].items()))
    print("endpoint_dimension", sorted(t["endpoint_dimension"].items()))
    return 0


if __name__ == "__main__":
    sys.exit(main())
