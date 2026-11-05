"""Independent exact oracle for the cut-attractor bookkeeping, the Lemma F
controls, the configuration census, the endpoint-collapse survey and the deep
strong-coincidence class (docs/c4-cut-attractor-window-2026-11-05.md).

Integers, Fractions and number fields Q(beta) as polynomials reduced modulo a
verified-irreducible minimal polynomial; no floats. No measure, no Rauzy
subtile, no C4/PSC conclusion is computed here.
"""
import collections
import itertools
import pytest
from fractions import Fraction as Fr

from psc_research.pip_screen import pip_corpus


# ---------------------------------------------------------------- words/matrices
def parikh(w):
    p = [0, 0, 0]
    for a in w:
        p[a] += 1
    return tuple(p)


def vadd(a, b):
    return tuple(x + y for x, y in zip(a, b))


def vsub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def incidence(sig):
    return [[sig[b].count(a) for b in range(3)] for a in range(3)]


def matvec(M, v):
    return tuple(sum(M[i][j] * v[j] for j in range(3)) for i in range(3))


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def charpoly(M):
    """x^3 + c2 x^2 + c1 x + c0 as (c0, c1, c2)."""
    T = M[0][0] + M[1][1] + M[2][2]
    U = ((M[0][0] * M[1][1] - M[0][1] * M[1][0]) + (M[0][0] * M[2][2] - M[0][2] * M[2][0])
         + (M[1][1] * M[2][2] - M[1][2] * M[2][1]))
    return (-det3(M), U, -T)


def cubic_irreducible(c):
    c0, c1, c2 = c
    if c0 == 0:
        return False
    for r in range(1, abs(c0) + 1):
        if c0 % r == 0:
            for s in (r, -r):
                if s ** 3 + c2 * s ** 2 + c1 * s + c0 == 0:
                    return False
    return True


def apply(sig, w):
    out = []
    for a in w:
        out.extend(sig[a])
    return out


def power(sig, w, n):
    for _ in range(n):
        w = apply(sig, w)
    return w


def rev(sig):
    return [list(reversed(x)) for x in sig]


# ---------------------------------------------------------------- number field
class NF:
    def __init__(self, c):
        self.c = [Fr(x) for x in c]
        self.n = len(c)

    def el(self, coeffs):
        v = [Fr(x) for x in coeffs] + [Fr(0)] * self.n
        return tuple(v[:self.n])

    def beta(self):
        return self.el([0, 1])

    def add(self, a, b):
        return tuple(x + y for x, y in zip(a, b))

    def sub(self, a, b):
        return tuple(x - y for x, y in zip(a, b))

    def scal(self, k, a):
        return tuple(Fr(k) * x for x in a)

    def mul(self, a, b):
        n = self.n
        prod = [Fr(0)] * (2 * n - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    prod[i + j] += x * y
        for d in range(2 * n - 2, n - 1, -1):
            coef = prod[d]
            if coef:
                prod[d] = Fr(0)
                for k in range(n):
                    prod[d - n + k] -= coef * self.c[k]
        return tuple(prod[:n])

    def dot(self, row, vec):
        acc = self.el([0])
        for r, v in zip(row, vec):
            acc = self.add(acc, self.scal(v, r))
        return acc

    def iszero(self, a):
        return all(x == 0 for x in a)


def quad_sign(a, D=3):
    """Sign of a0 + a1*beta in Q(sqrt D) with beta = 1 + sqrt D."""
    a0, a1 = a[0] + a[1], a[1]
    if a1 == 0:
        return (a0 > 0) - (a0 < 0)
    if a0 == 0:
        return (a1 > 0) - (a1 < 0)
    if a0 > 0 and a1 > 0:
        return 1
    if a0 < 0 and a1 < 0:
        return -1
    if a0 * a0 > D * a1 * a1:
        return (a0 > 0) - (a0 < 0)
    if a0 * a0 < D * a1 * a1:
        return (a1 > 0) - (a1 < 0)
    return 0


# ---------------------------------------------------------------- balanced pairs
def cuts(u, v):
    assert parikh(u) == parikh(v)
    out, pu, pv = [], [0, 0, 0], [0, 0, 0]
    for i in range(len(u) + 1):
        if pu == pv:
            out.append(i)
        if i < len(u):
            pu[u[i]] += 1
            pv[v[i]] += 1
    return out


def factorise(u, v):
    c = cuts(u, v)
    return [(tuple(u[c[k]:c[k + 1]]), tuple(v[c[k]:c[k + 1]]), c[k]) for k in range(len(c) - 1)]


def validate_states(sig, states):
    if len(sig) != 3 or any(not w or any(a not in range(3) for a in w) for w in sig):
        raise ValueError("malformed substitution")
    if not states or len(set(states)) != len(states):
        raise ValueError("empty or duplicate state table")
    for u, v in states:
        if not u or not v or any(a not in range(3) for a in u + v):
            raise ValueError("malformed state")
        if parikh(u) != parikh(v) or cuts(u, v) != [0, len(u)] or u == v:
            raise ValueError("state is not irreducible, balanced and noncoincident")


def validate_closure(sig, states, rows=None):
    """Independently reconstruct every child; optionally compare supplied rows."""
    validate_states(sig, states)
    expected = []
    for u, v in states:
        row = []
        for a, b, _ in factorise(apply(sig, u), apply(sig, v)):
            if a == b:
                raise ValueError("coincident factor")
            if (a, b) not in states:
                raise ValueError("missing child state")
            row.append(states.index((a, b)))
        expected.append(row)
    if rows is not None and rows != expected:
        raise ValueError("child occurrences differ from exact ordered factors")


def strict_closure(sig, seed, cap=256):
    """Ordered breadth-first child closure; raises on a coincident factor."""
    validate_states(sig, [seed])
    if cap <= 0:
        raise ValueError("state cap must be positive")
    states, idx, rows, q = [seed], {seed: 0}, [], 0
    while q < len(states):
        u, v = states[q]
        q += 1
        kids = []
        for a, b, _pos in factorise(apply(sig, list(u)), apply(sig, list(v))):
            if a == b:
                raise ValueError("coincident factor")
            S = (a, b)
            if S not in idx:
                if len(states) >= cap:
                    raise ValueError("state cap exhausted")
                idx[S] = len(states)
                states.append(S)
            kids.append(idx[S])
        rows.append(kids)
    return states, rows


def locate(sig, word, pos):
    acc = 0
    for i, letter in enumerate(word):
        n = len(sig[letter])
        if acc <= pos < acc + n:
            return i, tuple(sig[letter][:pos - acc])
        acc += n
    raise RuntimeError


def interior_edges(sig, states, rows=None):
    """(parent, child-first-letters, d, i, Q, i', Q') for every interior cut, with
    the Lemma N identities asserted."""
    validate_closure(sig, states, rows)
    M = incidence(sig)
    out = []
    for F, (u, v) in enumerate(states):
        su, sv = apply(sig, list(u)), apply(sig, list(v))
        for a, b, pos in factorise(su, sv):
            if pos == 0:
                continue
            d = parikh(su[:pos])
            i, Q = locate(sig, u, pos)
            i2, Q2 = locate(sig, v, pos)
            assert d == vadd(matvec(M, parikh(u[:i])), parikh(Q))
            assert d == vadd(matvec(M, parikh(v[:i2])), parikh(Q2))
            assert sig[u[i]][len(Q)] == a[0] and sig[v[i2]][len(Q2)] == b[0]
            assert (parikh(u[:i]), u[i]) != (parikh(v[:i2]), v[i2])
            out.append((F, (a[0], b[0]), d, i, Q, i2, Q2))
    return out


def recursion_holds(sig, states, depth):
    validate_closure(sig, states)
    M = incidence(sig)
    r = len(states)
    dvec = {}
    for F, (u, v) in enumerate(states):
        su, sv = apply(sig, list(u)), apply(sig, list(v))
        for a, b, pos in factorise(su, sv):
            dvec.setdefault(F, []).append((states.index((a, b)), parikh(su[:pos])))
    for root in range(r):
        X = {S: collections.Counter() for S in range(r)}
        X[root][(0, 0, 0)] = 1
        for n in range(1, depth + 1):
            Xn = {S: collections.Counter() for S in range(r)}
            for F in range(r):
                for x, mult in X[F].items():
                    for S, d in dvec[F]:
                        Xn[S][vadd(matvec(M, x), d)] += mult
            u, v = states[root]
            su, sv = power(sig, list(u), n), power(sig, list(v), n)
            direct = {S: collections.Counter() for S in range(r)}
            for a, b, pos in factorise(su, sv):
                direct[states.index((a, b))][parikh(su[:pos])] += 1
            if direct != Xn or any(m > 1 for S in range(r) for m in Xn[S].values()):
                return False
            X = Xn
    return True


def left_sc_level(sig, i, j, nmax):
    for n in range(1, nmax + 1):
        wi, wj = power(sig, [i], n), power(sig, [j], n)
        pi, pj = [0, 0, 0], [0, 0, 0]
        for k in range(min(len(wi), len(wj))):
            if pi == pj and wi[k] == wj[k]:
                return (n, k, wi[k])
            pi[wi[k]] += 1
            pj[wj[k]] += 1
    return None  # exhausted budget, not a verdict


REDUCIBLE = [[1, 0], [1, 0, 2], [2, 1, 1]]
UNIFORM = [[0, 1, 2], [1, 2, 0], [2, 0, 1]]
UNIT_PIP = [[0, 1], [1, 2], [0, 2, 1]]
DEEP = [[1], [2], [0, 1]]


def test_reducible_strict_control_bookkeeping():
    sig = REDUCIBLE
    M = incidence(sig)
    assert not cubic_irreducible(charpoly(M))
    states, rows = strict_closure(sig, ((1, 0, 2), (2, 1, 0)))
    assert states == [((1, 0, 2), (2, 1, 0)), ((1, 0, 2, 1, 0, 2, 1, 1), (2, 1, 1, 1, 0, 2, 1, 0)),
                      ((1, 1, 1, 0, 2), (2, 1, 1, 1, 0)),
                      ((1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 1), (2, 1, 1, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0))]
    r = len(states)
    N = [[rows[S].count(T) for S in range(r)] for T in range(r)]
    assert N == [[0, 3, 0, 5], [1, 1, 0, 1], [0, 1, 0, 3], [0, 0, 1, 0]]
    P = [[parikh(states[S][0])[i] for S in range(r)] for i in range(3)]
    assert matmul(P, N) == matmul(M, P)
    # L^T N = beta L^T exactly in Q(sqrt 3), beta = 1 + sqrt 3, ell = (1, sqrt 3, 2)
    K = NF([-2, -2])
    beta = K.beta()
    ell = (K.el([1]), K.el([-1, 1]), K.el([2]))
    assert all(K.iszero(K.sub(K.dot(ell, tuple(M[i][j] for i in range(3))), K.mul(beta, ell[j]))) for j in range(3))
    L = [K.dot(ell, parikh(states[S][0])) for S in range(r)]
    assert all(quad_sign(x) > 0 for x in L)
    for S in range(r):
        lhs = K.el([0])
        for T in range(r):
            lhs = K.add(lhs, K.scal(N[T][S], L[T]))
        assert K.iszero(K.sub(lhs, K.mul(beta, L[S])))
    edges = interior_edges(sig, states, rows)
    assert len(edges) == 12
    assert sum(1 for F, _p, _d, i, _Q, _i2, _Q2 in edges if states[F][0][i] != states[F][0][0]) == 8
    assert all(p == (1, 2) or p == (2, 1) for _F, p, *_ in edges)
    assert recursion_holds(sig, states, 3)
    assert left_sc_level(sig, 0, 1, 8) == (1, 0, 1)
    assert left_sc_level(sig, 1, 2, 8) is None
    # Lemma F hypothesis fails: ell.(2,0,-1) = 0; no non-cut common vertex found to depth 5 (budget).
    assert K.iszero(K.dot(ell, (2, 0, -1)))
    noncut = 0
    for u0, v0 in states:
        for n in range(6):
            u, v = power(sig, list(u0), n), power(sig, list(v0), n)
            keyu, exact, p = collections.Counter(), collections.Counter(), (0, 0, 0)
            for i in range(len(u) + 1):
                keyu[(p[1], p[0] + 2 * p[2])] += 1
                exact[p] += 1
                if i < len(u):
                    p = vadd(p, parikh([u[i]]))
            p = (0, 0, 0)
            for i in range(len(v) + 1):
                noncut += keyu[(p[1], p[0] + 2 * p[2])] - exact[p]
                if i < len(v):
                    p = vadd(p, parikh([v[i]]))
    assert noncut == 0


def test_uniform_control_and_lemma_f_negative():
    sig = UNIFORM
    states, rows = strict_closure(sig, ((0, 1, 2), (1, 2, 0)))
    assert len(states) == 3
    assert [[rows[S].count(T) for S in range(3)] for T in range(3)] == [[1, 1, 1]] * 3
    edges = interior_edges(sig, states)
    assert len(edges) == 6
    assert sum(1 for F, _p, _d, i, *_ in edges if states[F][0][i] != states[F][0][0]) == 6
    assert recursion_holds(sig, states, 3)
    # ell = (1,1,1) has a rational relation: common vertices exceed balanced cuts.
    u, v = power(sig, [0, 1, 2], 2), power(sig, [1, 2, 0], 2)
    common = len(u) + 1
    balanced = sum(1 for i in range(len(u) + 1) if parikh(u[:i]) == parikh(v[:i]))
    assert (common, balanced) == (28, 10)


def test_powered_uniform_zero_source_defect():
    sig = [apply(UNIFORM, w) for w in UNIFORM]
    assert sig[:2] == [[0, 1, 2, 1, 2, 0, 2, 0, 1], [1, 2, 0, 2, 0, 1, 0, 1, 2]]
    states, rows = strict_closure(sig, ((0, 1, 2), (1, 2, 0)))
    assert len(states) == 3
    assert [[rows[S].count(T) for S in range(3)] for T in range(3)] == [[3, 3, 3]] * 3
    edges = interior_edges(sig, states, rows)
    assert len(edges) == 24
    assert edges[0] == (0, (1, 2), (1, 1, 1), 0, (0, 1, 2), 0, (1, 2, 0))
    zero = [e for e in edges if parikh(states[e[0]][0][:e[3]]) == parikh(states[e[0]][1][:e[5]])]
    assert len(zero) == 6
    assert all(states[F][0][i] != states[F][1][i2] for F, _p, _d, i, _Q, i2, _Q2 in zero)
    assert sum(states[F][0][i] != states[F][0][0] for F, _p, _d, i, *_ in edges) == 18
    assert recursion_holds(sig, states, 3)


def test_malformed_closures_and_missing_occurrences_are_refused():
    states, rows = strict_closure(UNIFORM, ((0, 1, 2), (1, 2, 0)))
    for bad_states in ([], states[:-1], states + [states[0]],
                       [((0,), (0,))], [((0, 1), (1, 2))],
                       [((0, 1, 0, 1), (1, 0, 1, 0))], [((0, 3), (3, 0))]):
        with pytest.raises(ValueError):
            interior_edges(UNIFORM, bad_states)
        with pytest.raises(ValueError):
            recursion_holds(UNIFORM, bad_states, 1)
    for bad_row in (rows[0][:-1], rows[0][1:], rows[0] + [rows[0][0]],
                    [-1] + rows[0][1:], [len(states)] + rows[0][1:],
                    [rows[0][1], rows[0][0], rows[0][2]]):
        with pytest.raises(ValueError):
            interior_edges(UNIFORM, states, [bad_row] + rows[1:])
    with pytest.raises(ValueError):
        interior_edges(UNIFORM, states, rows[:-1])
    with pytest.raises(ValueError):
        interior_edges(UNIT_PIP, [((1, 0), (0, 1))])
    for seed in (((0,), (0,)), ((0, 1), (1, 2)),
                 ((0, 1, 0, 1), (1, 0, 1, 0)), ((0, 3), (3, 0))):
        with pytest.raises(ValueError):
            strict_closure(UNIFORM, seed)
    with pytest.raises(ValueError):
        strict_closure(UNIFORM, ((0, 1, 2), (1, 2, 0)), cap=2)


def test_unit_pip_common_vertices_are_balanced_cuts():
    sig = UNIT_PIP
    M = incidence(sig)
    c = charpoly(M)
    assert cubic_irreducible(c) and abs(det3(M)) == 1
    K = NF(list(c))
    beta = K.beta()
    ell = (K.el([1]), K.el([-1, 1]), K.el([1, -2, 1]))
    assert all(K.iszero(K.sub(K.dot(ell, tuple(M[i][j] for i in range(3))), K.mul(beta, ell[j]))) for j in range(3))
    expected = {((0, 1), (1, 0)): [2, 3, 6, 14, 39], ((0, 2), (2, 0)): [4, 9, 18, 44, 104]}
    for (u0, v0), counts in expected.items():
        got = []
        for n in range(1, 6):
            u, v = power(sig, list(u0), n), power(sig, list(v0), n)
            posu, pu = {}, (0, 0, 0)
            for i in range(len(u) + 1):
                posu.setdefault(K.dot(ell, pu), []).append(pu)
                if i < len(u):
                    pu = vadd(pu, parikh([u[i]]))
            common = balanced = 0
            pv = (0, 0, 0)
            for i in range(len(v) + 1):
                for pj in posu.get(K.dot(ell, pv), []):
                    common += 1
                    balanced += pj == pv
                if i < len(v):
                    pv = vadd(pv, parikh([v[i]]))
            assert common == balanced
            got.append(balanced)
        assert got == counts
    try:
        strict_closure(sig, ((1, 0), (0, 1)))
    except ValueError:
        pass
    else:
        raise AssertionError("the swap seed of a unit PIP was accepted as strict")


def merged(g, a, b, steps=12):
    for _ in range(steps):
        if a == b:
            return True
        a, b = g[a], g[b]
    return a == b


def test_configuration_census():
    maps = list(itertools.product(range(3), repeat=3))
    gpair = lambda g, p: frozenset((g[min(p)], g[max(p)]))
    triples = []
    for g in maps:
        for G in (frozenset((0, 1)), frozenset((0, 2)), frozenset((1, 2))):
            h = ({0, 1, 2} - G).pop()
            cands = [frozenset((h, x)) for x in sorted(G)]
            for mask in (1, 2, 3):
                A = {c for k, c in enumerate(cands) if (mask >> k) & 1}
                if all(g[min(p)] != g[max(p)] and gpair(g, p) in A and not merged(g, *sorted(p)) for p in A):
                    triples.append((g, G, frozenset(A)))
    assert len(triples) == 54
    cyc, fixed, swap = collections.Counter(), 0, 0
    for g, _G, A in triples:
        longest = 1
        for p in A:
            q = p
            for _ in range(5):
                q = gpair(g, q)
            per, q2 = 1, gpair(g, q)
            while q2 != q:
                per += 1
                q2 = gpair(g, q2)
            longest = max(longest, per)
        cyc[(len(A), longest)] += 1
        assert any(g[g[a]] == a and g[g[b]] == b for a, b in (sorted(p) for p in A))
        if len(A) == 1:
            a, b = sorted(next(iter(A)))
            fixed += g[a] == a and g[b] == b
            swap += g[a] == b and g[b] == a
    assert dict(cyc) == {(1, 1): 36, (2, 1): 15, (2, 2): 3}
    assert (fixed, swap) == (18, 18)
    dist, inst = collections.Counter(), 0
    for g in maps:
        for p in [(0, 1), (0, 2), (1, 2)]:
            if merged(g, *p):
                continue
            inst += 1
            orbit = [p]
            for _ in range(12):
                orbit.append((g[orbit[-1][0]], g[orbit[-1][1]]))
            t = next(t for t in range(12) if orbit[t] in orbit[t + 1:])
            m = next(m for m in range(1, 12) if orbit[t + m] == orbit[t])
            dist[(t, m)] += 1
    assert inst == 42 and dict(dist) == {(0, 1): 9, (1, 1): 6, (0, 2): 15, (1, 2): 6, (0, 3): 6}


def corpus_sigmas():
    return [[list(x - 1 for x in spec[a + 1]) for a in range(3)] for spec in pip_corpus()]


def test_endpoint_collapse_survey():
    sigs = corpus_sigmas()
    assert len(sigs) == 4554

    def nonmerged(sig, first):
        g = [sig[a][0] if first else sig[a][-1] for a in range(3)]
        return {p for p in [(0, 1), (0, 2), (1, 2)] if not merged(g, *p)}

    cf = cl = either = 0
    joint = collections.Counter()
    for s in sigs:
        Rf, Rl = nonmerged(s, True), nonmerged(s, False)
        cf += not Rf
        cl += not Rl
        if not Rf or not Rl:
            either += 1
        else:
            joint[(len(Rf), len(Rl))] += 1
    assert (cf, cl, either, 4554 - either) == (1896, 1896, 3012, 1542)
    assert dict(joint) == {(2, 2): 534, (2, 3): 408, (3, 2): 408, (3, 3): 192}


def test_deep_strong_coincidence_class():
    base = DEEP
    assert cubic_irreducible(charpoly(incidence(base)))
    assert {p: left_sc_level(base, *p, 16) for p in [(0, 1), (0, 2), (1, 2)]} == {
        (0, 1): (13, 17, 1), (0, 2): (14, 17, 1), (1, 2): (12, 17, 1)}
    assert left_sc_level(base, 0, 1, 12) is None
    assert {p: left_sc_level(rev(base), *p, 16) for p in [(0, 1), (0, 2), (1, 2)]} == {
        (0, 1): (15, 47, 1), (0, 2): (1, 0, 1), (1, 2): (14, 47, 1)}
    keyset = {tuple(tuple(x) for x in s) for s in corpus_sigmas()}
    cls = set()
    for perm in itertools.permutations(range(3)):
        rl = [None] * 3
        for a in range(3):
            rl[perm[a]] = [perm[x] for x in base[a]]
        for s in (rl, rev(rl)):
            cls.add(tuple(tuple(x) for x in s))
    assert len(cls) == 12 and cls <= keyset
    maxima = sorted(max(left_sc_level([list(x) for x in c], *p, 16)[0] for p in [(0, 1), (0, 2), (1, 2)]) for c in cls)
    assert maxima == [14] * 6 + [15] * 6
