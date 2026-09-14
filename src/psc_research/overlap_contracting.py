"""Contracting lower bound on the first boundary-coincidence depth (exact Q(beta)).

An overlap (i, j, t) with a level-m descendant of offset 0 satisfies
    t = -sum_{s=0}^{m-1} beta^{-(s+1)} c_s
with each increment c_s in the finite digit set F of single-inflation offset
increments q - p (prefix positions of sub-tiles).  Applying a contracting
embedding sigma_k (|sigma_k(beta)| < 1) gives
    |sigma_k(t)| <= C_k * sum_{s=1}^{m} |sigma_k(beta)|^{-s},   C_k = max_F |sigma_k(c)|,
so the first left-aligned depth b(O) is at least the least m for which this
holds for every contracting embedding.  Complex pair: with rho(t) = N(t)/t =
|sigma_2(t)|^2 and Chebyshev's sum inequality, rho(t) <= K m sum_{s=1}^{m}
(beta/D)^s, K = max_F rho(c).  Two real conjugates: sign tests at each root.
All comparisons are exact sign tests of elements of Q(beta) at a real root."""
from __future__ import annotations

from fractions import Fraction

from .overlap_graph import Elt, Field, OverlapGraph


def field_norm(F: Field, x: Elt) -> Fraction:
    """N(x) = det of multiplication by x on the basis 1, beta, beta^2."""
    T, U, D = Fraction(F.T), Fraction(F.U), Fraction(F.D)
    cols = [x]
    for _ in range(2):
        a0, a1, a2 = cols[-1]
        # beta * (a0 + a1 b + a2 b^2) with b^3 = T b^2 - U b + D
        cols.append((a2 * D, a0 - a2 * U, a1 + a2 * T))
    m = [[cols[j][i] for j in range(3)] for i in range(3)]
    return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
            - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))


def discriminant(F: Field) -> int:
    a, b, c = -F.T, F.U, -F.D
    return 18 * a * b * c - 4 * a ** 3 * c + a * a * b * b - 4 * b ** 3 - 27 * c * c


class RealRoot:
    """Sign of elements of Q(beta) under the real embedding at a chosen root of chi."""

    def __init__(self, F: Field, lo: Fraction, hi: Fraction):
        self.f, self.lo, self.hi = F.f, lo, hi
        assert F.f(lo) * F.f(hi) < 0

    def sign(self, x: Elt) -> int:
        if not any(x):
            return 0
        while True:
            lo, hi = self.lo, self.hi
            a1, a2 = x[1], x[2]
            m1, M1 = sorted((a1 * lo, a1 * hi))
            sq = sorted((lo * lo, hi * hi))
            if lo < 0 < hi:
                sq[0] = Fraction(0)
            m2, M2 = sorted((a2 * sq[0], a2 * sq[1]))
            if x[0] + m1 + m2 > 0:
                return 1
            if x[0] + M1 + M2 < 0:
                return -1
            mid = (lo + hi) / 2
            if self.f(lo) * self.f(mid) <= 0:
                self.hi = mid
            else:
                self.lo = mid


def _sturm_count(F: Field, a: Fraction, b: Fraction) -> int:
    """Number of real roots of chi in (a, b] by Sturm's theorem."""
    p0 = [Fraction(1), Fraction(-F.T), Fraction(F.U), Fraction(-F.D)]
    p1 = [Fraction(3), Fraction(-2 * F.T), Fraction(F.U)]

    def ev(p, x):
        r = Fraction(0)
        for c in p:
            r = r * x + c
        return r

    def rem(p, q):
        p = p[:]
        while len(p) >= len(q) and any(p):
            k = p[0] / q[0]
            for i in range(len(q)):
                p[i] -= k * q[i]
            p.pop(0)
        return p

    seq = [p0, p1]
    while len(seq[-1]) > 1:
        r = [-c for c in rem(seq[-2], seq[-1])]
        while r and r[0] == 0:
            r.pop(0)
        if not r:
            break
        seq.append(r)
    def changes(x):
        vals = [ev(p, x) for p in seq]
        vals = [v for v in vals if v != 0]
        return sum(1 for u, v in zip(vals, vals[1:]) if (u < 0) != (v < 0))
    return changes(a) - changes(b)


def contracting_real_roots(F: Field) -> list[RealRoot]:
    """Isolating brackets in (-1, 1) for the two real contracting conjugates."""
    lo, hi = Fraction(-1), Fraction(1)
    assert _sturm_count(F, lo, hi) == 2
    stack, out = [(lo, hi)], []
    while stack:
        a, b = stack.pop()
        n = _sturm_count(F, a, b)
        if n == 0:
            continue
        if n == 1 and F.f(a) * F.f(b) < 0:
            out.append(RealRoot(F, a, b))
            continue
        mid = (a + b) / 2
        if F.f(mid) == 0:
            raise ArithmeticError("rational root of an irreducible cubic")
        stack.extend([(a, mid), (mid, b)])
    assert len(out) == 2
    return out


def digit_set(g: OverlapGraph) -> list[Elt]:
    """Single-inflation offset increments q - p over all letter pairs and sub-tiles."""
    F = g.F
    pos = {}
    for a, word in g.sigma.items():
        cur, ps = F.zero, []
        for letter in word:
            ps.append(cur)
            cur = F.add(cur, g.l[letter - 1])
        pos[a] = ps
    out = set()
    for a in pos:
        for b in pos:
            for p in pos[a]:
                for q in pos[b]:
                    out.add(F.sub(q, p))
    return sorted(out)


def _abs(sign_fn, x: Elt) -> Elt:
    return x if sign_fn(x) >= 0 else tuple(-c for c in x)


class ContractingBound:
    """Least m allowed by the contracting embeddings for a hit at level m."""

    def __init__(self, g: OverlapGraph, max_level: int = 64):
        F = self.F = g.F
        self.max_level = max_level
        self.complex = discriminant(F) < 0
        digits = [c for c in digit_set(g) if any(c)]
        one = F.one
        if self.complex:
            # K = max_F |N(c)|/|c| chosen by cross-multiplication; store c* and |N(c*)|
            best, best_norm = None, None
            for c in digits:
                nc = abs(field_norm(F, c))
                ac = _abs(F.sign, c)
                if best is None:
                    best, best_norm = ac, nc
                    continue
                # nc/|c| > best_norm/|best|  <=>  nc*|best| - best_norm*|c| > 0
                lhs = F.sub(F.mul((nc, 0, 0), best), F.mul((best_norm, 0, 0), ac))
                if F.sign(lhs) > 0:
                    best, best_norm = ac, nc
            self.cstar, self.cstar_norm = best, best_norm
            D = Fraction(F.D)
            assert D > 0
            # S_m = m * sum_{s=1}^m beta^s D^{m-s}
            self.S = [F.zero]
            beta_pow = [one]
            for _ in range(max_level):
                beta_pow.append(F.mul(beta_pow[-1], F.beta))
            for m in range(1, max_level + 1):
                acc = F.zero
                for s in range(1, m + 1):
                    acc = F.add(acc, F.mul(beta_pow[s], (D ** (m - s), 0, 0)))
                self.S.append(F.mul((Fraction(m), 0, 0), acc))
            self.Dpow = [D ** m for m in range(max_level + 1)]
        else:
            self.roots = contracting_real_roots(F)
            self.per_root = []
            for r in self.roots:
                eps = r.sign(F.beta)
                assert eps != 0
                eb = tuple(eps * c for c in F.beta)  # |beta_k| as a field element at root k
                cs = [_abs(r.sign, c) for c in digits]
                cmax = cs[0]
                for c in cs[1:]:
                    if r.sign(F.sub(c, cmax)) > 0:
                        cmax = c
                # G_m = sum_{s=0}^{m-1} |beta_k|^s ; compare |t beta^m| <= C_k G_m
                G, pw = [F.zero], one
                for _ in range(max_level):
                    G.append(F.add(G[-1], pw))
                    pw = F.mul(pw, eb)
                bpow = [one]
                for _ in range(max_level):
                    bpow.append(F.mul(bpow[-1], F.beta))
                self.per_root.append((r, cmax, G, bpow))

    def least_level(self, t: Elt) -> int:
        F = self.F
        if not any(t):
            return 0
        if self.complex:
            nt = abs(field_norm(F, t))
            at = _abs(F.sign, t)
            lhs_const = F.mul((nt, 0, 0), self.cstar)  # |N(t)| |c*|
            rhs_base = F.mul(at, (self.cstar_norm, 0, 0))  # |t| |N(c*)|
            for m in range(1, self.max_level + 1):
                # |N(t)| D^m |c*| <= |t| |N(c*)| S_m
                lhs = F.mul(lhs_const, (self.Dpow[m], 0, 0))
                if F.sign(F.sub(F.mul(rhs_base, self.S[m]), lhs)) >= 0:
                    return m
            raise ArithmeticError("contracting bound exceeded the level cap")
        worst = 0
        for r, cmax, G, bpow in self.per_root:
            for m in range(1, self.max_level + 1):
                tb = _abs(r.sign, F.mul(t, bpow[m]))
                if r.sign(F.sub(F.mul(cmax, G[m]), tb)) >= 0:
                    worst = max(worst, m)
                    break
            else:
                raise ArithmeticError("contracting bound exceeded the level cap")
        return worst
