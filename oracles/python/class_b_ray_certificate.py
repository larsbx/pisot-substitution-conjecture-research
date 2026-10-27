"""Independent symbolic verifier of the class-B top-layer ray closure and descent.

Reads the carriers and potentials from the canonical Mojo tables
(kernel/psc/class_b_ray_tables.mojo) and re-proves, with its own Fraction
Sturm chains and affine-ray comparisons, that for every q >= q0 on each ray
the carrier is a strict forward-closed superset of the complete swap-seed
graph and that X = |k| + b strictly decreases along a realizable child of every
non-target carrier label. It cross-checks kernel/psc/class_b_ray_certificate.mojo;
the canonical result is the Mojo one.

Before using them it re-derives, from the incidence matrix it reads off the
image words, the Perron relation q beta(beta+1) = A(beta) and that the scaled
lengths L are a left Perron eigenvector (both coefficient-wise in beta and q).
Conventions: docs/class-b-ray-certificate-2026-10-27.md.

    python oracles/python/class_b_ray_certificate.py [INDEX ...]
"""
from __future__ import annotations

import re
import sys
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TABLES = ROOT / "kernel/psc/class_b_ray_tables.mojo"
WINDOW = 6

# ---------------------------------------------------------------- polynomials in beta (ascending)


def norm(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def add(a, b):
    n = max(len(a), len(b))
    return norm([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def scale(a, c):
    return norm([c * x for x in a])


def sub(a, b):
    return add(a, scale(b, -1))


def mul(a, b):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return norm(out)


def ev(a, x):
    s = F(0)
    for c in reversed(a):
        s = s * x + c
    return s


def prem(a, b):
    a = [F(x) for x in a]
    while len(norm(a)) >= len(b) and norm(a):
        a = norm(a)
        k, c = len(a) - len(b), a[-1] / F(b[-1])
        for i, y in enumerate(b):
            a[i + k] -= c * y
    return norm(a)


def roots_in(p, lo, hi):
    """Distinct real roots of p in (lo, hi] by a Sturm chain."""
    seq = [norm([F(x) for x in p]), norm([F(i * p[i]) for i in range(1, len(p))])]
    while len(seq[-1]) > 1:
        r = prem(seq[-2], seq[-1])
        if not r:
            break
        seq.append([-x for x in r])

    def changes(x):
        s = [v for v in (ev(f, x) for f in seq if f) if v != 0]
        return sum(1 for i in range(1, len(s)) if (s[i] > 0) != (s[i - 1] > 0))

    return changes(lo) - changes(hi)


# ---------------------------------------------------------------- the ray


class Ray:
    def __init__(self, eps, g, r):
        if eps not in (1, -1) or not 0 <= r < g:
            raise ValueError("bad ray")
        self.eps, self.g, self.r = eps, g, r
        self.images = self.images_at  # images as functions of q

    def p_of(self, q):
        return 3 * q + 6 + 6 * self.eps - self.g

    def images_at(self, q):
        x, c, y = 0, 1, 2
        return [[x] + [y] * self.p_of(q) + [x], [c] + [y] * q + [x], [c] + [y] * (q + self.eps) + [x]]

    def derive(self):
        """Read the incidence matrix off the images at two q, as affine in q, and
        derive A(t) with chi(t) = A(t) - q t(t+1); check L M = beta L mod chi."""
        cols = []
        for q in (0, 1):
            im = self.images_at(q + 40)
            cols.append([[w.count(i) for i in range(3)] for w in im])
        # entries are affine in q: M[i][j] = m0 + q m1
        m1 = [[cols[1][j][i] - cols[0][j][i] for j in range(3)] for i in range(3)]
        m0 = [[cols[0][j][i] - 40 * m1[i][j] for j in range(3)] for i in range(3)]
        # chi(t) = det(tI - M) for M = m0 + q m1, expanded as A(t) + q B(t) + q^2 C(t)
        def entry(i, j):
            base = ([0, 1] if i == j else [])
            return [sub(base, [m0[i][j]]), scale([1], -m1[i][j]) if m1[i][j] else []]
        # polynomials in (t, q): represent as list over q-degree of t-polys
        def pm(a, b):
            out = [[] for _ in range(len(a) + len(b) - 1)]
            for i, x in enumerate(a):
                for j, y in enumerate(b):
                    out[i + j] = add(out[i + j], mul(x, y))
            return out

        def pa(a, b, s=1):
            n = max(len(a), len(b))
            return [add(a[i] if i < len(a) else [], scale(b[i], s) if i < len(b) else []) for i in range(n)]

        e = [[entry(i, j) for j in range(3)] for i in range(3)]
        det = []
        for (a, b, c), sgn in (((0, 1, 2), 1), ((1, 2, 0), 1), ((2, 0, 1), 1), ((2, 1, 0), -1), ((0, 2, 1), -1), ((1, 0, 2), -1)):
            det = pa(det, pm(pm(e[0][a], e[1][b]), e[2][c]), sgn)
        while det and not det[-1]:
            det.pop()
        if len(det) != 2 or det[1] != [0, -1, -1]:
            raise ValueError("characteristic polynomial is not A(t) - q t(t+1)")
        self.a_poly = det[0]
        e = self.eps
        self.lengths = [[3 * e, 3 + 3 * e - self.g, 3], [-e, 1 - e, 1], [0, 1, 1]]
        for j in range(3):
            a = sub(add(add(scale(self.lengths[0], m0[0][j]), scale(self.lengths[1], m0[1][j])),
                        scale(self.lengths[2], m0[2][j])), mul(self.lengths[j], [0, 1]))
            b = add(add(scale(self.lengths[0], m1[0][j]), scale(self.lengths[1], m1[1][j])),
                    scale(self.lengths[2], m1[2][j]))
            if add(mul(a, [0, 1, 1]), mul(b, self.a_poly)):
                raise ValueError("L is not a left Perron eigenvector")
        self.runs = [[3 * self.g, 3 * self.r + 6 + 6 * e - self.g], [self.g, self.r], [self.g, self.r + e]]

    def sign(self, expr, q0):
        """sign of a(beta) + l b(beta) for all beta >= q0 + 3 + eps."""
        a, b = expr
        bb = [0, 1, 1]
        f = norm(add(scale(mul(a, bb), self.g), mul(b, sub(self.a_poly, scale(bb, self.r)))))
        if not f:
            return 0
        h = list(reversed(f))
        while h[0] == 0:
            h = h[1:]
        bound = F(1, q0 + 3 + self.eps)
        v = ev(h, bound)
        if v == 0 or roots_in(h, F(0), bound) != 0:
            raise ValueError("UNDECIDED sign")
        return 1 if v > 0 else -1

    def check_bound(self, q0):
        bl = q0 + 3 + self.eps
        if ev(sub(self.a_poly, scale([0, 1, 1], q0)), F(bl)) >= 0:
            raise ValueError("beta_low is not below the Perron root")


def e_add(x, y):
    return add(x[0], y[0]), add(x[1], y[1])


def e_sub(x, y):
    return sub(x[0], y[0]), sub(x[1], y[1])


def disp(ray, u, d, k):
    return sub(mul([1, 1], [-ray.eps * d, u]), [0, ray.g * k[1]]), [0, -ray.g * k[0]] if k[0] else []


def length(ray, t):
    return ray.lengths[t], []


def le(u, v, l0):
    if u[0] <= v[0] and u[0] * l0 + u[1] <= v[0] * l0 + v[1]:
        return 1
    if u[0] >= v[0] and u[0] * l0 + u[1] > v[0] * l0 + v[1]:
        return 0
    return -1


def plus(u, v):
    return [u[0] + v[0], u[1] + v[1]]


def minus(u, v):
    return [u[0] - v[0], u[1] - v[1]]


def ceil_div(u, g):
    if u[0] % g:
        raise ValueError("slope not divisible by g")
    return [u[0] // g, -((-u[1]) // g)]


def floor_div(u, g):
    if u[0] % g:
        raise ValueError("slope not divisible by g")
    return [u[0] // g, u[1] // g]


def amax(u, v, l0):
    if le(u, v, l0) == 1:
        return v
    if le(v, u, l0) == 1:
        return u
    raise ValueError("UNDECIDED max")


def amin(u, v, l0):
    if le(u, v, l0) == 1:
        return u
    if le(v, u, l0) == 1:
        return v
    raise ValueError("UNDECIDED min")


def meet(parts, l0):
    lo, hi = parts[0]
    for a, b in parts[1:]:
        if le(lo, a, l0) == 1:
            lo = a
        elif le(a, lo, l0) != 1:
            return None
        if le(b, hi, l0) == 1:
            hi = b
        elif le(hi, b, l0) != 1:
            return None
    o = le(lo, hi, l0)
    return "empty" if o == 0 else ((lo, hi) if o == 1 else None)


def segment(ray, t, part):
    if part == 0:
        return (0 if t == 0 else 1), 0, 0, [0, 0], [0, 0]
    px = 1 if t == 0 else 0
    run = ray.runs[t]
    if part == 1:
        return 2, px, 1 - px, [0, 0], minus(run, [0, 1])
    return 0, px, 1 - px, run, run


def strict(ray, t, b, T, q0):
    return ray.sign(e_sub(length(ray, t), T), q0) > 0 and ray.sign(e_add(T, length(ray, b)), q0) > 0


def edges(ray, row, u2s):
    top, bot, u, d = row[:4]
    klo = [row[4], row[5]]
    for pt in range(3):
        ct, px1, pc1, lo1, hi1 = segment(ray, top, pt)
        for pb in range(3):
            cb, px2, pc2, lo2, hi2 = segment(ray, bot, pb)
            dx, dc = px2 - px1, pc2 - pc1
            kc = plus(minus([0, u], klo), [0, dx])
            base = [ray.g * u - ray.g * klo[0], (4 + ray.r + ray.eps) * u - ray.g * klo[1] - ray.eps * d + 3 * dx + dc]
            for u2 in u2s:
                rlo = ceil_div(minus(plus(base, minus(lo2, hi1)), [0, u2]), ray.g)
                rhi = floor_div(minus(plus(base, minus(hi2, lo1)), [0, u2]), ray.g)
                yield (pt, pb), ct, cb, u2, -2 * u + dc - 3 * dx, kc, rlo, rhi


def certify(ray, q0, rows, pot):
    ray.derive()
    l0 = (q0 - ray.r) // ray.g
    if ray.g * l0 + ray.r != q0:
        raise ValueError("floor off the ray")
    ray.check_bound(q0)
    sl = {}
    for i, row in enumerate(rows):
        sl.setdefault(tuple(row[:4]), []).append(i)
    st = dict(rows=len(rows), seeds_real=0, seeds_unreal=0, u_cases=0, covered=0, gap_geometry=0,
              window_checks=0, clip_fallbacks=0, terminal_splits=0, pieces=0, targets=0, descent_intervals=0)
    for a in range(3):
        for b in range(a + 1, 3):
            for which in range(4):
                top, bot = (a if which < 2 else b), (b if which % 2 == 0 else a)
                w = [0, 0, 0]
                if which in (1, 3):
                    w[b] += 1
                if which in (2, 3):
                    w[a] -= 1
                k, c, y = w
                u, d = 3 * k + c + y, c - 3 * k
                if strict(ray, top, bot, disp(ray, u, d, [0, k]), q0):
                    st["seeds_real"] += 1
                    if not any(le([rows[i][4], rows[i][5]], [0, k], l0) == 1 and le([0, k], [rows[i][6], rows[i][7]], l0) == 1
                               for i in sl.get((top, bot, u, d), [])):
                        raise ValueError("seed omitted")
                else:
                    st["seeds_unreal"] += 1

    def child_ivs(ct, cb, u2, d2, kc):
        ivs = sorted(((minus(kc, [rows[i][6], rows[i][7]]), minus(kc, [rows[i][4], rows[i][5]])) for i in sl.get((ct, cb, u2, d2), [])),
                     key=lambda iv: iv[0][0] * l0 + iv[0][1])
        for i in range(1, len(ivs)):
            if le(plus(ivs[i - 1][1], [0, 1]), ivs[i][0], l0) != 1:
                raise ValueError("UNDECIDED child order")
        return ivs

    for row in rows:
        top, bot, u, d = row[:4]
        klo, khi = [row[4], row[5]], [row[6], row[7]]
        if le(klo, khi, l0) != 1:
            raise ValueError("empty row")
        for kk in (klo, khi):
            if not strict(ray, top, bot, disp(ray, u, d, kk), q0):
                raise ValueError("row member not strict")
        J = minus(khi, klo)
        has_t = top == bot and u == 0 and d == 0 and le(klo, [0, 0], l0) == 1 and le([0, 0], khi, l0) == 1
        term = minus([0, 0], klo)
        # ---- closure
        for _, ct, cb, u2, d2, kc, _, _ in edges(ray, row, (WINDOW, -WINDOW)):
            for kk in (kc, minus(kc, J)):
                T = disp(ray, u2, d2, kk)
                if u2 > 0 and ray.sign(e_sub(length(ray, ct), T), q0) > 0:
                    raise ValueError("window edge strict")
                if u2 < 0 and ray.sign(e_add(T, length(ray, cb)), q0) > 0:
                    raise ValueError("window edge strict")
            st["window_checks"] += 1
        for _, ct, cb, u2, d2, kc, rlo, rhi in edges(ray, row, range(-WINDOW + 1, WINDOW)):
            st["u_cases"] += 1
            lo, hi = [0, 0], J
            if le([0, 0], rlo, l0) == 1:
                lo = rlo
            elif le(rlo, [0, 0], l0) != 1:
                st["clip_fallbacks"] += 1
            if le(rhi, J, l0) == 1:
                hi = rhi
            elif le(J, rhi, l0) != 1:
                st["clip_fallbacks"] += 1
            if le(lo, hi, l0) == 0:
                continue
            gaps, cur = [], lo
            for a1, a2 in child_ivs(ct, cb, u2, d2, kc):
                gaps.append((cur, minus(a1, [0, 1])))
                cur = plus(a2, [0, 1])
            gaps.append((cur, hi))
            if has_t:
                split = []
                for glo, ghi in gaps:
                    if le(glo, term, l0) == 1 and le(term, ghi, l0) == 1:
                        split += [(glo, minus(term, [0, 1])), (plus(term, [0, 1]), ghi)]
                        st["terminal_splits"] += 1
                    elif le(term, minus(glo, [0, 1]), l0) == 1 or le(plus(ghi, [0, 1]), term, l0) == 1:
                        split.append((glo, ghi))
                    else:
                        raise ValueError("UNDECIDED terminal")
                gaps = split
            for glo, ghi in gaps:
                # Clip to the realizable range. A gap empty for some l only is
                # still decided by its end signs, which hold for every l.
                glo, ghi = amax(glo, lo, l0), amin(ghi, hi, l0)
                if le(glo, ghi, l0) == 0:
                    continue
                if not (ray.sign(e_add(disp(ray, u2, d2, minus(kc, ghi)), length(ray, cb)), q0) <= 0
                        or ray.sign(e_sub(length(ray, ct), disp(ray, u2, d2, minus(kc, glo))), q0) <= 0):
                    raise ValueError("ESCAPE")
                st["gap_geometry"] += 1
            st["covered"] += 1
        # ---- descent
        cut = minus([0, 0], klo)
        for s, a, b in ((-1, [0, 0], minus(cut, [0, 1])), (0, cut, cut), (1, plus(cut, [0, 1]), J)):
            reg = meet([([0, 0], J), (a, b)], l0)
            if reg == "empty":
                continue
            if reg is None:
                raise ValueError("UNDECIDED sign region")
            j1, j2 = reg
            st["pieces"] += 1
            if s == 0 and u == 0 and d == 0:
                st["targets"] += 1
                continue
            bp = pot[(top, bot, u, d, s)]
            good = []
            for _, ct, cb, u2, d2, kc, rlo, rhi in edges(ray, row, range(-WINDOW + 1, WINDOW)):
                for c1, c2 in child_ivs(ct, cb, u2, d2, kc):
                    for t, region in ((-1, (plus(kc, [0, 1]), j2)), (0, (kc, kc)), (1, (j1, minus(kc, [0, 1])))):
                        if (ct, cb, u2, d2, t) not in pot:
                            continue
                        I = meet([(j1, j2), (rlo, rhi), (c1, c2), region], l0)
                        if I is None or I == "empty":
                            continue
                        bc = pot[(ct, cb, u2, d2, t)]
                        if all(le([0, 0], [s * (klo[0] + e[0]) - t * (kc[0] - e[0]), s * (klo[1] + e[1]) - t * (kc[1] - e[1]) + bp - bc - 1], l0) == 1
                               for e in I):
                            good.append(I)
            cur = j1
            while le(plus(j2, [0, 1]), cur, l0) != 1:
                best = None
                for a1, b1 in good:
                    if le(a1, cur, l0) == 1 and le(cur, b1, l0) == 1 and (best is None or le(best, b1, l0) == 1):
                        best = b1
                if best is None:
                    raise ValueError("NO DESCENT")
                cur = plus(best, [0, 1])
                st["descent_intervals"] += 1
    return st


def tables():
    text = TABLES.read_text()
    specs = [list(map(int, m.group(1).split(","))) for m in re.finditer(r"List\[Int\]\(\[([-0-9, ]+)\]\),", text)]

    def flat(name, width):
        vals = list(map(int, re.search(rf'comptime {name} = "([-0-9 ]*)"', text).group(1).split()))
        return [vals[i:i + width] for i in range(0, len(vals), width)]

    for i, spec in enumerate(specs):
        rows = flat(f"ROWS_{i}", 8)
        pot = {tuple(r[:5]): r[5] for r in flat(f"POT_{i}", 6)}
        if len(rows) != spec[5] or len(pot) != spec[6]:
            raise ValueError("table size disagrees with ray_specs")
        yield i, spec, rows, pot


def main():
    want = {int(x) for x in sys.argv[1:]}
    for i, spec, rows, pot in tables():
        if want and i not in want:
            continue
        eps, g, r, q0 = spec[:4]
        st = certify(Ray(eps, g, r), q0, rows, pot)
        print(f"CLASS_B_RAY_ORACLE {'plus' if eps == 1 else 'minus'} g={g} q={g}l+{r} q>={q0} "
              + " ".join(f"{k} {v}" for k, v in st.items()))


if __name__ == "__main__":
    main()
