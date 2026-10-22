"""Independent symbolic verifier of the class-A carrier closure and descent tables.

Reads the 89 carrier rows, the potential pieces and the descent rows from the
canonical Mojo sources and re-proves, with its own Fraction Sturm chains and
affine-ray comparisons, that for every integer n >= n0 the carrier is forward
closed, contains every real swap seed, and that the chosen child occurrences
strictly lower a non-negative integer potential. This is the cross-check of
`kernel/psc/class_a_carrier_closure.mojo` and `class_a_carrier_descent.mojo`;
the canonical result is the Mojo one.

Conventions (bottom minus top offsets, scaled lengths L=(1+h+h^2,1,1+h),
displacement T = s + k h(1+h) + y h, n h(1+h) = 1-h-h^2-h^3) are derived in
docs/class-a-carrier-closure-2026-10-22.md.
"""
from __future__ import annotations

from fractions import Fraction as F
from pathlib import Path
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
ROWS_SRC = ROOT / "kernel/psc/class_a_typed_carrier.mojo"
DATA_SRC = ROOT / "kernel/psc/class_a_descent_data.mojo"


# ---------------------------------------------------------------------------
# integer polynomials in h (ascending) and exact Sturm root counting
# ---------------------------------------------------------------------------
def pnorm(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def padd(a, b):
    return pnorm([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(max(len(a), len(b)))])


def pscale(a, c):
    return pnorm([c * x for x in a])


def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1) if a and b else []
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return pnorm(out)


def peval(a, x):
    r = F(0)
    for c in reversed(a):
        r = r * x + c
    return r


def prem(a, b):
    a = [F(x) for x in pnorm(a)]
    b = [F(x) for x in pnorm(b)]
    while a and len(a) >= len(b):
        q = a[-1] / b[-1]
        d = len(a) - len(b)
        for i in range(len(b)):
            a[d + i] -= q * b[i]
        a = pnorm(a)
    return a


def sturm_chain(p):
    chain = [pnorm([F(x) for x in p]), pnorm([i * p[i] for i in range(1, len(p))])]
    while chain[-1]:
        r = prem(chain[-2], chain[-1])
        if not r:
            break
        chain.append([-x for x in r])
    return [c for c in chain if c]


def variations(chain, x):
    s = [v for v in ((peval(c, x) > 0) - (peval(c, x) < 0) for c in chain) if v]
    return sum(1 for i in range(1, len(s)) if s[i] != s[i - 1])


def sign_on_interval(p, q):
    """sign of p on (0, q]; raises when not uniform (fail closed)."""
    p = pnorm(p)
    if not p:
        return 0
    while p[0] == 0:
        p = p[1:]
    at_q = peval(p, q)
    if at_q == 0:
        raise ValueError("UNDECIDED: polynomial vanishes at the interval bound")
    ch = sturm_chain(p)
    if variations(ch, F(0)) - variations(ch, q) != 0:
        raise ValueError("UNDECIDED: root inside (0, q]")
    return 1 if at_q > 0 else -1


N_NUM = [1, -1, -1, -1]   # n h (1+h) = 1 - h - h^2 - h^3
D_DEN = [0, 1, 1]


class AffH:
    """A(h) + n B(h)."""
    def __init__(self, a, b=None):
        self.a, self.b = pnorm(a), pnorm(b or [])

    def __add__(s, o):
        return AffH(padd(s.a, o.a), padd(s.b, o.b))

    def __sub__(s, o):
        return AffH(padd(s.a, pscale(o.a, -1)), padd(s.b, pscale(o.b, -1)))

    def sign(s, q):
        return sign_on_interval(padd(pmul(s.a, D_DEN), pmul(N_NUM, s.b)), q)


def times(coef, poly):
    return AffH(pscale(poly, coef[1]), pscale(poly, coef[0]))


LENGTH = {0: AffH([1, 1, 1]), 1: AffH([1]), 2: AffH([1, 1])}


def displacement(s, k, y):
    return times(s, [1]) + times(k, [0, 1, 1]) + times(y, [0, 1])


# ---------------------------------------------------------------------------
# affine integers on the ray n >= n0
# ---------------------------------------------------------------------------
def a_le(u, v, n0):
    if u[0] <= v[0] and u[0] * n0 + u[1] <= v[0] * n0 + v[1]:
        return True
    if u[0] >= v[0] and u[0] * n0 + u[1] > v[0] * n0 + v[1]:
        return False
    return None


def a_add(u, v):
    return (u[0] + v[0], u[1] + v[1])


def a_sub(u, v):
    return (u[0] - v[0], u[1] - v[1])


def a_max(u, v, n0):
    if a_le(u, v, n0) is True:
        return v
    if a_le(v, u, n0) is True:
        return u
    raise ValueError("UNDECIDED affine maximum")


def a_min(u, v, n0):
    if a_le(u, v, n0) is True:
        return u
    if a_le(v, u, n0) is True:
        return v
    raise ValueError("UNDECIDED affine minimum")


FIRST = {0: 0, 1: 1, 2: 0}
LAST = {0: 0, 1: 0, 2: 1}
RUN = {0: (1, 1), 1: (1, 0), 2: (1, 1)}


def segment(letter, part):
    """child letter, prefix x count, prefix c count, prefix-y range [lo, hi]."""
    if part == 0:
        return FIRST[letter], 0, 0, (0, 0), (0, 0)
    fx = 1 if FIRST[letter] == 0 else 0
    run = RUN[letter]
    if part == 1:
        return 2, fx, 1 - fx, (0, 0), a_sub(run, (0, 1))
    return LAST[letter], fx, 1 - fx, run, run


# ---------------------------------------------------------------------------
# tables
# ---------------------------------------------------------------------------
def _lists(src: Path, name: str, width: int):
    text = src.read_text()
    start = text.index("def %s(" % name)
    end = text.find("\ndef ", start + 1)
    body = text[start:end if end > 0 else None]
    pat = r"List\[Int\]\(\[(-?\d+(?:,-?\d+){%d})\]\)" % (width - 1)
    return [tuple(map(int, m.split(","))) for m in re.findall(pat, body)]


def carrier_rows():
    rows = _lists(ROWS_SRC, "template_rows", 8)
    if len(rows) != 89:
        raise ValueError("expected 89 carrier rows")
    return rows


def pieces():
    return _lists(DATA_SRC, "piece_rows", 8)


def descents():
    return _lists(DATA_SRC, "descent_rows", 9)


def slices(rows):
    out = {}
    for i, r in enumerate(rows):
        out.setdefault(r[:4], []).append(i)
    return out


# ---------------------------------------------------------------------------
# closure
# ---------------------------------------------------------------------------
def strict(top, bottom, t, q):
    return (LENGTH[top] - t).sign(q) > 0 and (t + LENGTH[bottom]).sign(q) > 0


def verify_closure(rows, n0, window=6):
    if n0 < 4:
        raise ValueError("n0 >= 4 required")
    q = F(1, n0 + 1)
    sl = slices(rows)
    st = dict(seeds_real=0, seeds_unreal=0, member_checks=0, segments=0, y_cases=0,
              covered=0, gap_geometry=0, window_checks=0, clip_fallbacks=0, terminal_splits=0)
    # seeds
    for a in range(3):
        for b in range(a + 1, 3):
            for which in range(4):
                top = a if which < 2 else b
                bottom = b if which % 2 == 0 else a
                w = [0, 0, 0]
                if which in (1, 3):
                    w[b] += 1
                if which in (2, 3):
                    w[a] -= 1
                s = sum(w)
                t = displacement((0, s), (0, w[0]), (0, w[2]))
                if strict(top, bottom, t, q):
                    st["seeds_real"] += 1
                    ok = any(a_le((rows[i][4], rows[i][5]), (0, w[0]), n0) and a_le((0, w[0]), (rows[i][6], rows[i][7]), n0)
                             for i in sl.get((top, bottom, s, w[2]), []))
                    if not ok:
                        raise ValueError("real swap seed omitted")
                else:
                    st["seeds_unreal"] += 1
    for row in rows:
        t, b, s, y, al, bl, au, bu = row
        k_lo, J = (al, bl), (au - al, bu - bl)
        if a_le((0, 0), J, n0) is not True:
            raise ValueError("empty row")
        for k in (k_lo, (au, bu)):
            if not strict(t, b, displacement((0, s), k, (0, y)), q):
                raise ValueError("row member is not a strict overlap")
            st["member_checks"] += 1
        terminal = None
        if t == b and s == 0 and y == 0 and a_le(k_lo, (0, 0), n0) is True and a_le((0, 0), (au, bu), n0) is True:
            terminal = (-al, -bl)
        for pt in range(3):
            for pb in range(3):
                ct, fxt, fct, mt_lo, mt_hi = segment(t, pt)
                cb, fxb, fcb, mb_lo, mb_hi = segment(b, pb)
                dx, dc = fxb - fxt, fcb - fct
                k0 = (al, bl + s + dx)
                base = (al + s, bl + y)
                d_lo, d_hi = a_sub(mb_lo, mt_hi), a_sub(mb_hi, mt_lo)
                st["segments"] += 1
                for yw in (window, -window):
                    s2 = 2 * s + dx + dc + yw
                    t0 = displacement((0, s2), k0, (0, yw))
                    tj = displacement((0, s2), a_add(k0, J), (0, yw))
                    if yw > 0:
                        if (LENGTH[ct] - t0).sign(q) > 0 or (LENGTH[ct] - tj).sign(q) > 0:
                            raise ValueError("window edge is real")
                    elif (t0 + LENGTH[cb]).sign(q) > 0 or (tj + LENGTH[cb]).sign(q) > 0:
                        raise ValueError("window edge is real")
                    st["window_checks"] += 1
                for y2 in range(-window + 1, window):
                    s2 = 2 * s + dx + dc + y2
                    st["y_cases"] += 1
                    r_lo = a_sub(a_sub((0, y2), base), d_hi)
                    r_hi = a_sub(a_sub((0, y2), base), d_lo)
                    try:
                        lo = a_max(r_lo, (0, 0), n0)
                    except ValueError:
                        lo = (0, 0)
                        st["clip_fallbacks"] += 1
                    try:
                        hi = a_min(r_hi, J, n0)
                    except ValueError:
                        hi = J
                        st["clip_fallbacks"] += 1
                    if a_le(lo, hi, n0) is False:
                        continue
                    ivs = sorted(((a_sub((rows[i][4], rows[i][5]), k0), a_sub((rows[i][6], rows[i][7]), k0))
                                  for i in sl.get((ct, cb, s2, y2), [])), key=lambda iv: iv[0][0] * n0 + iv[0][1])
                    for i in range(1, len(ivs)):
                        if a_le(a_add(ivs[i - 1][1], (0, 1)), ivs[i][0], n0) is not True:
                            raise ValueError("target intervals not uniformly ordered")
                    gaps, cur = [], lo
                    for ilo, ihi in ivs:
                        gaps.append((cur, a_sub(ilo, (0, 1))))
                        cur = a_add(ihi, (0, 1))
                    gaps.append((cur, hi))
                    if terminal is not None:
                        split = []
                        for glo, ghi in gaps:
                            inside = a_le(glo, terminal, n0) is True and a_le(terminal, ghi, n0) is True
                            outside = a_le(terminal, a_sub(glo, (0, 1)), n0) is True or a_le(a_add(ghi, (0, 1)), terminal, n0) is True
                            if inside:
                                split += [(glo, a_sub(terminal, (0, 1))), (a_add(terminal, (0, 1)), ghi)]
                                st["terminal_splits"] += 1
                            elif outside:
                                split.append((glo, ghi))
                            else:
                                raise ValueError("terminal membership varies with n")
                        gaps = split
                    for glo, ghi in gaps:
                        glo, ghi = a_max(glo, lo, n0), a_min(ghi, hi, n0)
                        if a_le(glo, ghi, n0) is False:
                            continue
                        t_hi = displacement((0, s2), a_add(k0, ghi), (0, y2))
                        if (t_hi + LENGTH[cb]).sign(q) <= 0:
                            st["gap_geometry"] += 1
                            continue
                        t_lo = displacement((0, s2), a_add(k0, glo), (0, y2))
                        if (LENGTH[ct] - t_lo).sign(q) <= 0:
                            st["gap_geometry"] += 1
                            continue
                        raise ValueError("ESCAPE: real child outside the carrier, row %s seg %d,%d y'=%d" % (row, pt, pb, y2))
                    st["covered"] += 1
    return st


# ---------------------------------------------------------------------------
# descent
# ---------------------------------------------------------------------------
def nonneg(u, n0):
    return a_le((0, 0), u, n0) is True


def partition(parts, lo, hi, n0, what):
    if not parts:
        raise ValueError(what + ": no parts")
    cur = lo
    for p_lo, p_hi in parts:
        if p_lo != cur:
            raise ValueError(what + ": parts do not tile")
        if a_le(p_lo, a_add(p_hi, (0, 1)), n0) is not True:
            raise ValueError(what + ": negative length")
        cur = a_add(p_hi, (0, 1))
    if cur != a_add(hi, (0, 1)):
        raise ValueError(what + ": parts stop short")


def potential(piece, j):
    return (piece[5] + piece[6] * j[0], piece[6] * j[1] + piece[7])


def is_target(row, piece):
    return row[2] == 0 and row[3] == 0 and piece[1:3] == piece[3:5] and row[4] + piece[1] == 0 and row[5] + piece[2] == 0


def verify_descent(rows, P, D, n0):
    q = F(1, n0 + 1)
    by_row = {}
    for p in P:
        by_row.setdefault(p[0], []).append(((p[1], p[2]), (p[3], p[4])))
    for ri, row in enumerate(rows):
        partition(by_row.get(ri, []), (0, 0), (row[6] - row[4], row[7] - row[5]), n0, "pieces of row %d" % ri)
    bound_slope, bound_at = 0, 0
    targets = 0
    for p in P:
        for j in ((p[1], p[2]), (p[3], p[4])):
            x = potential(p, j)
            if not nonneg(x, n0):
                raise ValueError("negative potential")
            bound_slope = max(bound_slope, x[0])
            bound_at = max(bound_at, x[0] * n0 + x[1])
        targets += is_target(rows[p[0]], p)
    by_piece = {}
    for d in D:
        by_piece.setdefault(d[0], []).append(((d[1], d[2]), (d[3], d[4])))
    for pi, p in enumerate(P):
        if is_target(rows[p[0]], p):
            if pi in by_piece:
                raise ValueError("target piece has descent rows")
            continue
        partition(by_piece.get(pi, []), (p[1], p[2]), (p[3], p[4]), n0, "descents of piece %d" % pi)
    for d in D:
        pi, lo_a, lo_b, hi_a, hi_b, pt, pb, yp, cpi = d
        parent, child = P[pi], P[cpi]
        row, crow = rows[parent[0]], rows[child[0]]
        s_lo, s_hi = (lo_a, lo_b), (hi_a, hi_b)
        ct, fxt, fct, mt_lo, mt_hi = segment(row[0], pt)
        cb, fxb, fcb, mb_lo, mb_hi = segment(row[1], pb)
        dx, dc = fxb - fxt, fcb - fct
        s2 = 2 * row[2] + dx + dc + yp
        if (ct, cb, s2, yp) != tuple(crow[:4]):
            raise ValueError("child type disagrees with child piece")
        k_lo = (row[4], row[5])
        k0 = a_add(k_lo, (0, row[2] + dx))
        shift = a_sub(k0, (crow[4], crow[5]))
        if not nonneg(a_sub(a_add(s_lo, shift), (child[1], child[2])), n0) or not nonneg(a_sub((child[3], child[4]), a_add(s_hi, shift)), n0):
            raise ValueError("child leaves its piece")
        base = (row[4] + row[2], row[5] + row[3])
        d_lo, d_hi = a_sub(mb_lo, mt_hi), a_sub(mb_hi, mt_lo)
        if not nonneg(a_sub(a_sub(a_sub((0, yp), base), s_hi), d_lo), n0) or not nonneg(a_sub(d_hi, a_sub(a_sub((0, yp), base), s_lo)), n0):
            raise ValueError("occurrence not realizable")
        for j in (s_lo, s_hi):
            if not strict(row[0], row[1], displacement((0, row[2]), a_add(k_lo, j), (0, row[3])), q):
                raise ValueError("source not strict")
            if not strict(crow[0], crow[1], displacement((0, s2), a_add(k0, j), (0, yp)), q):
                raise ValueError("child not strict")
            drop = a_sub(a_sub(potential(parent, j), potential(child, a_add(j, shift))), (0, 1))
            if not nonneg(drop, n0):
                raise ValueError("potential does not drop")
    return dict(pieces=len(P), targets=targets, descent_rows=len(D), bound_slope=bound_slope,
                bound_const=bound_at - bound_slope * n0)


def main(argv):
    n0 = int(argv[1]) if len(argv) > 1 else 8
    rows = carrier_rows()
    closure = verify_closure(rows, n0)
    descent = verify_descent(rows, pieces(), descents(), n0)
    print(json.dumps(dict(n0=n0, closure=closure, descent=descent,
                          scope="class-A line (n+1,n,n+1): seed graph in carrier and uniform hit depth <= bound for every n>=n0; other A/C regions and universal #139 open"), indent=2))


if __name__ == "__main__":
    main(sys.argv)
