"""Exploratory finite probe for class-B step 2b: are per-ray carriers g-uniform?

Fits each residue ray exactly as class_b_label_rays.audit does (earliest floor
whose first two members predict every later member), then asks whether the
rays of one residue regime share a single table whose l-slopes are constant
and whose intercepts are affine in g. Finite observation only: a fit here is
a candidate regime table, never a certificate.
"""
from collections import defaultdict
from pathlib import Path
import argparse
import json
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from class_b_label_rays import expand, intervals, predict, read  # noqa: E402


def fit_ray(files, gap, residue):
    """Return (floor, members, rows) or None; rows are [t,b,u,d,a,b0,c,e] at floor."""
    qs = sorted(q for q in files if q % gap == residue)
    data = {q: intervals(read(files[q])[1]) for q in qs}
    for q in qs:
        if expand(data[q]) != {r[:5] for r in read(files[q])[1]}:
            raise ValueError('lossy compression')
    for i, q in enumerate(qs[:-2]):
        tail = qs[i:]
        if any(v != q + j * gap for j, v in enumerate(tail)):
            raise ValueError(f'missing ray member near q={q}')
        try:
            ok = all(predict(data[q], data[tail[1]], j) == data[v] for j, v in enumerate(tail[2:], 2))
        except ValueError:
            ok = False
        if ok:
            a, b = data[q], data[q + gap]
            l0 = q // gap
            rows = [[*x[:4], y[4] - x[4], x[4] - (y[4] - x[4]) * l0, y[5] - x[5], x[5] - (y[5] - x[5]) * l0]
                    for x, y in zip(a, b)]
            return q, len(tail), rows
    return None


def keyed(rows):
    """Rows keyed by slice and ordinal: a slice (t, b, u, d) may hold several k-intervals."""
    seen, out = defaultdict(int), {}
    for x in rows:
        key = tuple(x[:4])
        out[(*key, seen[key])] = tuple(x[4:])
        seen[key] += 1
    return out


def regime_fit(rays):
    """rays: {g: rows}. Return the g-affine table, or the first key/slope/intercept conflict."""
    gs = sorted(rays)
    tables = {g: keyed(rays[g]) for g in gs}
    keys = set(tables[gs[0]])
    for g in gs[1:]:
        if set(tables[g]) != keys:
            return dict(ok=False, reason='keys', g=g, only_new=len(set(tables[g]) - keys), only_old=len(keys - set(tables[g])))
    if len(gs) < 3:
        return dict(ok=False, reason='too few gaps to check an affine fit', gaps=gs)
    g0, g1 = gs[0], gs[1]
    table = {}
    for key in sorted(keys):
        a0, b0, c0, e0 = tables[g0][key]
        a1, b1, c1, e1 = tables[g1][key]
        if (a0, c0) != (a1, c1):
            return dict(ok=False, reason='slope', key=key, g=g1)
        # intercepts b(g) = beta0 + beta1 g, checked on every further gap
        db, de = b1 - b0, e1 - e0
        if db % (g1 - g0) or de % (g1 - g0):
            return dict(ok=False, reason='non-integral intercept slope', key=key)
        bg, eg = db // (g1 - g0), de // (g1 - g0)
        for g in gs[2:]:
            a, b, c, e = tables[g][key]
            if (a, c) != (a0, c0) or b != b0 + bg * (g - g0) or e != e0 + eg * (g - g0):
                return dict(ok=False, reason='intercept', key=key, g=g, got=(a, b, c, e))
        table[key] = (a0, b0 - bg * g0, bg, c0, e0 - eg * g0, eg)
    return dict(ok=True, gaps=gs, rows=len(table), table=table)


def middle_fit(rays):
    """rays: {(g, r): rows}. One table with constant slopes, intercepts affine in (g, r)?"""
    pts = sorted(rays)
    tables = {pt: keyed(rays[pt]) for pt in pts}
    keys = set(tables[pts[0]])
    if any(set(tables[pt]) != keys for pt in pts):
        return dict(ok=False, reason='keys')
    # three affinely independent anchor points determine (alpha, beta_g, beta_r)
    base = next(((a, b, c) for a in pts for b in pts for c in pts
                 if (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0]) != 0), None)
    if base is None or len(pts) < 4:
        return dict(ok=False, reason='too few points')
    a, b, c = base
    det = (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])
    table = {}
    for key in sorted(keys):
        va, vb, vc = tables[a][key], tables[b][key], tables[c][key]
        if not (va[0] == vb[0] == vc[0] and va[2] == vb[2] == vc[2]):
            return dict(ok=False, reason='slope', key=key)
        coef = []
        for i in (1, 3):
            db, dc = vb[i] - va[i], vc[i] - va[i]
            ng = db * (c[1] - a[1]) - dc * (b[1] - a[1])
            nr = dc * (b[0] - a[0]) - db * (c[0] - a[0])
            if ng % det or nr % det:
                return dict(ok=False, reason='non-integral intercept', key=key)
            bg, br = ng // det, nr // det
            coef.append((va[i] - bg * a[0] - br * a[1], bg, br))
        for pt in pts:
            v = tables[pt][key]
            if (v[0], v[2]) != (va[0], va[2]) or any(
                    v[i] != c0 + cg * pt[0] + cr * pt[1] for i, (c0, cg, cr) in zip((1, 3), coef)):
                return dict(ok=False, reason='intercept', key=key, at=pt)
        table[key] = (va[0], *coef[0], va[2], *coef[1])
    return dict(ok=True, rows=len(table), table=table)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('directory')
    p.add_argument('--out')
    a = p.parse_args()
    files = defaultdict(dict)
    for path in Path(a.directory).glob('*.labels'):
        m = re.fullmatch(r'(plus|minus)-g(\d+)-q(\d+)\.labels', path.name)
        files[m[1], int(m[2])][int(m[3])] = path
    fits = {}
    for (branch, gap), byq in sorted(files.items()):
        for residue in range(gap):
            fit = fit_ray(byq, gap, residue)
            fits[branch, gap, residue] = fit
            print(branch, gap, residue, 'NO_FLOOR' if fit is None else f'floor {fit[0]} members {fit[1]} rows {len(fit[2])}')
    report = []
    for branch in ('plus', 'minus'):
        gaps = sorted(g for b, g in files if b == branch)
        if not gaps:
            continue
        for g_min in gaps:
            for j0 in range(0, 6):
                for j1 in range(1, 10):
                    rays = {(g, r): fits[branch, g, r][2] for g in gaps if g >= g_min
                            for r in range(j0, g - j1 + 1) if fits.get((branch, g, r)) is not None}
                    if len({g for g, _ in rays}) < 3:
                        continue
                    res = middle_fit(rays)
                    if res['ok']:
                        print(dict(branch=branch, kind='middle', j0=j0, j1=j1, g_min=g_min, rays=len(rays), rows=res['rows']))
        for kind in ('low', 'high'):
            for j in range(0, max(gaps)):
                rays = {}
                for g in gaps:
                    r = j if kind == 'low' else g - j
                    if not (0 <= r < g) or (kind == 'high' and j == 0):
                        continue
                    fit = fits.get((branch, g, r))
                    if fit is not None:
                        rays[g] = fit[2]
                # the largest suffix of gaps on which one g-affine table holds
                best = None
                gs = sorted(rays)
                for start in range(len(gs)):
                    res = regime_fit({g: rays[g] for g in gs[start:]})
                    if res['ok']:
                        best = res
                        break
                if len(gs) >= 3:
                    summary = dict(branch=branch, kind=kind, j=j, gaps=gs,
                                   uniform_from=None if best is None else best['gaps'][0],
                                   rows=None if best is None else best['rows'])
                    print(summary)
                    report.append(dict(summary, table=None if best is None else
                                       [[*k, *v] for k, v in sorted(best['table'].items())]))
    if a.out:
        Path(a.out).write_text(json.dumps(report, indent=1) + '\n')


if __name__ == '__main__':
    main()
