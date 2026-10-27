"""Independent oracle for a class-B piecewise rank certificate. Not canonical.

Re-derives every all-parameter condition by another route than the Mojo checker:
an affine function of k on [lo(t), hi(t)] is evaluated at both endpoints, each
endpoint value is an affine function of t, and those are compared on t >= 0.
Coverage is swept by brute force up to a horizon |Δv0|+1 over all endpoint
pairs, an independent bound past every crossing of integer-slope lines.
`replay` reads a native `edges` export and checks the two graph hypotheses.
"""
import sys
from itertools import combinations
from pathlib import Path


def parse(text):
    lines = text.splitlines()
    tag, branch, gap, residue, q0 = lines[0].split()
    if tag != 'C' or branch not in ('plus', 'minus'):
        raise ValueError('bad header')
    pieces, edges = [], []
    for line in lines[1:]:
        tag, *row = line.split()
        row = tuple(map(int, row))
        if tag == 'P' and len(row) == 12:
            pieces.append(dict(T=row[:4], lo=row[4:6], hi=row[6:8], X=row[8:11], target=bool(row[11])))
        elif tag == 'E' and len(row) == 7:
            edges.append(dict(P=row[0], Q=row[1], dx=row[2], lo=row[3:5], hi=row[5:7]))
        else:
            raise ValueError('bad row')
    return dict(gap=int(gap), q0=int(q0), pieces=pieces, edges=edges)


def nonneg(slope, v0):
    """slope*t + v0 >= 0 for every integer t >= 0."""
    return v0 >= 0 and slope >= 0


def X_on(cert, i, k_aff):
    """X_i(q(t), k(t)) as (slope, v0) in t, for k(t) = k_aff."""
    a, b, c = cert['pieces'][i]['X']
    return (a*cert['gap'] + b*k_aff[0], a*cert['q0'] + b*k_aff[1] + c)


def check(cert):
    P, E = cert['pieces'], cert['edges']
    for i, p in enumerate(P):
        if not nonneg(p['hi'][0] - p['lo'][0], p['hi'][1] - p['lo'][1]):
            raise ValueError(f'piece {i} empty')
        if p['target'] and (p['T'][2:], p['lo'], p['hi']) != ((0, 0), (0, 0), (0, 0)):
            raise ValueError('bad target')
        for end in (p['lo'], p['hi']):
            if not nonneg(*X_on(cert, i, end)):
                raise ValueError(f'negative potential on piece {i}')
    for (i, p), (j, r) in zip(enumerate(P), list(enumerate(P))[1:]):
        if p['T'] > r['T'] or (p['T'] == r['T'] and not nonneg(r['lo'][0] - p['hi'][0], r['lo'][1] - p['hi'][1] - 1)):
            raise ValueError(f'pieces {i},{j} overlap or unordered')
    for n, e in enumerate(E):
        p, q = P[e['P']], P[e['Q']]
        if p['target'] or e['dx'] not in (-1, 0, 1):
            raise ValueError('bad edge')
        base = p['T'][2] + e['dx']
        for lo, hi in ((p['lo'], e['lo']), (e['lo'], e['hi']), (e['hi'], p['hi']),
                       (q['lo'], (-e['hi'][0], base - e['hi'][1])), ((-e['lo'][0], base - e['lo'][1]), q['hi'])):
            if not nonneg(hi[0] - lo[0], hi[1] - lo[1]):
                raise ValueError(f'edge {n} domain/image')
        for end in (e['lo'], e['hi']):
            xp = X_on(cert, e['P'], end); xq = X_on(cert, e['Q'], (-end[0], base - end[1]))
            if not nonneg(xp[0] - xq[0], xp[1] - xq[1] - 1):
                raise ValueError(f'edge {n} does not decrease')
    owned = {}
    for e in E:
        owned.setdefault(e['P'], []).append(e)
    for i, p in enumerate(P):
        if p['target']:
            continue
        fs = [p['lo'], p['hi']] + [f for e in owned.get(i, []) for f in (e['lo'], e['hi'])]
        horizon = max([abs(f[1] - g[1]) + 2 for f, g in combinations(fs, 2)] + [1])
        for t in range(horizon + 1):
            at = lambda f: f[1] + f[0]*t
            need = set(range(at(p['lo']), at(p['hi']) + 1))
            for e in owned.get(i, []):
                need -= set(range(at(e['lo']), at(e['hi']) + 1))
            if need:
                raise ValueError(f'piece {i} uncovered at t={t}')
    return len(P), len(E)


def replay(cert, export):
    lines = Path(export).read_text().splitlines()
    tag, q, size, _ = lines[0].split()
    q = int(q); t, rem = divmod(q - cert['q0'], cert['gap'])
    if tag != 'M' or t < 0 or rem:
        raise ValueError('member off the ray')
    V = {tuple(map(int, l.split()[1:6])) for l in lines if l.startswith('V ')}
    A = {tuple(map(int, l.split()[1:])) for l in lines if l.startswith('E ')}
    if len(V) != int(size):
        raise ValueError('vertex count')
    at = lambda f: f[1] + f[0]*t
    def lab(p, k):
        s, d = p['T'][2:]; return (*p['T'][:2], k, 3*k + d, s - 6*k - d)
    where = {}
    for i, p in enumerate(cert['pieces']):
        for k in range(at(p['lo']), at(p['hi']) + 1):
            where[lab(p, k)] = i
    if not V <= set(where):
        raise ValueError('vertex outside every piece')
    checked = 0
    for e in cert['edges']:
        p, c = cert['pieces'][e['P']], cert['pieces'][e['Q']]
        for k in range(at(e['lo']), at(e['hi']) + 1):
            if lab(p, k) in V:
                if lab(p, k) + lab(c, p['T'][2] + e['dx'] - k) not in A:
                    raise ValueError(f'not an actual edge at q={q}')
                checked += 1
    return q, len(V), checked, len(where) - len(V)


if __name__ == '__main__':
    cert = parse(Path(sys.argv[1]).read_text())
    print('ORACLE_RANK_CERT_PASS pieces %d edges %d' % check(cert))
    for path in sys.argv[2:]:
        print('ORACLE_RANK_REPLAY_PASS q %d vertices %d edges_checked %d carrier_points_without_vertex %d' % replay(cert, path))
