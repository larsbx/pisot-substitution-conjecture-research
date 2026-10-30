"""Independent exact-arithmetic lower-strip oracle: literal word prefix sweep.

Uses the existing separately written Fraction field/sign oracle, not Mojo's
symbolic polynomials, brackets, run fitting, PIP screen or graph closure.
Integer label transport and ordered literal child intervals are built here.
A state cap or any mismatch aborts. This is a finite cross-check, never a
universal certificate. Usage: python ... EPS D N [native-row-log].
"""
from collections import deque
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'reference'))
from psc_research.overlap_graph import Field, charpoly, left_perron_lengths


def run(eps, d, n, native=None):
    if eps not in (-1, 1) or not 6 <= d <= 64 or not 0 <= n <= 400:
        raise ValueError('finite oracle budget/sign')
    start = 2*d + (-5 if eps == 1 else 1)
    if n < start:
        raise ValueError('outside the independently proved PIP domain')
    sigma = {1: (1,)+(3,)*(n+d)+(1,),
             2: (2,)+(3,)*n+(1,),
             3: (2,)+(3,)*(n-d+eps)+(2,)}
    assert charpoly(sigma) == (n-d+eps+3, n-3*d+3*eps+2, 2*eps)
    field = Field(*charpoly(sigma))
    lengths = left_perron_lengths(sigma, field)
    zero = (0, 0, 0)
    unit = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
    add = lambda a,b: tuple(x+y for x,y in zip(a,b))
    sub = lambda a,b: tuple(x-y for x,y in zip(a,b))
    cache = {zero: 0}

    def sign(w):
        if w not in cache:
            elt = tuple(sum((w[i]*lengths[i][k] for i in range(3)), Fraction()) for k in range(3))
            cache[w] = field.sign(elt)
        return cache[w]

    prefixes = {}
    for a, word in sigma.items():
        p = [zero]
        for c in word:
            p.append(add(p[-1], unit[c-1]))
        prefixes[a] = p
    M = [[prefixes[j+1][-1][i] for j in range(3)] for i in range(3)]
    inflate = lambda w: tuple(sum(M[i][j]*w[j] for j in range(3)) for i in range(3))
    real = lambda a,b,w: sign(add(w,unit[b-1])) > 0 and sign(sub(unit[a-1],w)) > 0

    def children(state):
        a,b,w = state
        if a == b and w == zero:
            return ()
        shift = inflate(w)
        i = j = 0
        out = set()
        while i < len(sigma[a]) and j < len(sigma[b]):
            ca, cb = sigma[a][i], sigma[b][j]
            t = sub(add(shift, prefixes[b][j]), prefixes[a][i])
            if real(ca,cb,t):
                out.add((ca,cb,t))
            # Difference of right endpoints: bottom minus top. Advance the
            # earlier end (both if equal); no possible intersection is skipped.
            end = sign(sub(add(t,unit[cb-1]),unit[ca-1]))
            if end >= 0:
                i += 1
            if end <= 0:
                j += 1
        return tuple(sorted(out))

    seeds = set()
    for a in range(1,4):
        for b in range(a+1,4):
            for ta,pa in ((a,zero),(b,unit[a-1])):
                for tb,pb in ((b,zero),(a,unit[b-1])):
                    w = sub(pb,pa)
                    if real(ta,tb,w):
                        seeds.add((ta,tb,w))
    graph = {}
    todo = deque(sorted(seeds))
    while todo:
        state = todo.popleft()
        if state in graph:
            continue
        if len(graph) >= 20000:
            raise RuntimeError('STATE_BUDGET_EXHAUSTED')
        graph[state] = children(state)
        todo.extend(c for c in graph[state] if c not in graph)
    reverse = {s: [] for s in graph}
    for s, edges in graph.items():
        for c in edges:
            reverse[c].append(s)
    depths = {s: 0 for s in graph if s[2] == zero}
    todo = deque(depths)
    while todo:
        c = todo.popleft()
        for s in reverse[c]:
            if s not in depths:
                depths[s] = depths[c]+1
                todo.append(s)
    assert len(depths) == len(graph), 'complete graph has a non-hitting vertex'
    keyed = sorted((a-1,b-1,sum(w),w[2],w[0]) for a,b,w in graph)
    rows = []
    for a,b,s,y,k in keyed:
        if rows and rows[-1][:4] == [a,b,s,y] and rows[-1][5]+1 == k:
            rows[-1][5] = k
        else:
            rows.append([a,b,s,y,k,k])
    rowtext = ''.join('R '+' '.join(map(str,r))+'\n' for r in rows)
    if native:
        expected = ''.join(line+'\n' for line in Path(native).read_text().splitlines() if line.startswith('R '))
        assert expected == rowtext, 'native/oracle label set mismatch'
    encoded = json.dumps([(s,graph[s]) for s in sorted(graph)], separators=(',',':')).encode()
    return dict(eps=eps,d=d,n=n,vertices=len(graph),edges=sum(map(len,graph.values())),
                max_depth=max(depths.values()),rows=len(rows),
                rows_sha256=hashlib.sha256(rowtext.encode()).hexdigest(),
                graph_sha256=hashlib.sha256(encoded).hexdigest(),
                native_rows_checked=bool(native),sign_vectors=len(cache))


def domain():
    from psc_research.pisot_screen import screen, irreducibility, REFUSED
    counts, refused = {}, []
    for eps in [1, -1]:
        for d in range(6, 65):
            start = 2*d + (-5 if eps == 1 else 1)
            for n in range(d-eps, 4*d+9):
                poly = [-2*eps, n-3*d+3*eps+2, -(n-d+eps+3), 1]
                status = screen(poly)
                ir = irreducibility(poly)
                counts[status] = counts.get(status, 0)+1
                if status == REFUSED:
                    refused.append([eps,d,n])
                else:
                    assert (status == 'pisot' and ir == 'irreducible') == (n >= start)
    return dict(counts=counts,refused=refused,mismatches=[])


if __name__ == '__main__':
    if sys.argv[1:] == ['domain']:
        result = domain()
    else:
        result = run(*map(int,sys.argv[1:4]),sys.argv[4] if len(sys.argv)>4 else None)
    print(json.dumps(result,sort_keys=True))
