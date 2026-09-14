"""EXPLORATORY (not a certificate).  For specimens where no short prefix of
one fixed point gave type inclusion of the Sirvent--Solomyak overlap types
into the seed-patch vertex types, probe: (a) longer prefixes up to kmax;
(b) every prolongable (power, letter) fixed point; (c) the full family over
all prefixes W (return-translate family) -- whether its closure is productive
and how it relates to the seed-patch graph.  Usage: python3 ... <listfile>"""
import sys, ast, time
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parents[1] / 'src'))
from psc_research.oa_overlap_graph import fixed_point_prefix, oa_types
from psc_research.overlap_graph import OverlapGraph

def all_prolongable(sigma):
    first = {a: sigma[a][0] for a in sigma}
    out = []
    for q in range(1, len(sigma) + 1):
        for c in sorted(sigma):
            x = c
            for _ in range(q):
                x = first[x]
            if x == c:
                out.append((q, c))
    return out

specs = [ast.literal_eval(l) for l in open(sys.argv[1]) if l.strip()]
kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 24
for sigma in specs:
    t0 = time.time()
    g = OverlapGraph(sigma)
    seed = {s for s in g.states if not OverlapGraph.is_coincidence(s)}
    report = {"sigma": sigma, "seed_noncoinc_types": len(seed)}
    best = None
    union = set()
    for (q, c) in all_prolongable(sigma):
        u = fixed_point_prefix(sigma, q, c, 6000)
        for k in range(1, kmax + 1):
            oa = {s for s in oa_types(g, u, k, 14 + k) if not OverlapGraph.is_coincidence(s)}
            union |= oa
            miss = len(oa - seed)
            if miss == 0 and best is None:
                best = (q, c, k)
    # productivity of the union closure and relation to the seed-patch graph
    good = set()
    closure = set()
    from collections import deque
    queue = deque(union)
    while queue:
        s = queue.popleft()
        if s in closure: continue
        closure.add(s)
        queue.extend(g.children(s))
    coinc = {s for s in closure if OverlapGraph.is_coincidence(s)}
    good = set(coinc); changed = True
    while changed:
        changed = False
        for s in closure:
            if s not in good and any(c in good for c in g.children(s)):
                good.add(s); changed = True
    nc = {s for s in closure if not OverlapGraph.is_coincidence(s)}
    report.update({"first_inclusion_(q,c,k)": best, "union_noncoinc_types": len(nc),
                   "union_minus_seed": len(nc - seed), "seed_minus_union": len(seed - nc),
                   "union_all_productive": all(s in good for s in nc), "secs": round(time.time() - t0)})
    print(report, flush=True)
