"""Independent Fraction-field calibration of the canonical Mojo graph export.

Usage: python3 oracles/python/class_a_run_index.py GRAPH.log
Rebuilds the complete graph with the existing independently written nested-
occurrence oracle; compares all labelled directed support, depths and seeds.
"""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
import json
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'reference'))
from psc_research.overlap_graph import OverlapGraph, first_left_aligned_depths


def read_export(path):
    vertices, edges, seeds, summaries = {}, [], [], []
    parameter = None
    for line in Path(path).read_text().splitlines():
        fields = line.split()
        if not fields or fields[0] not in ('V', 'E', 'SEED', 'SUMMARY'):
            continue
        tag, n, *row = fields
        n = int(n)
        if parameter is not None and n != parameter:
            raise ValueError('one complete parameter graph required')
        parameter = n
        row = tuple(map(int, row))
        if tag == 'V':
            if len(row) != 7 or row[0] in vertices:
                raise ValueError('duplicate or malformed vertex')
            vertices[row[0]] = row[1:]
        elif tag == 'E':
            if len(row) != 4:
                raise ValueError('malformed occurrence edge')
            edges.append(row)
        elif tag == 'SEED':
            seeds.append(row[0])
        else:
            summaries.append(row)
    if parameter is None or not 1 <= parameter <= 64 or len(summaries) != 1:
        raise ValueError('missing completion or invalid parameter')
    if set(vertices) != set(range(len(vertices))):
        raise ValueError('noncontiguous vertices')
    return parameter, vertices, edges, seeds, summaries[0]


@lru_cache(maxsize=4)
def reference_graph(n):
    sigma = {1:(1,)+(3,)*(n+1)+(1,),
             2:(2,)+(3,)*n+(1,),
             3:(1,)+(3,)*(n+1)+(2,)}
    g = OverlapGraph(sigma, 20000)
    if g.capped:
        raise RuntimeError('STATE_BUDGET_EXHAUSTED: no calibration verdict')
    return g


def calibrate(path):
    n, vertices, edges, seeds, summary = read_export(path)
    g = reference_graph(n)
    sigma = g.sigma
    # Interpret Mojo's integral labels in the oracle's independently scaled
    # left-eigenvector basis; no graph enumeration order is assumed.
    def state(label):
        a,b,x,c,y = label
        return a+1,b+1,tuple(sum(Fraction(w)*g.l[k][j]
                              for k,w in enumerate((x,c,y))) for j in range(3))
    states = {i:state(row[:5]) for i,row in vertices.items()}
    if len(set(states.values())) != len(states) or set(states.values()) != set(g.states):
        raise ValueError('complete labelled vertex sets differ')
    depths = first_left_aligned_depths(g)
    if any(depths[g.index[states[i]]] != row[5] for i,row in vertices.items()):
        raise ValueError('first-hit depths differ')
    if Counter(states[i] for i in seeds) != Counter(g.seeds()):
        raise ValueError('swap seeds differ')
    actual = Counter()
    choices = set()
    for src,dst,ti,bi in edges:
        if (src,ti,bi) in choices:
            raise ValueError('duplicate ordered occurrence')
        choices.add((src,ti,bi))
        a,b,t = states[src]
        if g.is_coincidence(states[src]):
            raise ValueError('terminal coincidence must not have outgoing edges')
        if not (0<=ti<len(sigma[a]) and 0<=bi<len(sigma[b])):
            raise ValueError('occurrence index outside image')
        child = (sigma[a][ti], sigma[b][bi],
                 g.F.sub(g.F.add(g.F.mul(g.F.beta,t),g.prefix[b,bi]),g.prefix[a,ti]))
        if child != states[dst] or not g.overlaps(child):
            raise ValueError('ordered geometric occurrence does not replay')
        actual[states[src],states[dst]] += 1
    expected = Counter((g.states[i],g.states[j]) for i,row in enumerate(g.adj) for j in row)
    if actual != expected:
        raise ValueError('full directed occurrence support differs')
    if summary[0] != len(states) or summary[1] != max(depths) or min(depths)<0:
        raise ValueError('complete summary disagrees')
    return dict(n=n, vertices=len(states), occurrence_edges=len(edges),
                max_first_hit=max(depths), all_labels_depths_seeds_and_edges_equal=True,
                arithmetic='independent Fraction field, rational isolation signs',
                scope='one complete finite seed graph; not universal BH')


if __name__ == '__main__':
    if len(sys.argv)!=2:
        raise SystemExit(__doc__)
    print(json.dumps(calibrate(sys.argv[1]),indent=2))
