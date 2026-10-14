"""Bounded comparison companion to the parametric minus-branch candidate.
Reuses exact all-seed graphs; no sample fit has acceptance authority.
"""
import json
from class_d_boundary_probe import labelled_support, probe


def report():
    graphs=[labelled_support(a) for a in range(2,9)]
    if not all(g.keys()==graphs[0].keys() for g in graphs):
        raise ValueError('full labelled vertex coverage differs')
    common={k:set.intersection(*(g[k] for g in graphs)) for k in graphs[0]}
    ranks={k:0 for k in common if k[2:]==(0,0,0)}
    while True:
        new={k:1+min(ranks[c] for c in cs if c in ranks)
             for k,cs in common.items() if k not in ranks and any(c in ranks for c in cs)}
        if not new:break
        ranks.update(new)
    if len(ranks)!=len(common):raise ValueError('common graph has target-free vertices')
    return dict(authority='independent-python-oracle',canonical_execution='NOT_RUN_LOCALLY',
                family_exhaustion=False,
                minus=dict(parameters=list(range(2,9)),states=len(common),
                           edge_counts=[sum(map(len,g.values())) for g in graphs],
                           common_edges=sum(map(len,common.values())),targets=sum(v==0 for v in ranks.values()),
                           max_rank=max(ranks.values()),
                           nondecreasing_edges=sum(ranks[c]>=ranks[k] for k,cs in common.items() if ranks[k] for c in cs)),
                plus=[probe(1,a) for a in range(4,9)])


if __name__=='__main__':
    print(json.dumps(report(),indent=2))
