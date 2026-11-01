"""Exact reversal-orbit quotient with liftable occurrence provenance."""
from pathlib import Path
import runpy
import pytest

m=runpy.run_path(str(Path(__file__).resolve().parents[1] /
                     'oracles/python/class_a_reversal_quotient.py'))

# Strict complete X and full 18-orientation closures; do not extrapolate.
COUNTS={
 (0,0):(784,393,784,393),
 (0,1):(1010,506,1010,506),
 (0,2):(1220,611,1220,611),
 (0,3):(1438,720,1440,721),
 (1,0):(436,219,436,219),
 (1,1):(642,322,642,322),
 (1,2):(644,323,646,324),
 (1,3):(836,419,836,419),
 (2,0):(378,190,378,190),
 (2,1):(388,195,390,196),
 (2,2):(594,298,594,298),
 (2,3):(566,284,568,285),
 (3,0):(350,176,352,177),
 (3,1):(340,171,342,172),
 (3,2):(360,181,362,182),
 (3,3):(546,274,548,275),
}

def test_every_complete_finite_x_graph_exact_quotient_and_coincidence_lifts():
    for (k,t),(original,quotient,_,_) in COUNTS.items():
        r=m['analyze'](k,t,scope='X')
        assert (r['actual_vertices'],r['quotient_vertices'])==(original,quotient)
        assert r['quotient_sccs']==3 and r['quotient_recurrent_sccs']==1
        assert r['x_quotient_scc']==quotient-2
        assert r['fixed_typed_terminals']==2
        assert r['actual_indexed_edges']==2*r['quotient_indexed_edges']
        assert r['quotient_nonproductive_orbits']==r['actual_nonproductive_vertices']==0
        assert r['all_states_productive'] and not r['universal_X_productivity']


def test_eighteen_seed_orientation_graphs_and_exact_extra_orbit():
    for (k,t),(x,_q,original,q) in COUNTS.items():
        r=m['analyze'](k,t,scope='S18')
        assert (r['actual_vertices'],r['quotient_vertices'])==(original,q)
        assert r['quotient_sccs']==(3 if original==x else 4)
        assert r['x_quotient_scc']==_q-2
        assert r['quotient_recurrent_sccs']==1
        assert r['actual_indexed_edges']==2*r['quotient_indexed_edges']
        assert r['all_states_productive'] and not r['universal_X_productivity']


def test_actual_lift_from_either_reversal_orientation_and_shortest_paths():
    for k,t in ((0,0),(1,2),(3,0)):
        g=m['Geometry'](-1,k,t)
        states,ids,edges=m['raw']['closure'](g,[m['X']],cap=5000)
        q=m['quotient'](states,ids,edges)
        terminals=[i for i,w in enumerate(q['labels']) if m['coincidence'](w)]
        dist,chosen=m['reverse_distances'](q['adj'],terminals)
        for state in states:
            path=m['target_path'](q,q['ids'][m['canonical'](state)],chosen)
            walk=m['lift'](g,q,state,path)
            assert len(walk)==dist[q['ids'][m['canonical'](state)]]
            assert m['coincidence'](walk[-1][2] if walk else state)
            rev=m['reverse'](state)
            rp=m['lift'](g,q,rev,path)
            assert rp==[(j,i,m['reverse'](target)) for i,j,target in walk]


def test_nonproductive_cycle_is_not_accidentally_certified():
    a=m['X'];b=m['reverse'](a);c=(2,2,0,0,0)
    states=[a,b,c];ids={s:i for i,s in enumerate(states)}
    edges=[[(0,0,0)],[(1,0,0)],[]]
    q=m['quotient'](states,ids,edges)
    dist,_=m['reverse_distances'](q['adj'],[q['ids'][c]])
    assert len(q['labels'])==2 and len(dist)==1
    assert q['ids'][m['canonical'](a)] not in dist


def test_reversal_edge_and_word_index_refusals():
    a=m['X'];b=m['reverse'](a);c=(2,2,0,0,0)
    states=[a,b,c];ids={s:i for i,s in enumerate(states)}
    with pytest.raises(m['InvalidReversalGraph']):
        m['quotient'](states,ids,[[(2,0,0)],[],[]])
    with pytest.raises(m['InvalidReversalGraph']):
        m['quotient'](states,ids,[[(2,0,0)],[(2,1,0)],[]])
    with pytest.raises(m['InvalidReversalGraph']):
        m['quotient'](states,ids,[[(2,0,0),(2,0,0)],[(2,0,0)],[]])
    with pytest.raises(m['InvalidReversalGraph']):
        m['quotient'](states[:2],{a:0,b:1},[[(0,0,0)],[(1,0,0)],[(0,1,0)]])
    g=m['Geometry'](-1,3,0)
    with pytest.raises(m['IncompleteGraph']):
        m['raw']['closure'](g,[m['X']],cap=10)
    states,ids,edges=m['raw']['closure'](g,[m['X']])
    q=m['quotient'](states,ids,edges)
    with pytest.raises(m['InvalidReversalGraph']):
        m['lift'](g,q,m['X'],[(q['ids'][m['canonical'](m['X'])],(0,123456,0))])
