"""Source-specific finite SCC auditing: complete graphs only, no universal BH."""
from class_a_boundary_four_seed_scc import (
    X,Y0,CY,CC,C,build,probe,census,audit_graph,IncompleteGraph)
import pytest

# Deterministic exact original-Fraction oracle regression, finite grid only.
EXPECTED={
 (0,0):(784,3,782,0,9,7), (0,1):(1012,5,1008,2,9,8),
 (0,2):(1223,6,1218,3,9,8),(0,3):(1441,6,1436,3,10,8),
 (1,0):(436,3,434,0,6,4),(1,1):(645,6,640,3,7,6),
 (1,2):(644,3,642,0,7,5),(1,3):(839,6,834,3,7,5),
 (2,0):(378,3,376,0,6,5),(2,1):(391,6,386,3,6,4),
 (2,2):(594,3,592,0,6,5),(2,3):(569,6,564,3,6,4),
 (3,0):(350,3,348,0,5,4),(3,1):(343,6,338,3,6,4),
 (3,2):(360,3,358,0,5,4),(3,3):(549,6,544,3,6,4)
}

def test_16_complete_exact_graphs_X_is_productive_hub():
    rows=census()
    assert len(rows)==16
    for r in rows:
        actual=(r['states'],r['sccs'],r['nonterminal_x_scc'],
                r['other_nonterminal'],r['max_depth_to_X'],r['max_depth_to_coincidence'])
        assert actual==EXPECTED[(r['k'],r['t'])]
        assert r['typed_terminals']==2
        assert r['sink_sccs']==2
        assert r['recurrent_sccs']==1
        assert r['bad_sink_sccs']==0
        assert r['all_nonterminal_reach_X']
        assert r['all_states_productive']
        assert not r['universal_BH']

def test_reject_any_capped_graph_or_malformed_edge():
    with pytest.raises(IncompleteGraph):
        build(0,0,cap=10)
    with pytest.raises(IncompleteGraph):
        audit_graph([X,C],[[(1,0,0)],[]],{X:0,C:1},complete=False)
    with pytest.raises(ValueError):
        audit_graph([X,C],[[(2,0,0)],[]],{X:0,C:1})

def test_closed_nonproductive_sink_is_detected_not_misreported():
    bad=(0,2,2,-2,0)
    states=[X,bad,C]
    edges=[[(1,0,0)],[(1,0,0)],[]]
    r=audit_graph(states,edges,{s:i for i,s in enumerate(states)})
    assert r['bad_sink_sccs']==1
    assert not r['all_states_productive']
    assert not r['all_nonterminal_reach_X']

def test_productive_cycle_does_not_prove_every_edge_terminates():
    states=[X,Y0,C]
    edges=[[(1,1,0),(2,2,1)],[(0,0,1)],[]]
    r=audit_graph(states,edges,{s:i for i,s in enumerate(states)})
    assert r['recurrent_sccs']==1
    assert r['all_nonterminal_reach_X']
    assert r['all_states_productive']
    # X<->Y0 is still a perpetual noncoincident path under arbitrary choices.
    assert r['nonterminal_x_scc']==2
