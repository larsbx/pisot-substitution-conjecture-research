"""Exact complete nine-seed graph vs X-closure, no sampled-to-universal claim."""
from pathlib import Path
import runpy
import pytest
src=runpy.run_path(str(Path(__file__).resolve().parents[1]/'oracles/python/class_a_boundary_nine_seed_scc.py'))

BASE={
 (0,0):(784,784,3,782,9,7),(0,1):(1010,1010,3,1008,9,8),
 (0,2):(1220,1220,3,1218,9,8),(0,3):(1439,1438,4,1436,10,8),
 (1,0):(436,436,3,434,6,4),(1,1):(642,642,3,640,7,6),
 (1,2):(645,644,4,642,7,5),(1,3):(836,836,3,834,7,5),
 (2,0):(378,378,3,376,6,5),(2,1):(389,388,4,386,6,4),
 (2,2):(594,594,3,592,6,5),(2,3):(567,566,4,564,6,4),
 (3,0):(351,350,4,348,5,4),(3,1):(341,340,4,338,6,4),
 (3,2):(361,360,4,358,5,4),(3,3):(547,546,4,544,6,4),
}

def test_sixteen_complete_nine_seed_graphs_and_exact_X_extension():
    rows=src['census']()
    assert len(rows)==16
    for row in rows:
        actual=tuple(row[z] for z in ('states','x_forward','sccs',
                            'x_recurrent_size','max_depth_to_x',
                            'max_depth_to_coincidence'))
        assert actual==BASE[row['k'],row['t']]
        assert row['extra_from_nine'] in ([],[src['S1']])
        # S1 is exactly E6=(x,x,0,1,0) from research PR #382.
        # 2d-1 indexed children and eight distinct base labels per
        # orientation, sixteen with true reversal; no status promotion.
        d=row['k']+2*row['t']+5
        assert row['s1_indexed_children']==2*d-1
        assert row['s1_distinct_child_labels']==8
        assert row['typed_terminals']==2
        assert row['nonproductive_sink_sccs']==0
        assert row['nonproductive_states']==0
        assert row['all_nonterminal_reach_x']
        assert row['exception_criterion']['sufficient_criterion']
        assert not row['all_seed_boundary_hitting']

def test_one_state_at_k3_t0_is_not_reachable_from_X():
    r=src['probe'](3,0)
    assert r['states']==351 and r['x_forward']==350
    assert r['extra_from_nine']==[src['S1']]
    assert r['max_depth_to_x']==5

def test_capped_or_malformed_graph_refuses_productivity_verdict():
    with pytest.raises(src['IncompleteGraph']):src['build'](0,0,cap=10)
    with pytest.raises(src['IncompleteGraph']):
        src['audit']([src['X']],[[]],{src['X']:0},complete=False)
    with pytest.raises(ValueError):
        src['audit']([src['X'],(2,2,0,0,0)],[[(2,0,0)],[]],
                     {src['X']:0,(2,2,0,0,0):1})

def test_one_exception_graph_criterion_rejects_missing_seed_or_escape():
    f=src['hub_extension_criterion']
    # X(0)->A(1), S1(2)->X: all seeds covered, closure holds.
    ok=f([[1],[],[0]],[0,2],0,2)
    assert ok['sufficient_criterion']
    # An additional direct S1 child outside Reach(X) and outside S1
    # invalidates the one-exception lemma; cannot assert coverage.
    bad=f([[1],[],[0,3],[]],[0,2],0,2)
    assert not bad['sufficient_criterion']
    # Another independent seed outside the candidate also fails.
    missing=f([[1],[],[0],[]],[0,2,3],0,2)
    assert not missing['sufficient_criterion']


def test_existing_mainline_bad_sink_oracle_rejects_false_closure():
    from types import SimpleNamespace
    bad=SimpleNamespace(states=[src['X'],src['S1'],(2,2,0,0,0)],
        adj=[[1],[1],[]],capped=False,nonproductive=lambda:[0,1])
    assert src['SCC']['nonproductive_sink_sccs'](bad)==[[1]]
    bad.capped=True
    with pytest.raises(RuntimeError):
        src['SCC']['nonproductive_sink_sccs'](bad)
