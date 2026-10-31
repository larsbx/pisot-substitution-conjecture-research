"""All eighteen swapped-patch orientation closure and fail-closed graph lemma."""
import runpy
from pathlib import Path
import pytest
m=runpy.run_path(str(Path(__file__).resolve().parents[1]/'oracles/python/class_a_oriented_swap_closure.py'))

EXPECTED={
 (0,0):(784,0),(0,1):(1010,0),(0,2):(1220,0),(0,3):(1440,2),
 (1,0):(436,0),(1,1):(642,0),(1,2):(646,2),(1,3):(836,0),
 (2,0):(378,0),(2,1):(390,2),(2,2):(594,0),(2,3):(568,2),
 (3,0):(352,2),(3,1):(342,2),(3,2):(362,2),(3,3):(548,2),
}

def test_16_exact_completed_eighteen_swap_graphs():
    rows=m['census']()
    assert len(rows)==16
    for row in rows:
        expected=EXPECTED[(row['k'],row['t'])]
        actual=(row['full_oriented_seed_graph'],len(row['exceptional_labels']))
        assert actual==expected
        assert row['source_orientation_count']==18
        assert row['finite_graph_complete']
        assert row['conditional_set_identity']['eighteen_equals_x_plus_two_exceptions']
        assert row['all_descendants_productive_unproved']
        assert not row['universal_BH']

def test_oriented_exception_requires_two_distinct_states():
    r=m['probe'](3,0)
    assert r['full_oriented_seed_graph']==352
    assert r['forward_X_graph']==350
    assert r['exceptional_labels']==[m['R_E6'],m['E6']]
    assert len(set(m['S18']))==18
    assert m['reverse'](m['R_E6'])==m['E6']

def test_abstract_union_identity_and_all_failed_premises():
    X=m['X'];rx=m['reverse'](X);e=m['E6'];er=m['R_E6']
    u={X,rx};nine=u|{e};rnine=u|{er};whole=u|{e,er}
    r=m['oriented_closure_identity'](u,nine,rnine,whole)
    assert r['eighteen_equals_x_plus_two_exceptions']
    with pytest.raises(AssertionError):
        m['oriented_closure_identity'](u,nine,rnine,whole|{(0,2,0,0,3)})
    with pytest.raises(AssertionError):
        m['oriented_closure_identity'](u,nine,{X},whole)
    with pytest.raises(AssertionError):
        m['oriented_closure_identity']({X},nine,rnine,whole)

def test_fail_closed_for_truncated_or_malformed_input():
    g=m['Geometry'](-1,3,0)
    with pytest.raises(m['IncompleteGraph']):
        m['closure'](g,m['S18'],cap=10)
    with pytest.raises(m['IncompleteGraph']):
        m['probe'](3,0,cap=30)
    with pytest.raises(ValueError):
        m['closure'](g,[(0,0,0,0,100)],cap=6000)
    with pytest.raises(ValueError):
        m['probe'](-1,0)
