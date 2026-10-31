"""All eight E6 image labels have uniform X-paths, with precise boundaries."""
from pathlib import Path
import runpy
import pytest
src=runpy.run_path(str(Path(__file__).resolve().parents[1]/
    'oracles/python/class_a_x_to_e6_children.py'))

def test_exact_symbolic_two_chamber_closure_certificate():
    r=src['symbolic_certificate']()
    assert r['chambers']==2
    assert r['source_chamber_cases']==16
    assert r['typed_E6_targets']==8
    assert r['exact_symbolic_oriented_path_edges']==108
    assert r['max_X_to_E6_child_depth']==5
    assert r['distinct_path_labels']==28
    assert r['universal_strict_margins']==56
    assert r['all_descendants_productive_unproved']
    assert not r['BH'] and not r['PSC']

def test_original_exact_fraction_complete_e6_stars_and_forward_paths():
    r=src['finite_oracle']()
    assert r['specimens']==117
    assert r['E6_candidate_pairs']==297648
    assert r['strict_indexed_E6_children_both_orientations']==8658
    assert r['X_to_E6_child_selected_edge_replays']==6864

def test_uniform_word_run_last_star_and_no_e6_self_child():
    # Same eight typed labels simultaneously at every member. 
    for k,t in ((0,0),(0,1),(1,0),(1,2),(2,0),(3,3)):
        g=src['Geometry'](-1,k,t)
        star={(i,j,g.child(src['E6'],i,j))
            for i in range(g.n+g.d+2) for j in range(g.n+g.d+2)
            if src['e6_predicted'](g,i,j)}
        assert len(star)==2*g.d-1
        assert {w for i,j,w in star}==src['E6_IMAGE']
        assert src['E6'] not in {w for i,j,w in star}
        assert g.words[0][g.n+g.d+1]==0
        assert g.words[0][g.d-3]==2

def test_t0_vs_positive_t_paths_preserve_actual_letters():
    g=src['Geometry'](-1,0,0)
    h=src['Geometry'](-1,0,1)
    label=(0,2,1,1,-4)
    assert len(src['path'](label,src['CHAMBERS']['t0']))==3
    assert len(src['path'](label,src['CHAMBERS']['t1plus']))==5
    for param,geom in ((0,g),(1,h)):
        ch=src['CHAMBERS']['t0' if param==0 else 't1plus']
        state=src['X']
        for aa,bb,target in src['path'](label,ch):
            i=aa.k*0+aa.t*param+aa.c
            j=bb.k*0+bb.t*param+bb.c
            assert geom.child(state,i,j)==target
            state=target
        assert state==label

def test_bad_index_and_corrupt_typed_target_are_rejected():
    g=src['Geometry'](-1,0,0)
    with pytest.raises(ValueError):
        src['e6_predicted'](g,g.n+g.d+2,0)
    with pytest.raises(ValueError):
        src['path']((0,0,0,0,0),src['CHAMBERS']['t0'])
    with pytest.raises(AssertionError):
        src['certify_edge'](src['X'],src['Aff'](k=-1,c=1000),0,
                            (2,0,0,-1,0),src['CHAMBERS']['t1plus'])
    with pytest.raises(AssertionError):
        src['base']['strict']((0,0,0,0,999))
