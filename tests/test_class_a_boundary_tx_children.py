from pathlib import Path
import runpy
import pytest
ROOT=Path(__file__).resolve().parents[1]
o=runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_tx_children.py'))


def test_six_complete_stars_and_typed_paths():
    p=o['probe']()
    assert p['members']==117 and p['source_cells']==702
    assert p['image_labels']==42 and p['max_path_length']==3
    assert p['accepted']==11674 and p['path_edges']==1872
    assert p['real_T_X_cycle_with_exit']


def test_t0_last_c_geometry_and_target_controls():
    g=o['Geometry'](-1,0,0);A=g.n+g.d
    with pytest.raises(ValueError):o['predicted'](6,g,0,0)
    with pytest.raises(ValueError):o['predicted'](0,g,A+2,0)
    assert not o['predicted'](0,g,A,0)
    # The two actual last letters are c/c, never c/y even at equal offset.
    assert g.child(o['Y0'],g.n,g.n)==(1,1,0,-2,3)
    assert g.interior((1,2,0,-2,3)) # a forged interior type still isn't the actual target
    assert o['predicted'](4,g,g.n,g.n)
    for t in(1,2):
        h=o['Geometry'](-1,0,t)
        assert not o['predicted'](4,h,h.n,h.n)
        assert o['predicted'](4,h,0,0)==(t==1)
    p=list(o['path'](0,g));p[1]=(0,0,p[1][2])
    with pytest.raises(ValueError):o['verify_packet'](0,g,p)
    p=list(o['path'](5,g));p[-1]=(1,2,(2,1,0,0,0))
    with pytest.raises(ValueError):o['verify_packet'](5,g,p)
