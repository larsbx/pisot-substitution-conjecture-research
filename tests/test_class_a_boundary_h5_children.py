from pathlib import Path
import runpy
import pytest
ROOT=Path(__file__).resolve().parents[1]
o=runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_h5_children.py'))


def test_both_complete_stars_and_reversed_typed_exits():
    p=o['probe']()
    assert p['members']==117 and p['source_cells']==234
    assert p['accepted']==3042 and p['path_edges']==486
    assert p['image_labels']==30 and p['selected_typed_paths_at_most_three']


def test_strict_t_separator_and_packet_controls():
    for t,want in [(0,False),(1,False),(2,True)]:
        g=o['Geometry'](-1,4,t);A=g.n+g.d;q=A+2-g.k
        assert o['predicted'](0,g,q+2,0)==want
        assert g.interior(g.child(o['H'],q+2,0))==want
    for t,want in [(1,False),(2,True)]:
        g=o['Geometry'](-1,3,t)
        assert o['predicted'](0,g,g.n+g.d+1,0)==want
    g=o['Geometry'](-1,0,0)
    with pytest.raises(ValueError):o['predicted'](2,g,0,0)
    with pytest.raises(ValueError):o['predicted'](0,g,-1,0)
    p=list(o['path'](0,g));i,j,w=p[1];p[1]=(0,0,w)
    with pytest.raises(ValueError):o['verify_path'](0,g,p)
    p=list(o['path'](1,g));p[-1]=(1,2,(2,1,0,0,0))
    with pytest.raises(ValueError):o['verify_path'](1,g,p)
