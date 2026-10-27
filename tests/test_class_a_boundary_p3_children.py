from pathlib import Path
import runpy
import pytest
ROOT=Path(__file__).resolve().parents[1]
o=runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_p3_children.py'))


def test_complete_oriented_stars_and_typed_paths():
    p=o['probe']()
    assert p['members']==117 and p['source_cells']==234
    assert p['image_labels']==26 and p['max_path_length']==4
    assert p['accepted']==5382 and p['path_edges']==472


def test_endpoints_occurrence_target_and_disjoint_controls():
    g=o['Geometry'](-1,0,0);A=g.n+g.d
    with pytest.raises(ValueError):o['predicted'](2,g,0,0)
    with pytest.raises(ValueError):o['predicted'](0,g,A+2,0)
    assert o['predicted'](0,g,A+1,0)
    # The proposed shorter Q exit is LAST x at n=3, not RUN y.
    assert g.d+4==A+1 and g.child(o['P3'],g.d+4,0)!=o['Q']
    p=[(g.d+4,0,o['Q']),(1,2,o['C'])]
    with pytest.raises(ValueError):o['verify_packet'](0,g,p)
    assert not o['predicted'](0,g,g.d+2,0)
    p=list(o['path'](0,g));p[1]=(0,0,p[1][2])
    with pytest.raises(ValueError):o['verify_packet'](0,g,p)
    p=list(o['path'](1,g));p[-1]=(2,1,(2,1,0,0,0))
    with pytest.raises(ValueError):o['verify_packet'](1,g,p)
    for t in(2,3):
        g=o['Geometry'](-1,0,t);A=g.n+g.d
        assert o['predicted'](0,g,A+1,0)==(t==2)
