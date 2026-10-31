from pathlib import Path
import runpy
import pytest
ROOT=Path(__file__).resolve().parents[1]
o=runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_p3_children.py'))


def test_six_complete_stars_and_typed_exits():
    p=o['probe']()
    assert p['members']==117 and p['source_cells']==702
    assert p['image_labels']==37 and p['P3_typed_exit_at_most_two']
    assert p['path_edges']==936 and p['accepted']==17316 and p['pairs']==542880


def test_occurrence_target_geometry_and_endpoint_controls():
    g=o['Geometry'](-1,0,0);A=g.n+g.d
    with pytest.raises(ValueError):o['predicted'](6,g,0,0)
    with pytest.raises(ValueError):o['predicted'](0,g,A+2,0)
    with pytest.raises(ValueError):o['predicted'](0,g,-1,0)
    assert not o['predicted'](0,g,g.d+2,0)
    assert g.d+4==A+1
    assert o['path'](0,g)[0]==(A+1,0,o['source'](4))
    assert g.interior(o['source'](2))
    p=list(o['path'](0,g));p[0]=(A+1,0,o['source'](2))
    with pytest.raises(ValueError):o['verify_packet'](o['source'](0),g,p,o['path'](0,g))
    # Even if supplied as its own intended packet, actual word types refuse it.
    with pytest.raises(ValueError):o['verify_packet'](o['source'](0),g,p,p)
    p=list(o['path'](1,g));p[-1]=(2,1,(2,0,0,0,0))
    with pytest.raises(ValueError):o['verify_packet'](o['source'](1),g,p,o['path'](1,g))
    assert g.child(o['source'](4),A,A+1)==(2,0,0,0,0)!=o['C']
    g=o['Geometry'](-1,0,1)
    assert o['path'](0,g)[0]==(g.d+4,0,o['source'](2))
    assert g.words[0][g.d+4]==2
