from pathlib import Path
import runpy
import pytest
ROOT=Path(__file__).resolve().parents[1]
o=runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_f_children.py'))


def test_eight_complete_stars_and_every_direct_F_child_exit():
    p=o['probe']()
    assert p['members']==117 and p['source_cells']==936
    assert p['image_labels']==64 and p['accepted']==20826
    assert p['path_edges']==2574 and p['direct_F_child_exit_edges']==2574
    assert p['every_direct_F_child_has_typed_tail_within_three']


def test_occurrence_target_and_geometry_controls():
    g=o['Geometry'](-1,0,0);A=g.n+g.d
    with pytest.raises(ValueError):o['predicted'](8,g,0,0)
    with pytest.raises(ValueError):o['predicted'](0,g,A+2,0)
    with pytest.raises(ValueError):o['child_exit'](2,0,g)
    with pytest.raises(ValueError):o['child_exit'](0,3,g)
    assert not o['predicted'](0,g,A-1,0)
    p=list(o['path'](0,g));p[1]=(0,0,p[1][2])
    with pytest.raises(ValueError):o['verify_packet'](o['source'](0),g,p,o['path'](0,g))
    p=list(o['child_exit'](0,1,g));p[-1]=(1,2,(2,1,0,0,0))
    with pytest.raises(ValueError):o['verify_packet'](o['source'](0),g,p,o['child_exit'](0,1,g))
    assert o['predicted'](2,g,0,0)
    g=o['Geometry'](-1,0,1)
    assert not o['predicted'](2,g,0,0)
