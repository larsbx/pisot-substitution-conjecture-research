from pathlib import Path
import runpy
import pytest
ROOT=Path(__file__).resolve().parents[1]
o=runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_p_children.py'))


def test_ten_complete_stars_and_actual_typed_exits():
    p=o['probe']()
    assert p['members']==117 and p['source_cells']==1170
    assert p['image_labels']==51
    assert p['all_ten_sources_typed_coincident_within_five_steps']


def test_small_parameter_and_disjoint_controls():
    g=o['Geometry'](-1,0,0)
    with pytest.raises(ValueError):o['predicted'](10,g,0,0)
    with pytest.raises(ValueError):o['predicted'](0,g,1,3+1)
    assert not o['predicted'](4,g,2,1) # legal endpoint contact
    assert g.child(o['source'](4),3,1)==(1,2,0,0,0)
    assert len(o['path'](4,g))==4
    p=list(o['path'](0,g));i,j,w=p[1];p[1]=(0,0,w)
    with pytest.raises(ValueError):o['verify_path'](0,g,p)
    p=list(o['path'](0,g));p[-1]=(1,2,(2,1,0,0,0))
    with pytest.raises(ValueError):o['verify_path'](0,g,p)
