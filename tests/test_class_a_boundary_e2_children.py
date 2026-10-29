from pathlib import Path
import runpy
import pytest
ROOT=Path(__file__).resolve().parents[1]
o=runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_e2_children.py'))


def test_four_complete_stars_and_five_step_exits():
    p=o['probe']()
    assert p['members']==117 and p['source_cells']==468
    assert p['image_labels']==46 and p['path_edges']==2106
    assert p['all_four_sources_typed_coincident_within_five_steps']


def test_endpoint_and_typed_geometry_controls():
    g=o['Geometry'](-1,0,0);A=g.n+g.d
    assert set(g.edges(o['source'](0)))=={(A+1,0,o['source'](2))}
    with pytest.raises(ValueError):o['predicted'](4,g,0,0)
    with pytest.raises(ValueError):o['predicted'](0,g,A+2,0)
    p=list(o['path'](0,g));p[0]=(A+1,0,o['J'])
    with pytest.raises(ValueError):o['verify_path'](0,g,p)
    p=list(o['path'](0,g));i,j,w=p[1];p[1]=(0,0,w)
    with pytest.raises(ValueError):o['verify_path'](0,g,p)
    p=list(o['path'](0,g));p[-1]=(1,2,(2,1,0,0,0))
    with pytest.raises(ValueError):o['verify_path'](0,g,p)
    for k,t,expected in [(0,3,True),(4,3,False)]:
        g=o['Geometry'](-1,k,t)
        assert o['predicted'](0,g,g.n+g.d+1,0)==expected
