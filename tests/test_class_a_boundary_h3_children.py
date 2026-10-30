from pathlib import Path
import runpy
import pytest
ROOT=Path(__file__).resolve().parents[1]
o=runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_h3_children.py'))


def test_complete_eight_source_stars_and_five_step_exits():
    p=o['probe']()
    assert p['members']==117 and p['source_cells']==936
    assert p['image_labels']==76
    assert p['path_edges']==3276
    assert p['all_sources_typed_coincident_within_five_steps']


def test_half_separator_exceptions_and_packet_controls():
    assert not o['high'](0,0) and not o['high'](1,1)
    assert o['high'](2,2) and o['high'](0,1) and not o['high'](1,0)
    g=o['Geometry'](-1,0,0)
    with pytest.raises(ValueError):o['predicted'](8,g,0,0)
    with pytest.raises(ValueError):o['predicted'](0,g,-1,0)
    p=list(o['path'](0,g));p[-1]=(1,2,(2,1,0,0,0))
    with pytest.raises(ValueError):o['verify_path'](0,g,p)
