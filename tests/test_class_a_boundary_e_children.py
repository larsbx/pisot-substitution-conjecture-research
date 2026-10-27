from pathlib import Path
import runpy
import pytest

ROOT=Path(__file__).resolve().parents[1]
o=runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_e_children.py'))


def test_complete_six_source_stars_and_short_coincidence_paths():
    p=o['probe']()
    assert p['members']==117
    assert p['source_cells']==702
    assert p['every_member_image_labels']==29
    assert p['path_edges']==1170
    assert p['all_six_sources_typed_coincident_in_at_most_two_steps']


def test_packet_index_and_target_controls():
    g=o['Geometry'](-1,0,0)
    with pytest.raises(ValueError): o['predicted'](6,g,0,0)
    with pytest.raises(ValueError): o['predicted'](2,g,-1,0)
    p=list(o['short_path'](1,g)); p[-1]=(1,2,(2,1,0,0,0))
    with pytest.raises(ValueError): o['verify_path'](1,g,p)
