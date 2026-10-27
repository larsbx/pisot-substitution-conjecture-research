from pathlib import Path
import runpy
import pytest

ROOT=Path(__file__).resolve().parents[1]
o=runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_w_children.py'))


def test_complete_four_source_carrier_and_minus_seed_path():
    p=o['probe']()
    assert p['members']==117
    assert p['source_cells']==468
    assert p['image_labels']==17
    assert p['path_edges']==702
    assert p['every_seed_path_typed_coincident']


def test_false_coincidence_and_unavailable_occurrence_controls():
    assert not o['typed_coincidence']((1,2,0,0,0))
    g=o['Geometry'](-1,0,0)
    with pytest.raises(ValueError):
        o['predicted'](0,g,5,0)
    bad=list(o['path'](g)); source,i,j,target=bad[-1]
    bad[-1]=(source,i,j,(1,2,0,0,0))
    with pytest.raises(ValueError):
        o['verify_path'](g,bad)
