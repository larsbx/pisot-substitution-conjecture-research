"""Independent CC every-first-choice and universal exact strict geometry."""
import importlib.util
from pathlib import Path
import pytest

SRC=Path(__file__).resolve().parents[1]/"oracles/python/class_a_boundary_cc_every_child.py"
spec=importlib.util.spec_from_file_location("cc_every",SRC)
o=importlib.util.module_from_spec(spec)
spec.loader.exec_module(o)


def test_every_first_choice_to_coincidence():
    r=o.probe()
    assert r["members"]==117 and r["source_cells"]==234
    assert r["pairs"]==57486
    assert r["indexed_first_choices"]==936
    assert r["composed_path_edges"]==3298
    assert r["max_full_depth"]==5
    assert r["every_first_choice_has_selected_exit"]
    assert not r["every_later_choice_productivity"]
    assert not r["universal_BH"]


def test_all_path_states_have_exact_universal_physical_margins():
    result=o.symbolic_geometry_certificate()
    assert result["base_states"]==20
    assert result["oriented_states"]==37
    assert result["strict_margins"]==74


def test_real_word_last_vs_run_endpoints():
    for k,t in ((0,0),(0,1),(1,0),(1,1),
                (2,0),(2,1),(3,0),(3,1),(6,4)):
        g=o.Geometry(-1,k,t)
        for source in o.CHILD_LABELS:
            p=o.tail(source,g)
            o.verify_path(g,source,p)
            o.verify_path(g,o.reverse(source),
                          [(j,i,o.reverse(w)) for i,j,w in p])
    g=o.Geometry(-1,0,0)
    assert o.tail(o.XC,g)[0][2][:2]==(0,0)
    assert o.tail(o.XC,o.Geometry(-1,0,1))[0][2][:2]==(0,2)
    assert len(o.tail(o.XY3,g))==4
    assert len(o.tail(o.XY3,o.Geometry(-1,1,0)))==2


def test_reject_bad_target_and_bad_index():
    g=o.Geometry(-1,0,0)
    with pytest.raises(ValueError):
        o.tail((1,2,0,0,0),g)
    path=list(o.tail(o.XY2,g))
    path[0]=(path[0][0],1000000,path[0][2])
    with pytest.raises((ValueError,AssertionError)):
        o.verify_path(g,o.XY2,path)
    with pytest.raises(AssertionError):
        o.certify_strict((0,0,0,0,50))
