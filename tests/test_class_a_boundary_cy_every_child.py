"""Exact independent every-first-choice CY paths, including endpoint cases."""
import importlib.util
from pathlib import Path
import pytest

ROOT=Path(__file__).resolve().parents[1]
P=ROOT/"oracles/python/class_a_boundary_cy_every_child.py"
spec=importlib.util.spec_from_file_location("cy_every_child",P)
o=importlib.util.module_from_spec(spec)
spec.loader.exec_module(o)


def test_every_indexed_first_choice_on_117_members_and_reversals():
    r=o.probe()
    assert r["members"]==117
    assert r["source_cells"]==234
    assert r["pairs"]==53976
    assert r["indexed_first_children"]==6318
    assert r["composed_path_edges"]==22758
    assert r["max_first_choice_depth"]==7
    assert r["every_first_choice_productive_in_selected_continuation"]
    assert not r["all_later_choices_productive"]
    assert not r["forward_closed"]
    assert not r["universal_BH"]


def test_all_parameter_chamber_boundaries_and_real_reversals():
    specimens=((0,0),(1,0),(0,1),(1,1),(2,1),(3,1),(0,2),(2,3))
    for k,t in specimens:
        g=o.Geometry(k,t)
        for label in o.CHILD_LABELS:
            route=o.tail(label,g)
            o.verify_path(g,label,route)
            reversed_route=[(j,i,o.reverse(w)) for i,j,w in route]
            o.verify_path(g,o.reverse(label),reversed_route)
    assert len(o.tail(o.B5,o.Geometry(2,1)))==6
    assert len(o.tail(o.B4,o.Geometry(0,0)))==4
    assert len(o.tail(o.B5,o.Geometry(0,0)))==5


def test_no_wrong_terminal_or_invented_occurrence():
    g=o.Geometry(0,0)
    with pytest.raises(ValueError):
        o.tail((1,2,0,0,0),g)
    bad=list(o.tail(o.B1,g))
    bad[0]=(bad[0][0],10**6,bad[0][2])
    with pytest.raises(ValueError):
        o.verify_path(g,o.B1,bad)
    fake=list(o.tail(o.B2,g))
    fake[-1]=(fake[-1][0],fake[-1][1],(2,1,0,0,0))
    with pytest.raises(AssertionError):
        o.verify_path(g,o.B2,fake)
