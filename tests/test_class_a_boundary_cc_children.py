"""Exact CC four-kind child star and selected typed exit controls."""
import importlib.util
from pathlib import Path
import pytest

SRC=Path(__file__).resolve().parents[1]/"oracles/python/class_a_boundary_cc_children.py"
spec=importlib.util.spec_from_file_location("boundary_cc",SRC)
o=importlib.util.module_from_spec(spec)
spec.loader.exec_module(o)


def test_complete_oriented_stars_and_paths():
    r=o.probe()
    assert (r["members"],r["source_cells"],r["pairs"])==(117,234,57486)
    assert (r["accepted"],r["path_edges"],r["image_labels"])==(936,702,8)
    assert r["selected_depth"]==3
    assert not r["universal_BH"] and not r["all_child_productivity"]


def test_affine_symbolic_proper_prefix_certificate():
    r=o.symbolic_exit()
    assert r["universal_integer_transport"]
    assert r["actual_types_and_indices"]
    assert r["selected_path_length"]==3


def test_endpoint_and_word_legal_but_disjoint_controls():
    for k,t in ((0,0),(1,0),(0,1),(2,2),(4,3)):
        g=o.Geometry(-1,k,t)
        for flip in (0,1):
            o.verify_selected(flip,g,o.selected_path(flip,g))
            with pytest.raises(ValueError):
                o.predicted(flip,g,len(g.words[o.source(flip)[0]]),0)
        assert not o.predicted(0,g,0,0)
        assert not o.predicted(0,g,g.n+1,g.n+1)
        assert g.child(o.CC,g.n+1,2)==o.XY2
        assert g.child(o.XY2,g.d+2,0)==o.Q
        assert g.child(o.Q,1,2)==o.C
    with pytest.raises(ValueError):
        o.source(2)


def test_refuse_mutated_selected_path():
    g=o.Geometry(-1,0,0)
    p=o.selected_path(0,g)
    bad=list(p)
    bad[1]=(bad[1][0],bad[1][1],(2,0,0,-1,2))
    with pytest.raises(ValueError):
        o.verify_selected(0,g,bad)
