"""Exact T2 occurrence/typed exit and universal chamber guards."""
from pathlib import Path
import runpy
import pytest
o=runpy.run_path(str(Path(__file__).resolve().parents[1]/
                     "oracles/python/class_a_boundary_t2_exit.py"))

def test_universal_and_independent_finite_implementations():
    p=o["probe"]()
    assert p["members"]==117 and p["oriented_source_cells"]==234
    assert p["source_ordered_pairs"]==50700
    assert p["selected_path_edges"]==496
    assert p["symbolic"]["integer_chambers"]==4
    assert p["symbolic"]["coefficientwise_occurrence_edges"]==10
    assert p["strictness"]["oriented_states"]==13
    assert p["strictness"]["strict_margins"]==26
    assert p["selected_exit_depth_at_most"]==3
    assert p["all_first_choices_productive"] is False

def test_n4_last_c_prevents_false_typed_coincidence():
    g=o["Geometry"](-1,0,1)
    source=o["T2"]
    candidate=g.child(source,0,3)
    assert candidate==o["B"] and g.interior(candidate)
    assert g.child(candidate,1,4)==(2,1,0,0,0)
    assert g.child(candidate,1,4)!=o["C"]
    assert o["path"](0,1)[0]==(0,g.n,o["F4"])
    assert o["path"](0,0)[0]==(0,3,o["F3"])
    assert o["path"](1,1)[0]==(0,4,o["B"])

def test_bad_indices_and_recession_are_rejected():
    g=o["Geometry"](-1,0,0)
    damaged=list(o["path"](0,0))
    damaged[0]=(0,100000,o["F3"])
    with pytest.raises(ValueError):
        o["verify"](g,0,damaged)
    with pytest.raises(ValueError):
        o["path"](-1,0)
    with pytest.raises(AssertionError):
        o["CHAMBERS"][-1].nonnegative(o["Aff"](k=-1,c=1000))
