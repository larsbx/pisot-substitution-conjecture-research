"""Exact Y0 every-first-choice proof regression and refusal controls."""
from pathlib import Path
import runpy
import pytest

ROOT=Path(__file__).resolve().parents[1]
O=runpy.run_path(str(ROOT/"oracles/python/class_a_boundary_y0_every_child.py"))
S=runpy.run_path(str(ROOT/"oracles/python/class_a_boundary_y0_symbolic_transport.py"))


def test_all_indexed_first_choices_have_actual_typed_tails():
    r=O["probe"]()
    assert r["members"]==117 and r["source_cells"]==234
    assert r["pairs"]==50700
    assert r["accepted_indexed_first_choices"]==4654
    assert r["composed_path_edges"]==12920
    assert r["selected_max_depth"]==6
    assert r["chamber_union_child_labels"]==10
    assert r["every_first_choice_selected_exit"]
    assert r["universal_BH"] is False


def test_exact_affine_zkt_all_six_chambers_and_forty_paths():
    r=S["prove_all_affine_occurrences"]()
    assert r["integer_chambers"]==6
    assert r["complete_source_target_cases"]==40
    assert r["checked_occurrence_edges"]==139
    assert r["maximum_source_depth"]==6
    assert r["full_Z_k_t_Parikh_identities"]
    assert r["all_word_bounds_and_actual_types"]


def test_exact_rational_45_label_physical_strictness():
    r=O["strict_path_certificate"]()
    assert r["base_labels"]==26
    assert r["oriented_labels"]==45
    assert r["universal_exact_strict_margins"]==90


def test_endpoint_types_and_eligible_parameter_splits():
    Geometry=O["Geometry"]
    for k,t in ((0,0),(1,0),(0,1),(1,1),(0,2),(1,2),(4,7)):
        g=Geometry(-1,k,t)
        for i,j,w in g.edges(O["Y0"]):
            path=[(i,j,w)]+O["tail"](w,g)
            O["verify"](g,O["Y0"],path)
            O["verify"](g,O["reverse"](O["Y0"]),
                        [(b,a,O["reverse"](z)) for a,b,z in path])
        assert (O["CC"] in {w for _,_,w in g.edges(O["Y0"])})==(t==0)
    n3=Geometry(-1,0,0)
    assert O["tail"](O["D2"],n3)[0][2][:2]==(0,2)
    assert O["tail"](O["D2"],Geometry(-1,1,0))==[(1,3,O["C"])]
    assert len(O["tail"](O["A4"],Geometry(-1,0,1)))==5
    assert len(O["tail"](O["CY3"],Geometry(-1,0,2)))==5
    assert len(O["tail"](O["CY3"],Geometry(-1,1,2)))==3
    assert len(O["tail"](O["K5"],Geometry(-1,0,2)))==3
    assert len(O["tail"](O["K5"],Geometry(-1,1,2)))==2


def test_corrupted_ordinal_and_wrong_target_refused():
    g=O["Geometry"](-1,0,0)
    with pytest.raises(ValueError):
        O["tail"]((0,2,0,0,0),g)
    p=O["tail"](O["CY"],g)
    bad=list(p)
    i,j,w=bad[0]
    bad[0]=(i,100000,w)
    with pytest.raises(ValueError):
        O["verify"](g,O["CY"],bad)
    forged=list(p)
    forged[-1]=(forged[-1][0],forged[-1][1],(2,1,0,0,0))
    with pytest.raises(AssertionError):
        O["verify"](g,O["CY"],forged)
    with pytest.raises(AssertionError):
        S["CHAMBERS"][-1].nonnegative(S["Aff"](-1,0,1000))
    with pytest.raises(AssertionError):
        O["certify_strict"]((0,0,0,0,100))
