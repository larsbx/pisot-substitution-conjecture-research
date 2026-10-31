"""All-target conditional X composition with true words, exact source pins."""
from pathlib import Path
import hashlib
import runpy
import pytest

ROOT=Path(__file__).resolve().parents[1]
OR=ROOT/"oracles/python"
o=runpy.run_path(str(OR/"class_a_boundary_x_first_choice_composition.py"))

# Keep recovered paths byte-identical to their source PR heads.
EXPECTED_BLOBS={
    "class_a_boundary_t2_exit.py":"e14a3bafd41dbad50fe18c0cd1fcaa31a0339a06",
    "class_a_boundary_three_exit_recovery.py":"eacb52a07e854eb76b8d895ee563e80447523bc8",
    "class_a_boundary_b4_r4_exit_recovery.py":"260733a49b0ec54f43f7d4299fd31feea3841007",
}
def git_sha(data):
    return hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()

def test_exact_historical_source_revision_pins():
    for name,expected in EXPECTED_BLOBS.items():
        assert git_sha((OR/name).read_bytes())==expected

def test_ten_oriented_source_labels_and_external_status():
    r=o["conditional_certificate"]()
    assert r["source"]["base_labels"]==10
    assert r["existing_selected_exit_sources"]==4
    assert r["research_only_selected_exit_sources"]==6
    assert r["conditional_X_first_choice_depth"]==6
    assert not r["mainline_X_first_choice_accepted"]
    assert not r["universal_BH"]
    assert set(r["cited_candidate_PRs"])=={420,424,425}

def test_all_exact_first_choices_and_completed_typed_walks():
    r=o["probe"]()
    assert r["members"]==117 and r["oriented_source_cells"]==234
    assert r["pairs"]==297648
    assert r["indexed_first_choices"]==6786
    assert r["composed_edges"]==24468
    assert r["max_depth"]==6
    assert r["depth_histogram"]=={2:234,3:2650,4:3668,5:26,6:208}
    assert not r["forward_closed"] and not r["universal_BH"]

def test_n3_last_run_type_and_forged_path_refusals():
    g=o["Geometry"](-1,0,0)
    real={(i,j) for i in range(g.n+g.d+2)
                   for j in range(g.n+g.d+2) if o["x_guard"](g,i,j)}
    assert len(real)==2*g.n+3
    labelset={g.child(o["X"],i,j) for i,j in real}
    assert len(labelset)==9 and (2,2,1,-1,-2) not in labelset
    h=o["Geometry"](-1,1,0)
    image={h.child(o["X"],i,j) for i in range(h.n+h.d+2)
           for j in range(h.n+h.d+2) if o["x_guard"](h,i,j)}
    assert len(image)==10
    with pytest.raises(ValueError):
        o["x_guard"](g,10**6,0)
    with pytest.raises(AssertionError):
        o["verify"](g,o["X"],[(g.d+1,0,(2,0,0,-1,2)),(1,2,o["C"])])
