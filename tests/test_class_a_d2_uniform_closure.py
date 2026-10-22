"""Independent symbolic-infinite-ray d2 FIRST/RUN/LAST closure verification."""
from pathlib import Path
import importlib.util
import pytest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location(
    "uniform_d2_closure",ROOT/"oracles/python/class_a_d2_uniform_closure.py")
oracle=importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


def test_all_four_residues():
    findings=oracle.prove()
    assert [x["stats"]["gaps"] for x in findings]==[2483,2363,2483,2363]
    assert [x["stats"]["cells"] for x in findings]==[3005,2845,3005,2845]
    assert [x["stats"]["window"] for x in findings]==[1710,1602,1710,1602]
    assert sum(x["stats"]["left"]+x["stats"]["right"] for x in findings)==9692
    assert all(x["all_n_child_closure"] and not x["all_n_hitting"] for x in findings)


def test_affine_halving_and_exact_sign_controls():
    assert oracle.certificate((0,1,0,0),13)==(0,169,338,169)
    assert oracle.nonnegative((0,0,0,0),13)
    assert not oracle.nonnegative((0,-1,0,0),13)
    with pytest.raises(oracle.Undecided):
        oracle.le((2,0),(0,100),3)
    with pytest.raises(oracle.Undecided):
        oracle.endpoint(0,0,0,(1,0),0,0)


def test_actual_child_escape_after_narrowed_row():
    even=oracle.inferred(0)
    bad=even.copy()
    shortened=list(bad[0])
    shortened[-1]-=1
    bad[0]=tuple(shortened)
    with pytest.raises((oracle.Undecided,ValueError)):
        oracle.residue(bad,0)


def test_scope_and_parity_guards():
    even=oracle.inferred(0)
    with pytest.raises(ValueError):
        oracle.residue(even,4)
    with pytest.raises(ValueError):
        oracle.residue(even,0,l0=2)
    with pytest.raises(ValueError):
        oracle.residue(even,0,window=4)
    with pytest.raises(ValueError):
        oracle.residue(oracle.inferred(1),0)
