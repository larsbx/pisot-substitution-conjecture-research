"""Finite exact-rational H5 descendant and terminal regression."""
import importlib.util
from pathlib import Path

PATH=Path(__file__).resolve().parents[1]/"oracles/python/class_a_boundary_h5_exit.py"
spec=importlib.util.spec_from_file_location("h5",PATH)
h5=importlib.util.module_from_spec(spec)
spec.loader.exec_module(h5)


def test_h5_all_k_branch_replay():
    r=h5.probe()
    assert r["members"]==108
    assert r["k0_three_steps"]==9
    assert r["other_two_steps"]==99
    assert all(q["depth"]==(3 if q["k"]==0 else 2) for q in r["rows"])
    assert all(q["steps"][-1]["target"]==(2,2,0,0,0) for q in r["rows"])


def test_exact_target_and_bad_indices():
    import pytest
    with pytest.raises(ValueError):
        h5.H5_path(-1,0)
    with pytest.raises(ValueError):
        h5.H5_path(1,-1)
    for k,t in [(0,0),(0,3),(1,0),(2,0),(2,5),(9,3)]:
        r=h5.H5_path(k,t)
        assert r["steps"][0]["i"]==(r["n"]+r["d"]+1 if k<=1 else 2*r["d"]-r["n"]+3)
        assert r["steps"][0]["j"]==0
        assert r["steps"][-1]["target"]==(2,2,0,0,0)
