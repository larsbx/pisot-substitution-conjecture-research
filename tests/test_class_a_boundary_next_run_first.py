"""Regress true first/run/first geometric hits against independent oracle."""
import importlib.util
from pathlib import Path

PATH=Path(__file__).resolve().parents[1]/"oracles/python/class_a_boundary_next_run_first.py"
spec=importlib.util.spec_from_file_location("boundary_run_first",PATH)
obj=importlib.util.module_from_spec(spec)
spec.loader.exec_module(obj)


def test_run_first_complete_rational_replay():
    r=obj.probe()
    assert r["members"]==320
    assert r["cells"]==640
    assert r["ordinals"]>0 and r["accepted"]>0
    for row in r["rows"]:
        eps,k,t,m=row["eps"],row["k"],row["t"],row["m"]
        n=k+3+t if eps==-1 else 2*(k+2)+t
        assert row["indices"]==sorted(obj.expected(eps,k,t,m,n))


def test_reject_invalid_source():
    import pytest
    with pytest.raises(ValueError):
        obj.expected(1,4,0,3,12)
