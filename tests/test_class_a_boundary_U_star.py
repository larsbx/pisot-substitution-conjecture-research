"""Exact finite independent U outgoing star, no universal BH."""
from pathlib import Path
import importlib.util

PATH=Path(__file__).resolve().parents[1]/"oracles/python/class_a_boundary_U_star.py"
spec=importlib.util.spec_from_file_location("Ustar",PATH)
m=importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


def test_U_oracle_full_cartesian():
    r=m.probe()
    assert r["members"]==72
    assert r["labels"]==12
    assert r["pairs"]>r["accepted"]>0
    for row in r["results"]:
        assert row["edges"]==2*row["n"]-1


def test_invalid_run_indices():
    import pytest
    with pytest.raises(ValueError):
        m.expected(0,0,99,0)
    with pytest.raises(ValueError):
        m.expected(-1,0,0,0)
    assert not m.expected(0,0,0,0)
    assert not m.expected(0,0,8,3)
