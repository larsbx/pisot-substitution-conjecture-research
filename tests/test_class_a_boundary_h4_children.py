"""Verify the finite H4 oracle and exact source/type negative controls."""
from pathlib import Path
import importlib.util

PATH=Path(__file__).resolve().parents[1]/"oracles/python/class_a_boundary_h4_children.py"
spec=importlib.util.spec_from_file_location("h4",PATH)
h4=importlib.util.module_from_spec(spec)
spec.loader.exec_module(h4)


def test_full_h4_exact_rational_cartesian():
    r=h4.probe()
    assert r["members"]==100
    assert r["accepted"]==1400  # sum_{k=0}^9 sum_{t=0}^9 (2t+5)
    assert r["image_labels"]==13
    assert r["pairs"]>r["accepted"]
    assert all(row["edges"]==2*row["t"]+5 for row in r["rows"])


def test_empty_and_half_chamber_guards():
    import pytest
    assert not h4.high_half(0,0)
    assert not h4.high_half(1,1)
    assert h4.high_half(2,2)
    assert h4.high_half(0,1)
    assert h4.expected(0,0,0,0) is False
    assert h4.expected(0,0,8,0) is True
    with pytest.raises(ValueError):
        h4.expected(-1,0,0,0)
    with pytest.raises(ValueError):
        h4.expected(0,0,1000,0)
