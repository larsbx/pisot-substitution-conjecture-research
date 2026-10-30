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
    assert r["selected_edges"]==5*r["members"]
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

def test_uniform_five_edge_typed_exit_samples():
    base=h4.Geometry(-1,0,0)
    path=h4.selected_path(base)
    assert [e["target"] for e in path]==[
        (2,0,1,2,-4),(2,0,-1,-2,5),(2,0,0,3,-4),
        (0,2,0,-1,1),(2,2,0,0,0)]
    for k,t in ((0,1),(1,1),(2,2),(3,0),(3,5),(9,9)):
        g=h4.Geometry(-1,k,t)
        witness=h4.selected_path(g)
        assert len(witness)==5
        assert witness[0]["i"]==2*g.n+1
        assert witness[-1]["target"]==(2,2,0,0,0)
        # The first selected H4 edge is not a mere same-letter
        # endpoint and the final child is exactly typed.
        assert all(g.interior(edge["target"]) for edge in witness)
