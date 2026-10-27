import runpy
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
oracle = runpy.run_path(str(ROOT / "oracles/python/class_a_boundary_u_children.py"))


def test_complete_U_carrier_and_actual_four_cycle():
    data = oracle["probe"]()
    assert data["members"] == 117
    assert data["image_labels"] == 12
    assert data["four_cycle_members"] == 114
    assert data["V_pairs"] == data["pairs"]
    assert data["V_accepted"] == data["members"]
    assert data["V_unique_child"] == [1,0,0,1,-1]


def test_unavailable_U_occurrence_refuses():
    import pytest
    g = oracle["Geometry"](-1,0,0)
    with pytest.raises(ValueError):
        oracle["predicted"](g,g.n+g.d+2,0)
