"""Complete nine-kind CY oracle and strict typed exit controls."""
import importlib.util
from pathlib import Path
import pytest

FILE = Path(__file__).resolve().parents[1] / "oracles/python/class_a_boundary_cy_children.py"
spec = importlib.util.spec_from_file_location("boundary_cy", FILE)
o = importlib.util.module_from_spec(spec)
spec.loader.exec_module(o)


def test_both_oriented_stars_and_two_cycle_across_117_members():
    r = o.probe()
    assert r["members"] == 117 and r["source_cells"] == 234
    assert r["pairs"] == 53976 and r["accepted"] == 6318
    assert r["image_labels"] == 12 and r["path_edges"] == 936
    assert r["cycle_Y0_CY_with_exit"]
    assert not r["all_child_productivity"] and not r["universal_BH"]


def test_actual_last_letter_and_endpoint_are_not_forced_coincidence():
    g = o.Geometry(-1, 0, 0)
    assert o.predicted(0, g, 0, 0)
    assert o.predicted(0, g, 0, 1)
    assert not o.predicted(0, g, 0, 2)
    assert not o.predicted(0, g, g.n+1, g.n)
    assert g.child(o.Y0, g.n, g.n) == (1, 1, 0, -2, 3)
    assert g.child(o.CY, 1, 2) == o.Y0
    assert not g.interior(g.child(o.CY, 0, 2))
    with pytest.raises(ValueError):
        o.predicted(0, g, 0, 10**6)


def test_wrong_oriented_target_and_mutated_path_refused():
    g = o.Geometry(-1, 2, 1)
    for flip in (0, 1):
        path = o.selected_path(flip, g)
        o.verify_selected(flip, g, path)
        wrong = list(path)
        i, j, target = wrong[0]
        wrong[0] = (i, j, (1, 2, 1, -1, -1))
        with pytest.raises(ValueError):
            o.verify_selected(flip, g, wrong)
    with pytest.raises(ValueError):
        o.source(2)
