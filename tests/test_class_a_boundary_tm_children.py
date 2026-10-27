import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "tm_children", ROOT / "oracles/python/class_a_boundary_tm_children.py")
oracle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


def test_every_actual_child_pair_of_both_Tm_sources():
    data = oracle.probe()
    assert data["members"] == 182
    assert data["source_cells"] == 364
    assert data["pairs"] > 100_000
    assert all(count > 0 for count in data["kind_counts"].values())
    assert data["image_labels"] == 50
