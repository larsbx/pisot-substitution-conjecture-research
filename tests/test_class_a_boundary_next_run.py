import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "boundary_next_run", ROOT / "oracles/python/class_a_boundary_next_run.py")
oracle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


def test_complete_first_run_ordinals_and_word_clips():
    data = oracle.probe()
    assert data["members"] == 512
    assert data["source_cells"] == 1024
    assert data["run_ordinals"] > 20_000
    assert data["first_last_accepted"] == 64


def test_geometrically_disjoint_control_and_plus_k4_empty_packet():
    g = oracle.Geometry(-1, 0, 2)
    assert g.child((2, 2, -1, 1, 1), 0, 4) == (0, 2, 1, 2, -2)
    assert not g.interior((0, 2, 1, 2, -2))
    p = oracle.Geometry(1, 4, 0)
    assert oracle.expected(1, 4, 0, 1, p.n) == set()
    assert not any(p.interior(p.child((2, 2, -1, 1, 1), 0, j))
                   for j in range(1, p.n+2))
