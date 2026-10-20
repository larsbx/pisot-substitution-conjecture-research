import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "class_d_positive_b_support",
    ROOT / "oracles/python/class_d_positive_b_support.py",
)
oracle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


def test_positive_b_support_stays_in_sealed_cover_on_exact_grid():
    out = oracle.report()
    assert out["status"] == "FINITE_EXACT_SUPPORT_CALIBRATION"
    assert out["uniform_closure"] is False
    assert out["specimens"] == 56
    assert out["new_nonterminal_labels"] == []
    assert all(row["outside"] == 0 for row in out["rows"])
