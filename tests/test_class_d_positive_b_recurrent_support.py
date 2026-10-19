import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "class_d_positive_b_recurrent_support",
    ROOT / "oracles/python/class_d_positive_b_recurrent_support.py",
)
oracle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


def test_positive_b_recurrent_support_stays_in_sealed_carrier_on_exact_grid():
    out = oracle.report()
    assert out["status"] == "FINITE_EXACT_RECURRENT_SUPPORT_CALIBRATION"
    assert out["uniform_theorem"] is False
    assert out["specimens"] == 56
    assert out["outside_recurrent_labels"] == []
    assert all(row["outside_recurrent"] == 0 for row in out["rows"])
