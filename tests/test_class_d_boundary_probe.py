"""Independent boundary calibration and refusal, without canonical execution credit."""
import importlib.util
import json
from pathlib import Path
import pytest
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("class_d_boundary_probe", ROOT / "oracles/python/class_d_boundary_probe.py")
oracle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


def test_recorded_eight_graphs_replay_exactly():
    expected=json.loads((ROOT / "evidence/class-d-boundary-2026-10-14/oracle.json").read_text())
    assert oracle.report()==expected


def test_capped_graph_refuses_a_verdict():
    with pytest.raises(RuntimeError,match="STATE_BUDGET_EXHAUSTED"):
        oracle.probe(1,0,1)

@pytest.mark.parametrize("s,a,cap",[(0,0,20000),(1,9,20000),(1,-1,20000),(1,0,20001),(1,0,0)])
def test_invalid_budget_is_rejected(s,a,cap):
    with pytest.raises(ValueError):
        oracle.probe(s,a,cap)


def test_equal_vertex_counts_do_not_certify_equal_support():
    actual=json.loads(json.dumps(oracle.support_report()))
    expected=json.loads((ROOT / "evidence/class-d-support-change-2026-10-14/oracle.json").read_text())
    assert actual==expected
    assert actual["vertices"]==[145,145]
    assert actual["vertex_labels_equal"]
    assert not actual["support_equal"]
    assert all(not w["present_at_a2"] and w["present_at_a3"] for w in actual["witnesses"])
