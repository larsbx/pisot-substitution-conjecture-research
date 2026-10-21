import importlib.util
import json
import os
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "class_d_positive_b_recurrent_support",
    ROOT / "oracles/python/class_d_positive_b_recurrent_support.py",
)
oracle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


def test_revised_classification_on_exact_grid():
    artifact = os.environ.get("CLASS_D_ORACLE_REPORT")
    out = json.loads(Path(artifact).read_text()) if artifact else oracle.report()
    assert out["status"] == "FINITE_EXACT_RECURRENT_SUPPORT_CALIBRATION"
    assert out["uniform_theorem"] is False
    assert out["specimens"] == 56
    assert out["unexplained_recurrent_labels"] == []
    assert out["cycle_sum_violations"] == []
    for row in out["rows"]:
        assert sum(map(len,row["classified"].values())) == row["recurrent_vertices"]
        assert len(row["exceptional_exits"]) == len(row["classified"]["exceptional"])
    if path := os.environ.get("CLASS_D_MOJO_LOG"):
        oracle.compare_mojo(out,path)


def test_zero_offset_noncoincidences_are_not_skipped():
    assert oracle.classify((0,0,0,0,0),set()) == "coincidence"
    assert oracle.classify((0,1,0,0,0),set()) == "unexplained"
    assert oracle.classify((0,1,0,0,0)) == "carrier"
    assert oracle.classify((1,0,0,0,0)) == "boundary_hit_noncoincidence"
    assert oracle.classify((0,1,99,-99,0)) == "unexplained"


@pytest.mark.parametrize("b", [1,2])
def test_genuine_exceptional_cycles_and_their_productive_exits(b):
    g = oracle.OverlapGraph(oracle.member(2,b))
    for v in oracle.EXCEPTIONS:
        assert v not in oracle.COVER
        assert oracle.classify(v) == "exceptional"
        state = oracle.state_of(g,v)
        mirror = (v[1],v[0],*[-x for x in v[2:]])
        assert oracle.state_of(g,mirror) in g.children(state)
        witness = oracle.exceptional_exit(g,v,2,b)
        assert tuple(witness["target"]) in oracle.COVER
        assert len(witness["occurrences"]) == (1 if witness["name"].startswith("U") else 2)


def test_unknown_zero_offset_has_replayable_seed_path_and_cycle():
    g = oracle.OverlapGraph(oracle.member(2,1))
    labels = oracle._labels(g)
    at = labels.index((0,1,0,0,0))
    assert oracle.classify(labels[at],set()) == "unexplained"
    witness = oracle.counterexample(g,labels,at,2,1)
    for path in (witness["seed_path"],witness["cycle"]):
        for edge in path:
            assert oracle.occurrence(g,oracle.state_of(g,edge["source"]),
                edge["top_index"],edge["bottom_index"]) == oracle.state_of(g,edge["target"])
    assert witness["cycle"][0]["source"] == witness["cycle"][-1]["target"] == labels[at]
    assert oracle.state_of(g,witness["seed"]) in g.seeds()


def test_partial_graph_refuses():
    with pytest.raises(RuntimeError, match="STATE_BUDGET_EXHAUSTED"):
        oracle.recurrent_report(2,1,1)


def test_incomplete_cross_language_log_refuses(tmp_path):
    path = tmp_path / "incomplete.log"
    path.write_text("CLASS_D_MINUS_RECURRENT_FINITE_CALIBRATION_OK specimens=56 uniform_theorem=false\n")
    with pytest.raises(ValueError,match="missing/extra"):
        oracle.compare_mojo(oracle.report(2,1),path)
