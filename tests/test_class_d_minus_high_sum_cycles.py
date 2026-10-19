"""Independent calibration of the seed qualifier, never its universal removal."""
import importlib.util
import json
import os
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("high_sum",ROOT/"oracles/python/class_d_minus_high_sum_cycles.py")
oracle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


@pytest.fixture(scope="module")
def reports():
    path = os.environ.get("CLASS_D_HIGH_SUM_REPORT")
    if path:
        data = json.loads(Path(path).read_text())
        assert data["uniform_seed_theorem"] is False
        rows = data["rows"]
    else:
        rows = [oracle.sample(k) for k in (2,3,8)]
    assert [r["k"] for r in rows] == [2,3,8]
    return rows


def test_real_shared_parameter_cycles_are_not_seed_reachable_in_three_samples(reports):
    for row in reports:
        k = row["k"]
        assert row["a"] == 2*k-1 and row["b"] == 1
        assert row["interior"] and row["states"] == 139
        assert row["reachable_pair_vertices"] == 0 and row["counterexamples"] == []
        assert [sum(label[2:]) for label in row["labels"]] == [-k,k]
        assert [list(pair) for pair in row["occurrences"]] == [[4*k+4,6*k+4],[6*k+4,4*k+4]]
        assert all(oracle.support.classify(tuple(label)) == "unexplained" for label in row["labels"])


def test_capped_seed_graph_and_parameter_overflow_refuse():
    with pytest.raises(RuntimeError,match="capped"):
        oracle.sample(2,1)
    with pytest.raises(ValueError,match="budget"):
        oracle.sample(10**100)


def test_mojo_receipt_agreement_fails_on_missing_or_wrong_sample(tmp_path,reports):
    receipt = "HIGH_SUM_FORMAL_RAY_CERTIFIED k>=2 a=2k-1 b=1 abs_sum=k interior=true period=2 seed_reachability=unproved\n"
    text = receipt + "\n".join(f'HIGH_SUM_SEED_SAMPLE {r["k"]} a {r["a"]} b 1 complete_states 139 reachable_pair_vertices 0' for r in reports)
    log = tmp_path/"mojo.log"
    log.write_text(text)
    oracle.compare_mojo(reports,log)
    for broken in (text.replace("complete_states 139","complete_states 138"),text.splitlines()[0],text.replace(receipt,""),text+"\n"+text.splitlines()[-1]):
        log.write_text(broken)
        with pytest.raises(ValueError):
            oracle.compare_mojo(reports,log)


def test_cli_preserves_counterexample_json_before_agreement_failure(monkeypatch,capsys):
    monkeypatch.setattr(oracle.sys,"argv",["oracle","--mojo-log","wrong.log"])
    monkeypatch.setattr(oracle,"sample",lambda k:dict(k=k,reachable_pair_vertices=1,counterexamples=[{"seed_path":["replay"]}]))
    def disagree(rows,path):
        raise ValueError("deliberate agreement failure")
    monkeypatch.setattr(oracle,"compare_mojo",disagree)
    with pytest.raises(ValueError,match="deliberate"):
        oracle.main()
    report = json.loads(capsys.readouterr().out)
    assert [r["k"] for r in report["rows"]] == [2,3,8]
    assert all(r["counterexamples"] for r in report["rows"])
