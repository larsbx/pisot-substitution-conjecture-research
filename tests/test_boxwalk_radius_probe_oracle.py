"""Independent reference-oracle replay for the retired radius-eight assertion.

The Mojo driver/test remain canonical; this Python check pins the committed
finite-depth evidence JSON and refuses to call a depth plateau saturation.
"""
import json
import runpy
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ORACLE = runpy.run_path(str(ROOT / "oracles/python/boxwalk_radius_probe.py"))


def test_depth_nine_evidence_matches_exact_oracle():
    actual = ORACLE["probe"](max_depth=9, max_symbols=30000)
    expected = json.loads((ROOT / "evidence/boxwalk-radius8-depth9.json").read_text())
    assert actual == expected
    assert actual["saturation"] == "NOT_CHECKED"
    assert actual["constrained_family_exhaustion"] == "NOT_CHECKED"
    assert actual["rows"][8]["radius"] == 8
    assert actual["rows"][9]["radius"] == 10
    assert actual["rows"][9]["first_max_cut"] == 9054
    assert actual["rows"][9]["first_max_defect"] == [5, 5, -10]


def test_depth_eight_is_a_probe_not_saturation():
    partial = ORACLE["probe"](max_depth=8, max_symbols=10000)
    assert partial["status"] == "DEPTH_BUDGET_COMPLETE_NO_VERDICT"
    assert partial["rows"][-1]["radius"] == 8
    assert partial["saturation"] == "NOT_CHECKED"


def test_size_budget_is_explicit_refusal_not_verdict():
    capped = ORACLE["probe"](max_depth=9, max_symbols=20000)
    assert capped["status"] == "BUDGET_EXHAUSTED"
    assert capped["completed_through_depth"] == 8
    assert capped["rows"][-1]["radius"] == 8
