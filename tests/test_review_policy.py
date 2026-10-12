from __future__ import annotations

import tomllib
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
POLICY = ROOT / "claim_governance.toml"
HUMAN_RULE = "Independent human review is a final validation gate, not a research-progress gate."


def test_independent_human_review_is_nonblocking_until_final_validation() -> None:
    data = tomllib.loads(POLICY.read_text(encoding="utf-8"))
    policy = data["review_policy"]

    assert policy["mode"] == "post-closure-validation"
    assert policy["blocks_research_progress"] is False
    assert policy["blocks_provisional_dependency_use"] is False
    assert policy["blocks_closure_construction"] is False
    assert policy["final_validation_required"] is True
    assert policy["truthful_status_labels_required"] is True
    assert policy["independently_reviewed_label_requires_completed_review"] is True
    assert policy["review_pending_classification"] == "non-blocking-validation-debt"

    surfaces = policy["human_surfaces"]
    assert surfaces
    for relative in surfaces:
        path = ROOT / relative
        assert path.is_file(), relative
        assert HUMAN_RULE in path.read_text(encoding="utf-8"), relative
