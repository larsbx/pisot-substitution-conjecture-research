from __future__ import annotations

import hashlib
import json
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


def test_review_policy_is_pinned_without_promoting_claims() -> None:
    policy = tomllib.loads(POLICY.read_text(encoding="utf-8"))
    bank = json.loads((ROOT / "proof/proof-bank.json").read_text(encoding="utf-8"))
    # Governance-only changes still invalidate the proof inventory input pin.
    assert bank["input_digests"]["claim_governance.toml"] == hashlib.sha256(POLICY.read_bytes()).hexdigest()
    statuses = {claim["name"]: claim["status"] for claim in policy["claim"]}
    assert {claim["name"]: claim["status"] for claim in bank["claims"]} == statuses
    assert statuses["PSC"] == "open"
