from __future__ import annotations

import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
POLICY = ROOT / "research_evidence_policy.toml"

CANONICAL = "Show the inspectable work behind every theorem-facing contribution."


def test_show_your_work_policy_surfaces_are_present_and_consistent() -> None:
    data = tomllib.loads(POLICY.read_text(encoding="utf-8"))
    assert data["version"] == 1
    assert data["canonical_rule"] == CANONICAL
    assert data["private_reasoning_required"] is False

    required = data["required_pr_headings"]
    assert required == [
        "### Assumptions and hypotheses",
        "### Derivation / reduction",
        "### Evidence and replay",
        "### Negative controls",
        "### Non-claims / remaining gaps",
    ]

    agents = (ROOT / "AGENTS.md").read_text(encoding="utf-8")
    docs = (ROOT / "docs/research-evidence-policy.md").read_text(encoding="utf-8")
    template = (ROOT / ".github/pull_request_template.md").read_text(encoding="utf-8")
    workflow = (ROOT / ".github/workflows/show-your-work.yml").read_text(encoding="utf-8")

    assert CANONICAL in agents
    assert "## Work shown" in agents
    assert "## Work shown" in template
    assert "research_evidence_policy.toml" in docs
    assert "research_evidence_policy.toml" in workflow

    for heading in required:
        assert heading in agents
        assert heading in docs
        assert heading in template

    assert "private chain-of-thought" in docs
    assert "private chain-of-thought" in agents


def test_show_your_work_policy_has_enforcement_scope() -> None:
    data = tomllib.loads(POLICY.read_text(encoding="utf-8"))
    prefixes = data["theorem_facing_prefixes"]
    assert "manuscripts/" in prefixes
    assert "docs/" in prefixes
    assert "kernel/psc/" in prefixes
    assert "proof/" in prefixes
    assert "oracles/" in prefixes

    workflow = (ROOT / ".github/workflows/show-your-work.yml").read_text(encoding="utf-8")
    assert '["git", "diff", "--name-only",' in workflow
    assert "no substantive visible evidence" in workflow
    assert "raise SystemExit(1)" in workflow
