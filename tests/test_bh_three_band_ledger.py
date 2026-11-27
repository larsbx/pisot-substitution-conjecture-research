"""Exact family specialization closes; unrelated scopes and missing premises do not."""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import make_ledger  # noqa: E402
from proof_records import generate_ledgers as gl  # noqa: E402
from proof_records.records import SAME_SCOPE  # noqa: E402

FAMILY = "ThreeBandFiniteBPA"
PREMISES = (
    "HigherDeterminantPisotArithmetic",
    "ThreeBandLiteralClosure",
    "PisotAllSourceFiniteBPA",
)
UNIVERSAL_GATES = {
    "UniversalAlignedCoincidence", "UniversalBoundaryHitting",
    "TwoObstructionCompletion", "G1", "PDS", "OverlapProductivity",
    "AllSeedStrictZipperExclusion", "FormalProductivity",
}


def analyse_current():
    return gl.analyse(gl.load_ledger(ROOT / "proof/tla/ledger.json"))


def analyse_modified(tmp_path):
    path = tmp_path / "ledger.json"
    path.write_text(json.dumps(make_ledger.ledger()))
    return gl.analyse(gl.load_ledger(path))


def test_exact_family_has_complete_dependency_closure_and_full_lean_binding():
    analysis = analyse_current()
    entries = {entry.name: entry for entry in analysis.entries}
    names = {entry.record.id: entry.name for entry in analysis.entries}
    family = entries[FAMILY]
    assert family.status == "proved"
    assert family.closure.complete and not family.closure.missing_links
    assert family.requires == PREMISES
    assert {names[r] for r in family.closure.reached} == {FAMILY, *PREMISES}
    assert all(entries[name].record.kind == make_ledger.T for name in (FAMILY, *PREMISES))
    assert family.record.field("human_review_pending") == "true"
    claims = {claim["name"]: claim for claim in
              json.loads((ROOT / "proof/proof-bank.json").read_text())["claims"]}
    assert claims[FAMILY]["status"] == "proved"
    assert claims[FAMILY]["lean_support"]["coverage"] == "full"
    assert claims["PSC"]["status"] == "open"


def test_only_the_three_checked_applications_change_the_default_scope_rule():
    records = make_ledger.records()
    names = {record.id: name for name, record in records.items()}
    adapted = {
        (name, names[edge.record_id]): edge
        for name, record in records.items() for edge in record.depends_on
        if edge.scope_relation != SAME_SCOPE
    }
    assert set(adapted) == {(FAMILY, premise) for premise in PREMISES}
    for (_, premise), edge in adapted.items():
        assert edge.scope_relation == "scope=" + records[premise].scope
        assert edge.expected_claim == records[premise].statement
        assert edge.use_site.startswith(
            "proof/PscVerif/PscVerif/BHThreeBandBPA.lean:Psc.BHThreeBandBPA.")
        assert "FamilyClosure" in edge.use_site or "family_closure" in edge.use_site


def test_family_closure_does_not_discharge_the_generic_exit_or_universal_gates():
    analysis = analyse_current()
    entries = {entry.name: entry for entry in analysis.entries}
    generic = entries["PisotAllSourceFiniteBPA"].record
    assert "actual labelled-zero paths from every strict integral packet imply" in generic.statement
    assert "conditional on actual labelled exits from every strict integral packet" in generic.scope
    assert "no universal exit premise discharged" in generic.field("source")
    for name in ("UniversalAlignedCoincidence", "UniversalBoundaryHitting"):
        assert entries[name].status == "open"
        assert not entries[name].closure.complete
    for assumptions in ((), (FAMILY,), (FAMILY, "DensityToPDSBridge")):
        done = gl.established(analysis, assumptions)
        assert FAMILY in done
        assert not UNIVERSAL_GATES & done


@pytest.mark.parametrize("premise", PREMISES)
@pytest.mark.parametrize("fault", ("missing adapter", "wrong target scope"))
def test_unchecked_or_mismatched_scope_is_not_a_complete_closure(
        monkeypatch, tmp_path, premise, fault):
    key = (FAMILY, premise)
    if fault == "missing adapter":
        monkeypatch.delitem(make_ledger.CHECKED_SCOPE_APPLICATIONS, key)
    else:
        scope, use_site = make_ledger.CHECKED_SCOPE_APPLICATIONS[key]
        monkeypatch.setitem(make_ledger.CHECKED_SCOPE_APPLICATIONS, key,
                            (scope + "; negative-control scope mismatch", use_site))
    entries = {entry.name: entry for entry in analyse_modified(tmp_path).entries}
    family = entries[FAMILY]
    assert family.status == "conditional"
    assert not family.closure.complete
    assert any(link.record_id == entries[premise].record.id and
               link.reason.startswith("scope mismatch:")
               for link in family.closure.missing_links)


@pytest.mark.parametrize("premise", PREMISES)
def test_scope_adapter_does_not_supply_a_missing_mathematical_premise(
        monkeypatch, tmp_path, premise):
    _, statement, _, _, _ = make_ledger.TABLE[premise]
    monkeypatch.setitem(make_ledger.TABLE, premise,
                        (make_ledger.P, statement, "negative control: missing premise", (), ()))
    analysis = analyse_modified(tmp_path)
    entries = {entry.name: entry for entry in analysis.entries}
    assert entries[FAMILY].status == "conditional"
    assert not entries[FAMILY].closure.complete
    assert any(link.record_id == entries[premise].record.id and
               link.reason.startswith("pending:")
               for link in entries[FAMILY].closure.missing_links)
    assert FAMILY not in gl.established(analysis, ())
