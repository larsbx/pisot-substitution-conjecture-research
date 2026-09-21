import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CONTRACT = ROOT / "docs" / "p1b-adelic-prefix-difference-cylinder.json"
NOTE = ROOT / "docs" / "p1b-adelic-prefix-difference-cylinder-2026-09-21.md"


def load_contract():
    return json.loads(CONTRACT.read_text(encoding="utf-8"))


def test_cylinder_is_specified_but_hitting_remains_open():
    data = load_contract()
    assert data["issue"] == 139
    assert data["status"] == "specified_not_proved"
    assert data["residual_lemma"] == {
        "name": "PeriodicOrbitCylinderRecurrence",
        "status": "open",
        "must_be_uniform_in_component": True,
        "must_preserve_occurrence_compatibility": True,
    }


def test_nonunit_carrier_keeps_finite_places():
    carrier = load_contract()["carrier"]
    assert carrier["finite_places_required_when_nonunit"] is True
    assert "all finite places dividing (beta)" in carrier["internal_places"]
    assert carrier["intertwiner_required"] == "lambda(M*z) = beta*lambda(z)"


def test_acceptance_stays_exact_and_occurrence_labelled():
    target = load_contract()["level_target"]
    assert target["formula"] == (
        "C_m(i,j) = beta^(-m) * Phi'_sigma(lambda(D_m(i,j)))"
    )
    assert target["acceptance_equivalence"] == (
        "Phi'_sigma(lambda(w)) in C_m(i,j) iff M^m*w in D_m(i,j)"
    )
    assert "exact integer equality" in target["authoritative_acceptance"]
    assert "occurrence-labelled" in target["authoritative_acceptance"]


def test_weak_geometric_surrogates_cannot_accept():
    forbidden = set(load_contract()["forbidden_acceptance"])
    assert "Archimedean projection equality in the non-unit case" in forbidden
    assert "membership in the closure of the cumulative target" in forbidden
    assert "positive measure or almost-everywhere coverage" in forbidden
    assert "floating or truncated local-coordinate equality" in forbidden


def test_note_keeps_claim_boundary_explicit():
    note = NOTE.read_text(encoding="utf-8")
    for marker in [
        "**Status:** exact specification for issue #139.",
        "### AdelicPeriodicOffsetHitting",
        "### Periodic-orbit cylinder recurrence (open)",
        "It does not imply a target hit.",
        "certificate acceptance remains",
    ]:
        assert marker in note
