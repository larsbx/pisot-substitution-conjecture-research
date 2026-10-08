"""Regressions for complete inventories, exact pins and fail-closed audits."""
from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import make_proof_bank as pb  # noqa: E402
import make_ledger  # noqa: E402
from proof_records import generate_ledgers as gl  # noqa: E402


def test_bank_is_current_and_includes_every_governed_claim_and_lean_proof():
    run = subprocess.run([sys.executable, str(ROOT / "tools/make_proof_bank.py"), "--check"], capture_output=True, text=True)
    assert run.returncode == 0, run.stdout + run.stderr
    data = pb.bank()
    assert {c["name"] for c in data["claims"]} >= set(make_ledger.TABLE)
    # Attributes and nested namespaces must not leave a theorem unaudited.
    names = {d["name"] for d in data["lean_declarations"]}
    assert {"Psc.ind_self", "Psc.BalancedPair.K₁_eq_zero", "Psc.trace_sq_conj", "Psc.det_A_ne_zero"} <= names
    statements = data["source_statements"]
    for heading in ("Lemma Ω1", "Theorem Ω", "Proposition LC", "Lemma S"):
        assert any(heading in s["statement_heading"] for s in statements), heading


def test_spectral_claims_do_not_misrepresent_their_lean_coverage():
    claims = {c["name"]: c for c in pb.bank()["claims"]}
    for name in ("PhiSemisimplicity", "ThetaIntertwining"):
        assert claims[name]["lean_support"]["coverage"] == "none"
        assert claims[name]["source"].startswith("archive/")
    assert claims["Target1"]["lean_support"]["coverage"] == "partial"
    assert claims["PSC"]["status"] == "open"


def test_all_local_modules_must_be_imported(tmp_path):
    project = tmp_path / pb.PROJECT
    shutil.copytree(ROOT / pb.PROJECT, project, ignore=shutil.ignore_patterns(".lake"))
    (project / "PscVerif/Unimported.lean").write_text("theorem omitted : True := trivial\n")
    with pytest.raises(ValueError, match="outside the root import closure"):
        pb.check_imports(tmp_path)


def test_lean_lexing_ignores_nested_comments_and_strings_and_tracks_namespaces(tmp_path):
    project = tmp_path / pb.PROJECT / "PscVerif"
    project.mkdir(parents=True)
    (project / "Sample.lean").write_text('''/- theorem fake : False := by sorry
/- nested comment -/ -/
namespace Psc
section
def message := "theorem fake2"
@[simp] theorem visible : True := trivial
end
namespace BalancedPair
lemma nested : True := trivial
end BalancedPair
end Psc
''')
    assert [d["name"] for d in pb.lean_declarations(tmp_path)] == ["Psc.visible", "Psc.BalancedPair.nested"]
    with pytest.raises(ValueError, match="Unterminated"):
        pb.lean_code("/- unterminated")


def test_pins_reject_unpinned_direct_requirements_and_wrong_checkouts(tmp_path):
    project = tmp_path / pb.PROJECT
    shutil.copytree(ROOT / pb.PROJECT, project, ignore=shutil.ignore_patterns(".lake"))
    file = project / "lakefile.toml"
    file.write_text(file.read_text().replace('rev = "4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09"', 'rev = "master"'))
    with pytest.raises(ValueError, match="manifest URL and revision"):
        pb.check_pins(tmp_path)
    shutil.copyfile(ROOT / pb.PROJECT / "lakefile.toml", file)
    with pytest.raises(ValueError, match="checkout does not match"):
        pb.check_pins(tmp_path, require_packages=True)


def audit_line(name="Psc.target1", axioms="propext,Classical.choice,Quot.sound"):
    return f"PSC_AXIOMS\ttheorem\t{name}\t{axioms}\n"


def test_audit_accepts_standard_axioms_and_requires_every_named_proof():
    text = audit_line() + "PSC_AUDIT_COMPLETE\t1\t1\n"
    assert pb.check_audit(text, {"Psc.target1"}) == (1, 1)
    with pytest.raises(ValueError, match="Incomplete"):
        pb.check_audit(text, {"Psc.target1", "Psc.unseen"})


@pytest.mark.parametrize("text", [
    "Build completed successfully\n",
    audit_line(),
    "PSC_AUDIT_COMPLETE\t0\t0\n",
    audit_line() + "PSC_AUDIT_COMPLETE\t2\t1\n",
    audit_line() * 2 + "PSC_AUDIT_COMPLETE\t2\t2\n",
    audit_line(axioms="sorryAx") + "PSC_AUDIT_COMPLETE\t1\t1\n",
    audit_line(axioms="Psc.trusted_gap") + "PSC_AUDIT_COMPLETE\t1\t1\n",
    audit_line() + "PSC_AUDIT_COMPLETE\t1\t1\n" + audit_line("Psc.later"),
])
def test_incomplete_cached_or_nonstandard_audit_is_rejected(text):
    with pytest.raises(ValueError):
        pb.check_audit(text, {"Psc.target1"})


def test_box_and_leftmost_nodes_record_implications_without_promoting_psc():
    analysis = gl.analyse(gl.load_ledger(ROOT / "proof/tla/ledger.json"))
    names = {e.name for e in analysis.entries}
    assert {"PotentialOverlapFiniteDescent", "BoxProductivityEquivalence", "BoxPDSCertificate", "LeftmostChainPeriodicPair"} <= names
    assert make_ledger.TABLE["BoxPDSCertificate"][3] == ("BoxProductivityEquivalence", "PisotFamilyMeyerProperty", "OverlapCoincidenceCriterion")
    assert make_ledger.TABLE["LeftmostChainPeriodicPair"][3] == ("LeftmostChainSign",)
    done = gl.established(analysis, ("PisotFamilyMeyerProperty", "OverlapCoincidenceCriterion"))
    assert "BoxPDSCertificate" in done
    assert not {"PDS", "G1", "OverlapProductivity"} & done


def test_check_lean_obeys_a_failed_build_even_if_output_says_success(tmp_path):
    fake_bin = tmp_path / "bin"
    fake_bin.mkdir()
    lake = fake_bin / "lake"
    lake.write_text('#!/bin/sh\necho "Build completed successfully"\nexit 7\n')
    lake.chmod(0o755)
    import os
    run = subprocess.run(["bash", str(ROOT / "tools/check_lean.sh")], cwd=tmp_path,
                         env={**os.environ, "PATH": f"{fake_bin}:{os.environ['PATH']}"}, capture_output=True, text=True)
    assert run.returncode == 7, run.stdout + run.stderr
