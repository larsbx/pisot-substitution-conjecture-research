"""Regressions for complete inventories, exact pins and fail-closed audits."""
from __future__ import annotations

import shutil
import json
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


def test_root_module_proofs_are_inventoried_and_required_in_the_audit(tmp_path):
    project = tmp_path / pb.PROJECT
    shutil.copytree(ROOT / pb.PROJECT, project, ignore=shutil.ignore_patterns(".lake"))
    root_module = project / "PscVerif.lean"
    root_module.write_text(root_module.read_text() + "\nnamespace RootBank\n"
                           "theorem root_theorem : True := trivial\n"
                           "lemma root_lemma : True := trivial\nend RootBank\n")
    pb.check_imports(tmp_path)
    inventory = pb.lean_declarations(tmp_path)
    names = {d["name"] for d in inventory}
    assert {"RootBank.root_theorem", "RootBank.root_lemma"} <= names
    assert all(d["source"] == "proof/PscVerif/PscVerif.lean"
               for d in inventory if d["name"].startswith("RootBank."))
    expected = {(d["module"], d["name"]) for d in inventory}
    audited = [d for d in inventory if not d["name"].startswith("RootBank.")]
    log = "".join(audit_line(d["name"], module=d["module"]) for d in audited)
    log += f"PSC_AUDIT_COMPLETE\t{len(audited)}\t{len(audited)}\n"
    with pytest.raises(ValueError, match="Incomplete Lean audit.*RootBank"):
        pb.check_audit(log, expected)


@pytest.mark.parametrize("header", [
    "nonrec theorem",
    "public protected nonrec theorem",
    "noncomputable nonrec lemma",
    "public protected meta unsafe partial theorem",
    "@[\n  simp\n] public nonrec theorem",
    "nonrec\ntheorem\n",
])
def test_lean_modifier_and_multiline_proofs_cannot_escape_inventory(tmp_path, header):
    project = tmp_path / pb.PROJECT
    shutil.copytree(ROOT / pb.PROJECT, project, ignore=shutil.ignore_patterns(".lake"))
    module = project / "PscVerif.lean"
    module.write_text(module.read_text() + f"\nnamespace ModifierBank\n{header}"
                      " modified : True := trivial\nend ModifierBank\n")
    inventory = pb.lean_declarations(tmp_path)
    names = {d["name"] for d in inventory}
    assert "ModifierBank.modified" in names
    declaration = next(d for d in inventory if d["name"] == "ModifierBank.modified")
    assert declaration["source"] == "proof/PscVerif/PscVerif.lean"
    expected = {(d["module"], d["name"]) for d in inventory}
    audited = [d for d in inventory if d["name"] != "ModifierBank.modified"]
    log = "".join(audit_line(d["name"], module=d["module"]) for d in audited)
    log += f"PSC_AUDIT_COMPLETE\t{len(audited)}\t{len(audited)}\n"
    with pytest.raises(ValueError, match="Incomplete Lean audit.*ModifierBank.modified"):
        pb.check_audit(log, expected)


@pytest.mark.parametrize("prefix", ["set_option maxRecDepth 1000 in", "open Nat in"])
def test_unrecognized_scoped_proof_headers_refuse_an_incomplete_inventory(tmp_path, prefix):
    project = tmp_path / pb.PROJECT
    shutil.copytree(ROOT / pb.PROJECT, project, ignore=shutil.ignore_patterns(".lake"))
    module = project / "PscVerif.lean"
    module.write_text(module.read_text() + f"\n{prefix} nonrec theorem omitted : True := trivial\n")
    with pytest.raises(ValueError, match="Unaccounted Lean proof header"):
        pb.lean_declarations(tmp_path)


@pytest.mark.parametrize("change", ["unstaged", "staged", "deleted", "untracked",
                                    "ignored_source", "ignored_config",
                                    "assume_unchanged", "skip_worktree", "replace_object"])
@pytest.mark.parametrize("require_packages", [False, True])
def test_pinned_dependency_refuses_tracked_changes(tmp_path, change, require_packages):
    project = tmp_path / pb.PROJECT
    project.mkdir(parents=True)
    pin = (ROOT / pb.PROJECT / "lean-toolchain").read_text()
    (project / "lean-toolchain").write_text(pin)
    dependency = project / ".lake/packages/mathlib"
    dependency.mkdir(parents=True)
    source = dependency / "Fixture.lean"
    source.write_text("theorem trusted : True := trivial\n")
    (dependency / "lean-toolchain").write_text(pin)
    (dependency / ".gitignore").write_text(".lake/\n")

    def git(*args):
        return subprocess.check_output(["git", "-C", str(dependency), *args], text=True).strip()

    git("init", "-q")
    git("add", ".")
    git("-c", "user.name=Pin Regression", "-c", "user.email=pin-regression@example.invalid",
        "commit", "-qm", "Pin a dependency fixture")
    revision = git("rev-parse", "HEAD")
    url = "https://example.invalid/mathlib.git"
    (project / "lakefile.toml").write_text(
        f'[[require]]\nname = "mathlib"\ngit = "{url}"\nrev = "{revision}"\n')
    (project / "lake-manifest.json").write_text(json.dumps({
        "packagesDir": ".lake/packages", "packages": [{"name": "mathlib", "type": "git",
        "url": url, "rev": revision, "inputRev": revision}]}))
    cache = dependency / ".lake/build/cache.olean"
    cache.parent.mkdir(parents=True)
    cache.write_bytes(b"ignored build cache")
    # A real Lake build emits these beside/inside build/. Refusal of ordinary
    # build outputs would prevent the post-build pin audit from ever passing.
    setup = dependency / ".lake/build/ir/Fixture.setup.json"
    setup.parent.mkdir(parents=True)
    setup.write_text('{"name": "Fixture", "imports": []}\n')
    (dependency / ".lake/build.barrel").write_bytes(b"Reservoir build archive")
    (dependency / ".lake/build.barrel.trace").write_text("generated archive trace\n")
    assert pb.check_pins(tmp_path, require_packages)["packages"][0]["rev"] == revision
    if change == "replace_object":
        source.write_text("theorem trusted : False := by sorry\n")
        git("add", "Fixture.lean")
        git("-c", "user.name=Pin Regression", "-c", "user.email=pin-regression@example.invalid",
            "commit", "-qm", "Build an unpinned replacement object")
        replacement = git("rev-parse", "HEAD")
        git("reset", "--hard", revision)
        git("replace", revision, replacement)
        git("reset", "--hard", revision)
        assert "False" in source.read_text()
        assert not git("status", "--porcelain", "--untracked-files=all")
    elif change in {"assume_unchanged", "skip_worktree"}:
        git("update-index", "--assume-unchanged" if change == "assume_unchanged" else "--skip-worktree",
            "Fixture.lean")
        source.write_text("theorem trusted : False := by sorry\n")
    elif change.startswith("ignored_"):
        relative = "Mathlib/Injected.lean" if change == "ignored_source" else ".lake/build/injected.toml"
        injected = dependency / relative
        injected.parent.mkdir(parents=True, exist_ok=True)
        injected.write_text("-- an unpinned input\n")
        exclude = dependency / ".git/info/exclude"
        exclude.write_text(exclude.read_text() + f"\n{relative}\n")
    elif change == "untracked":
        (dependency / "Injected.lean").write_text("theorem injected : False := by sorry\n")
    elif change == "deleted":
        source.unlink()
    else:
        source.write_text("theorem trusted : False := by sorry\n")
        if change == "staged":
            git("add", "Fixture.lean")
    assert git("rev-parse", "HEAD") == revision
    with pytest.raises(ValueError, match="Lake checkout.*mathlib"):
        pb.check_pins(tmp_path, require_packages)


def audit_line(name="Psc.target1", axioms="propext,Classical.choice,Quot.sound", *,
               module="PscVerif", raw_name=None):
    return f"PSC_AXIOMS\ttheorem\t{module}\t{raw_name or name}\t{name}\t{axioms}\n"


@pytest.mark.parametrize("modules", [["PrivateA"], ["PrivateA", "PrivateB"]])
def test_private_proofs_reconcile_by_source_name_and_module_without_collapsing_counts(tmp_path, modules):
    project = tmp_path / pb.PROJECT
    shutil.copytree(ROOT / pb.PROJECT, project, ignore=shutil.ignore_patterns(".lake"))
    root = project / "PscVerif.lean"
    root.write_text("".join(f"import PscVerif.{m}\n" for m in modules) + root.read_text())
    for module in modules:
        (project / "PscVerif" / f"{module}.lean").write_text(
            "namespace PrivateBank\nprivate theorem helper : True := trivial\n"
            "private lemma helper_lemma : True := trivial\nend PrivateBank\n")
    pb.check_imports(tmp_path)
    inventory = pb.lean_declarations(tmp_path)
    private = [d for d in inventory if d["private"]]
    assert len(private) == 2 * len(modules)
    expected = {(d["module"], d["name"]) for d in inventory}

    def line(d):
        raw = f"_private.{d['module']}.0.{d['name']}" if d["private"] else d["name"]
        return audit_line(d["name"], module=d["module"], raw_name=raw)

    log = "".join(line(d) for d in inventory)
    log += f"PSC_AUDIT_COMPLETE\t{len(inventory)}\t{len(inventory)}\n"
    assert pb.check_audit(log, expected) == (len(inventory), len(inventory))
    omitted = private[0]
    incomplete = [d for d in inventory if d is not omitted]
    log = "".join(line(d) for d in incomplete)
    log += f"PSC_AUDIT_COMPLETE\t{len(incomplete)}\t{len(incomplete)}\n"
    with pytest.raises(ValueError, match=f"Incomplete Lean audit.*{omitted['module']}"):
        pb.check_audit(log, expected)


def test_audit_accepts_standard_axioms_and_requires_every_named_proof():
    text = audit_line() + "PSC_AUDIT_COMPLETE\t1\t1\n"
    assert pb.check_audit(text, {("PscVerif", "Psc.target1")}) == (1, 1)
    with pytest.raises(ValueError, match="Incomplete"):
        pb.check_audit(text, {("PscVerif", "Psc.target1"), ("PscVerif", "Psc.unseen")})


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
        pb.check_audit(text, {("PscVerif", "Psc.target1")})


def test_box_and_leftmost_nodes_record_implications_without_promoting_psc():
    analysis = gl.analyse(gl.load_ledger(ROOT / "proof/tla/ledger.json"))
    names = {e.name for e in analysis.entries}
    assert {"BoxCycleContainment", "BoxAutomatonCertificate", "BoxAutomatonPDSCertificate", "LeftmostChainCycleStructure"} <= names
    assert make_ledger.TABLE["BoxAutomatonPDSCertificate"][3] == ("BoxAutomatonCertificate", "PisotMeyerProperty", "OverlapCoincidenceCriterion")
    assert make_ledger.TABLE["LeftmostChainCycleStructure"][3] == ()
    done = gl.established(analysis, ("PisotMeyerProperty", "OverlapCoincidenceCriterion"))
    assert "BoxAutomatonPDSCertificate" in done
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


def test_cached_successful_build_still_requires_a_fresh_audit(tmp_path):
    fake_bin = tmp_path / "bin"
    fake_bin.mkdir()
    calls = tmp_path / "lake-calls"
    lake = fake_bin / "lake"
    import shlex
    lake.write_text('#!/bin/sh\nprintf "%s\\n" "$*" >> ' + shlex.quote(str(calls)) +
                    '\necho "Build completed successfully"\nexit 0\n')
    lake.chmod(0o755)
    import os
    run = subprocess.run(["bash", str(ROOT / "tools/check_lean.sh")], cwd=tmp_path,
                         env={**os.environ, "PATH": f"{fake_bin}:{os.environ['PATH']}"}, capture_output=True, text=True)
    assert run.returncode != 0, run.stdout + run.stderr
    assert calls.read_text().splitlines() == ["build PscVerif", "env lean ProofBankAudit.lean"]
    assert "Incomplete Lean audit" in run.stderr
