#!/usr/bin/env python3
"""Inspect a completed hosted nine-proof C4 termination artifact without Lean.

The expected run, commit and tree must be supplied explicitly. It reads raw
GitHub REST run/jobs JSON, the downloaded artifact, and the exact clean source.
It never fabricates a local process return code or executes artifact content.
This successor retains the exclusion inspector's gates and extends them to the
existing seed/actual-descendant endpoints. Download ID/ZIP-digest provenance
must still be retained separately; these inputs do not authenticate that link.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import importlib.util
import io
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

sys.dont_write_bytecode = True

REPOSITORY = "larsbx/pisot-substitution-conjecture-research"
WORKFLOW = ".github/workflows/c4-archived-payload-lean.yml"
WORKFLOW_NAME = "Original C4 archived payload Lean import"
JOB_NAME = "Original graph proof terms, geometry and compiled axiom audit"
REQUIRED_STEPS = (
    "Bind exact candidate revision and archive",
    "Provision pinned Lean and dependency sources",
    "Canonical payload construction and import controls",
    "Independent payload and original graph replay",
    "Isolated full build and both concrete geometric imports",
)
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PROOFS = {"valid", "accepted", "typed_accepted", "domain_iff", "roots_null",
          "ancestors_null", "no_strict_system", "seed_terminates", "reachable_terminates"}
TERMINATION_PROOFS = ("seed_terminates", "reachable_terminates")
EXPECTED_DECLARATIONS = {
    **{("PscVerif.NamedStrictExclusion", "Psc.NamedStrictExclusion." + name): "theorem"
       for name in ("intersection_eq_archivedRoot", "carrierOverlap_subset_archivedRoots",
                    "no_strictSystem_of_roots_null", "exists_probabilityHaar")},
    **{("PscVerif.NamedStrictExclusion", "Psc.ArchivedPayload.Packet." + name): "theorem"
       for name in ("no_strictSystem_of_measure", "no_strictSystem", "no_strictComponent", "no_bpaStrictComponent")},
    **{("PscVerif.NamedStrictExclusionControls", "Psc.NamedStrictExclusionControls." + name): kind
       for name, kind in (("diagonalTiles", "declaration"), ("omittedRootTiles", "declaration"),
                          ("dropping_distinct_labels_counterexample", "theorem"),
                          ("omitting_root_counterexample", "theorem"))},
    **{("PscVerif.FiniteProductivity", "Psc.FiniteProductivity." + name): "theorem"
       for name in ("isBlock_of_reachableNC", "reachableNC_subset",
                    "productive_of_finite_reachable", "terminates_of_finite_reachable",
                    "terminates_iff_finite_reachable", "infinite_reachable_of_not_productive",
                    "not_terminates_iff_infinite_reachable", "thueMorse_finite_nonproductive",
                    "fibonacci_terminates")},
    **{("PscVerif.NamedFiniteProductivity", "Psc.ArchivedPayload.Packet." + name): "theorem"
       for name in ("productive_of_finite_reachable", "terminates_of_finite_reachable",
                    "terminates_iff_finite_reachable", "infinite_reachable_of_not_productive",
                    "not_terminates_iff_infinite_reachable", "seed_terminates_of_finite_reachable")},
    **{("PscVerif.NamedForwardCarrier", "Psc.NamedForwardCarrier." + name): kind
       for name, kind in (("check", "declaration"), ("checkedStates", "declaration"),
                          ("valid_of_check", "theorem"), ("finite_bpaStatesNC_of_check", "theorem"),
                          ("finite_reachable_of_mem", "theorem"), ("fixture0Substitution_eq", "theorem"),
                          ("fixture1Substitution_eq", "theorem"), ("check_checkedStates", "theorem"),
                          ("finite_bpaStatesNC", "theorem"))},
    **{("PscVerif.NamedForwardCarrier", "Psc.ArchivedPayload.Packet." + name): "theorem"
       for name in ("terminates_of_forwardCarrier", "reachable_terminates_of_forwardCarrier",
                    "seed_terminates_of_forwardCarrier", "reachable_terminates", "seed_terminates")},
}
EXPECTED_MODULE_PATHS = {
    "proof/PscVerif/PscVerif/" + owner.removeprefix("PscVerif.") + ".lean": owner
    for owner, _ in EXPECTED_DECLARATIONS
}
ADDED_REPLAY_SOURCES = (
    "proof/PscVerif/PscVerif/FiniteProductivity.lean",
    "proof/PscVerif/PscVerif/NamedFiniteProductivity.lean",
    "proof/PscVerif/PscVerif/ForwardCarrier.lean",
    "proof/PscVerif/PscVerif/FastForwardCarrier.lean",
    "proof/PscVerif/PscVerif/NamedForwardCarrierWords0.lean",
    "proof/PscVerif/PscVerif/NamedForwardCarrierWords1.lean",
    "proof/PscVerif/PscVerif/NamedForwardCarrierData0.lean",
    "proof/PscVerif/PscVerif/NamedForwardCarrierData1.lean",
    "proof/PscVerif/PscVerif/NamedForwardCarrier.lean",
)
# Preserve every source path in the predecessor's 26-path static review, and
# require the nine exact new proof sources. No omitted or extra path silently
# changes which source bytes the metadata purports to bind.
REQUIRED_METADATA_PATHS = frozenset({
    "proof/PscVerif/PscVerif/NamedStrictExclusion.lean",
    "proof/PscVerif/PscVerif/NamedStrictExclusionControls.lean",
    "proof/PscVerif/PscVerif/NamedPositiveOverlap.lean",
    "proof/PscVerif/PscVerif/NamedFundamentalCell.lean",
    "proof/PscVerif/PscVerif/NamedPrefixCompact.lean",
    "proof/PscVerif/PscVerif/NamedCutNeighborhood.lean",
    "proof/PscVerif/PscVerif/StrictSystem.lean",
    "proof/PscVerif/PscVerif/ArchivedGraphRefinement.lean",
    "proof/PscVerif/PscVerif/OccurrencePiece.lean",
    "proof/PscVerif/PscVerif/OccurrenceResidue.lean",
    "proof/PscVerif/PscVerif/NamedProductHaar.lean",
    "proof/PscVerif/PscVerif/MadicResidue.lean",
    "proof/PscVerif/PscVerif/MadicHaar.lean",
    "proof/PscVerif/PscVerif/ArchivedPayloadConsumer.lean",
    "proof/PscVerif/PscVerif/OverlapContraction.lean",
    "proof/PscVerif/PscVerif.lean",
    "proof/PscVerif/ProofBankAudit.lean",
    "proof/PscVerif/lake-manifest.json",
    "proof/proof-bank.json",
    "tools/check_lean.sh",
    "tools/make_proof_bank.py",
    "tools/replay_archived_payload_lean.py",
    "evidence/c4-finite-cut-count-2026-11-12/gate/inspect-count-audit.py",
    "docs/c4-named-strict-exclusion.md",
    "docs/side-notes-ledger.md",
    "tests/fixtures/c4_archived_bad_binding.lean",
} | set(ADDED_REPLAY_SOURCES))
ARCHIVE = "evidence/c4-pair-overlap-graph-2026-11-05/receipt.json"
ADDRESSED_ARCHIVE = "evidence/c4-archived-graph-refinement-2026-11-11/native-oracle/receipt.json"
REPLAY_SOURCES = (
    "proof/PscVerif/PscVerif/NamedArchivedDigits.lean",
    "proof/PscVerif/PscVerif/ArchivedPayload.lean",
    "proof/PscVerif/PscVerif/ArchivedPayloadConsumer.lean",
    "proof/PscVerif/PscVerif/ArchivedPayloadEmit.lean",
    "proof/PscVerif/PscVerif/NamedPositiveOverlap.lean",
    "proof/PscVerif/PscVerif/NamedPositiveOverlapControls.lean",
    "proof/PscVerif/PscVerif/NamedStrictExclusion.lean",
    "proof/PscVerif/PscVerif/NamedStrictExclusionControls.lean",
    *ADDED_REPLAY_SOURCES,
    "tests/fixtures/c4_archived_bad_binding.lean",
    "kernel/psc/c4_archived_payload.mojo", "kernel/c4_archived_lean_export.mojo",
    "oracles/python/c4_archived_payload.py", "tools/replay_archived_payload_lean.py",
    "tools/check_lean.sh", ARCHIVE, ADDRESSED_ARCHIVE,
)
NATIVE_CONTROLS = {
    "different_original_substitution", "flipped_track_swap", "graph_domain_mismatch",
    "hidden_high_payload", "incomplete_inverse_ancestry", "missing_lookup_node",
    "missing_packed_leaf", "omitted_repeated_positional_edge", "packed_orientation_mismatch",
    "packed_weight_mismatch", "removed_ancestor_and_all_stored_edges",
    "swapped_graph_direction", "wrong_24_12_box", "wrong_lookup_identity",
    "wrong_lookup_shape", "wrong_nested_local_address",
}


class InspectionRefused(ValueError):
    pass


def require(condition, reason):
    if not condition:
        raise InspectionRefused(reason)


def now():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_sha(path):
    result = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def json_bytes(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def relative_path(name):
    path = PurePosixPath(name)
    require(not path.is_absolute() and ".." not in path.parts and str(path) == name,
            f"Unsafe relative path: {name}")
    return path


def git_source(root):
    def git(*parts):
        return subprocess.check_output(["git", "--no-optional-locks", *parts],
                                       cwd=root, text=True).strip()
    return {"commit": git("rev-parse", "HEAD"), "tree": git("rev-parse", "HEAD^{tree}"),
            "status_porcelain": git("status", "--porcelain=v1", "--untracked-files=all")}


class Artifact:
    def __init__(self, root):
        self.root = root
        self.manifest = []
        self.identities = {}
        self.cache = {}
        for path in sorted(root.rglob("*")):
            require(not path.is_symlink(), f"Artifact symlink refused: {path}")
            if path.is_dir():
                continue
            require(path.is_file(), f"Nonregular artifact entry: {path}")
            name = path.relative_to(root).as_posix()
            relative_path(name)
            before = path.stat()
            item = {"path": name, "bytes": before.st_size, "sha256": file_sha(path)}
            after = path.stat()
            before_id = (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns)
            require(before_id == (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns),
                    f"Artifact changed while hashing: {name}")
            self.manifest.append(item)
            self.identities[name] = before_id
        self.by_name = {item["path"]: item for item in self.manifest}
        require(bool(self.manifest), "Artifact directory is empty")

    def read(self, name):
        relative_path(name)
        require(name in self.by_name, f"Required artifact file missing: {name}")
        if name not in self.cache:
            data = (self.root / name).read_bytes()
            expected = self.by_name[name]
            require(len(data) == expected["bytes"] and sha(data) == expected["sha256"],
                    f"Artifact changed since inventory: {name}")
            self.cache[name] = data
        return self.cache[name]

    def text(self, name):
        return self.read(name).decode("utf-8", errors="strict")

    def json(self, name):
        return json.loads(self.read(name))

    def verify_unchanged(self):
        current = set()
        for path in self.root.rglob("*"):
            require(not path.is_symlink(), f"Artifact became a symlink: {path}")
            if path.is_dir():
                continue
            name = path.relative_to(self.root).as_posix()
            current.add(name)
            st = path.stat()
            require(self.identities.get(name) == (st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns),
                    f"Artifact changed during inspection: {name}")
        require(current == set(self.by_name), "Artifact file inventory changed")


def load_source_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def hosted_verdict(run, jobs, expected_run_id, expected_commit):
    require(run.get("id") == expected_run_id, "Wrong GitHub workflow run ID")
    require(run.get("repository", {}).get("full_name") == REPOSITORY, "Wrong GitHub repository")
    require(run.get("head_sha") == expected_commit, "GitHub run head differs from candidate")
    raw_workflow_path = run.get("path")
    require(isinstance(raw_workflow_path, str), "Missing GitHub workflow path")
    workflow_path, separator, workflow_ref = raw_workflow_path.partition("@")
    require(workflow_path == WORKFLOW and (not separator or bool(workflow_ref))
            and run.get("name") == WORKFLOW_NAME,
            "Wrong GitHub workflow")
    require(run.get("status") == "completed" and run.get("conclusion") == "success",
            "GitHub run is not completed/success; acceptance inspection is premature or refused")
    attempt = run.get("run_attempt")
    require(isinstance(attempt, int) and attempt > 0, "Missing GitHub run attempt")
    rows = jobs.get("jobs")
    require(isinstance(rows, list) and jobs.get("total_count") == len(rows),
            "Jobs metadata is not a complete raw REST jobs response")
    matching = [job for job in rows if job.get("name") == JOB_NAME]
    require(len(matching) == 1, "Expected exactly one relevant archived-payload job")
    job = matching[0]
    require(job.get("run_id") == expected_run_id and job.get("head_sha") == expected_commit,
            "Relevant job belongs to a different run or head")
    require(job.get("run_attempt") == attempt, "Relevant job belongs to a different or unknown attempt")
    require(job.get("status") == "completed" and job.get("conclusion") == "success",
            "Relevant GitHub job did not complete successfully")
    require(bool(job.get("completed_at")), "Relevant job has no completion timestamp")
    steps = job.get("steps", [])
    selected_steps = []
    for name in REQUIRED_STEPS:
        matches = [step for step in steps if step.get("name") == name]
        require(len(matches) == 1, f"Missing or duplicate critical GitHub step: {name}")
        step = matches[0]
        require(step.get("status") == "completed" and step.get("conclusion") == "success",
                f"Critical GitHub step did not complete successfully: {name}")
        require(bool(step.get("completed_at")), f"Critical step lacks completion timestamp: {name}")
        selected_steps.append(step)
    return job, selected_steps


def verify_oracle(oracle, payload, archive, addressed, label):
    require(oracle.get("schema") == "c4-archived-payload-v1", f"Wrong {label} oracle schema")
    require(oracle.get("all_two_original_fixtures_verified") is True,
            f"{label} oracle did not verify both original fixtures")
    require(oracle.get("kernel_acceptance_supplied_by_this_oracle") is False,
            f"{label} oracle has wrong acceptance scope")
    require(oracle.get("payload_sha256") == sha(payload) and oracle.get("payload_bytes") == len(payload),
            f"{label} oracle is not bound to retained payload bytes")
    fixtures = oracle.get("fixtures", [])
    require([fixture.get("fixture") for fixture in fixtures] == [0, 1],
            f"{label} oracle has missing, duplicate or wrong fixtures")
    for index, fixture in enumerate(fixtures):
        old = archive["fixtures"][index]
        count = (7150, 7083)[index]
        expected = {"states": count, "packed_rows": count, "lookup_nodes": count,
                    "positional_edges": (34826, 34853)[index], "radii": [16, 8],
                    "rate": old["rate"], "sigma": (["1", "021", "001"], ["1", "012", "001"])[index],
                    "historical_graph_sha256": old["canonical_graph_sha256"],
                    "addressed_packet_sha256": addressed["fixtures"][index]["addressed_packet_sha256"]}
        for key, value in expected.items():
            require(fixture.get(key) == value, f"{label} fixture {index}: wrong archive binding {key}")


def oracle_pytest_verdict(text, step):
    """Recognize the producer's eight-test quiet output plus its real step verdict.

    Keep an absent textual pass-count summary absent in the report. The genuine
    native-oracle step at failed head 16dd emitted only eight dots and [100%].
    This does not relax the enclosing run/job completed-success requirements.
    """
    require(step.get("name") == "Independent payload and original graph replay"
            and step.get("status") == "completed" and step.get("conclusion") == "success",
            "Oracle pytest transcript is not bound to its successful GitHub step")
    require(not re.search(r"\b(?:skipped|skips?|xfail(?:ed|s)?|xpass(?:ed|es)?|failed|failures?|errors?|interrupted|deselected)\b",
                          text, re.IGNORECASE),
            "Oracle pytest transcript reports skips, expected failures, errors or incomplete selection")
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    progress = r"\.{8}[ \t]+\[100%\]"
    summary = r"(?:=+[ \t]*)?8 passed(?: in [0-9]+(?:\.[0-9]+)?s(?: \([0-9:]+\))?)?(?:[ \t]*=+)?"
    quiet = len(lines) == 1 and re.fullmatch(progress, lines[0]) is not None
    normal = ((len(lines) == 1 and re.fullmatch(summary, lines[0]) is not None)
              or (len(lines) == 2 and re.fullmatch(progress, lines[0]) is not None
                  and re.fullmatch(summary, lines[1]) is not None))
    require(quiet or normal, "Oracle pytest transcript is not the complete eight-dot [100%] or eight-passed form")
    return {"transcript_form": "eight_dot_quiet_100_percent" if quiet else "normal_eight_passed_summary",
            "normal_pass_summary_present": bool(normal), "reported_passed_count": 8 if normal else None,
            "observed_progress_dot_count": 8 if quiet or len(lines) == 2 else None,
            "validated_expected_pass_count": 8, "bound_github_step_number": step.get("number"),
            "bound_github_step_conclusion": step["conclusion"], "stdout_summary_fabricated": False}


def metadata_source_records(metadata):
    """Require the fixed 35-path metadata contract, without duplicate shadowing."""
    records = []
    for key in ("modules", "reviewed_repository_dependencies_and_audit_sources",
                "changed_nonproof_sources"):
        group = metadata.get(key)
        require(isinstance(group, list) and all(isinstance(item, dict) for item in group),
                f"Missing or malformed static source group: {key}")
        records.extend(group)
    paths = [item.get("path") for item in records]
    require(all(isinstance(path, str) for path in paths), "Static source path is not a string")
    require(len(paths) == len(set(paths)), "Duplicate static source metadata path")
    require(set(paths) == REQUIRED_METADATA_PATHS,
            "Static source metadata must contain exactly the 35 required paths")
    return records


def declaration_inventory(metadata):
    """Pin all prior exclusion declarations and the three new consumer modules."""
    modules = metadata.get("modules")
    require(isinstance(modules, list) and len(modules) == len(EXPECTED_MODULE_PATHS),
            "Expected exactly five explicit-declaration modules")
    require({module.get("path"): module.get("module") for module in modules} == EXPECTED_MODULE_PATHS,
            "Static metadata has the wrong explicit-declaration module identities")
    inventory = []
    for module in modules:
        declarations = module.get("declarations")
        require(isinstance(declarations, list), "Missing explicit declaration inventory")
        for declaration in declarations:
            require(isinstance(declaration, dict)
                    and declaration.get("owner") == module["module"],
                    "Explicit declaration assigned to the wrong source module")
            require(declaration.get("private") is False,
                    "Required explicit declaration is private or has unknown visibility")
            inventory.append(declaration)
    identities = [(item.get("owner"), item.get("name")) for item in inventory]
    require(len(identities) == 41 and len(set(identities)) == 41,
            "Expected 41 distinct explicit declarations")
    require({(d["owner"], d["name"]): d.get("expected_compiled_kind") for d in inventory}
            == EXPECTED_DECLARATIONS,
            "Static metadata does not contain the exact 41 required declaration identities/kinds")
    require(sum(d["expected_compiled_kind"] == "theorem" for d in inventory) == 37,
            "Expected 37 explicit theorem declarations")
    require(sum(d["expected_compiled_kind"] == "declaration" for d in inventory) == 4,
            "Expected four explicit definitions")
    return inventory


def compiled_declarations(rows, inventory):
    """Match explicit declarations after the complete proof-bank parser succeeds."""
    owners = set(EXPECTED_MODULE_PATHS.values())
    selected = [row for row in rows if row[2] in owners]
    for declaration in inventory:
        matches = [row for row in selected if (row[2], row[4])
                   == (declaration["owner"], declaration["name"])]
        require(len(matches) == 1, f"Missing/duplicate compiled declaration: {declaration['name']}")
        row = matches[0]
        require(row[1] == declaration["expected_compiled_kind"] and row[3] == declaration["name"]
                and declaration["private"] is False,
                f"Wrong compiled declaration identity: {declaration['name']}")
    return selected


def replay_contract(replay_tool):
    require(replay_tool.PROOFS == PROOFS and replay_tool.ALLOWED == ALLOWED
            and replay_tool.TERMINATION_PROOFS == TERMINATION_PROOFS,
            "Unexpected nine-proof replay parser contract")


def replay_receipt_header(receipt, pin):
    require(receipt.get("schema") == "c4-archived-payload-lean-replay-v1", "Wrong concrete replay schema")
    require(receipt.get("both_original_fixtures_verified") is True and receipt.get("fixtures_verified") == 2,
            "Concrete receipt does not verify both original fixtures")
    require(receipt.get("strict_system_exclusion_fixtures") == [0, 1], "Missing fixture exclusion results")
    require(receipt.get("seed_and_reachable_termination_fixtures") == [0, 1],
            "Missing seed and actual-descendant termination results for both fixtures")
    require(receipt.get("semantic_proofs") == sorted(PROOFS),
            "Concrete semantic proof set differs from all nine obligations")
    require(receipt.get("allowed_axioms") == sorted(ALLOWED) and receipt.get("lean_toolchain") == pin,
            "Concrete axiom allowlist or toolchain mismatch")


def fixture_acknowledgement(full, index, acknowledgement):
    marker = (f"Original fixture {index}: concrete kernel checks, geometric, exclusion and "
              "termination theorem types, and axiom audit passed")
    require(full.splitlines().count(marker) == 1 and full.index(marker) > full.index(acknowledgement),
            f"Missing/out-of-order full-gate termination acknowledgement: {index}")


def wrong_type_controls(artifact, root, replay_tool):
    """Verify old controls and both isolated endpoint uses, each on its own evidence."""
    control_prefix = "lean/wrong-proof-type-control/"
    control = artifact.json(control_prefix + "receipt.json")
    for key in ("fixture_compiles", "typed_import_refuses", "no_strict_system_wrong_type_refused",
                *(name + "_wrong_type_refused" for name in TERMINATION_PROOFS)):
        require(control.get(key) is True, f"Unobserved wrong-type control: {key}")
    bad_fixture = (root / "tests/fixtures/c4_archived_bad_binding.lean").read_bytes()
    require(artifact.read(control_prefix + "Source0.lean") == bad_fixture
            and control.get("fixture_sha256") == sha(bad_fixture),
            "Wrong-type control source is not the exact candidate fixture")
    require(bool(artifact.read(control_prefix + "Source0.olean")),
            "Wrong-type fixture has no retained compiled object")
    require(artifact.text(control_prefix + "Audit0.lean") == replay_tool.audit_source(0),
            "Wrong-type full audit source changed")
    require(artifact.text(control_prefix + "ExclusionAudit0.lean")
            == "import Source0\n" + replay_tool.exclusion_type_check(0),
            "Exclusion-only control source changed")
    artifact.read(control_prefix + "compile.log")
    diagnostics_to_check = [("audit.log", "accepted"), ("exclusion-audit.log", "no_strict_system")]
    for name in TERMINATION_PROOFS:
        require(artifact.text(control_prefix + name + "_audit.lean")
                == "import Source0\n" + replay_tool.termination_type_check(0, name),
                f"Isolated {name} control source differs from the pinned auditor")
        diagnostics_to_check.append((name + "-audit.log", name))
    for file, name in diagnostics_to_check:
        diagnostics = artifact.text(control_prefix + file)
        require("type mismatch" in diagnostics.lower() and name in diagnostics,
                f"Wrong-type control lacks its intended type-mismatch diagnostic: {file}")
        require(not re.search(r"unknown (?:identifier|constant)", diagnostics, re.IGNORECASE),
                f"Wrong-type control has an unresolved-name error: {file}")
        if name in TERMINATION_PROOFS:
            require(all(other not in diagnostics for other in TERMINATION_PROOFS if other != name),
                    f"Isolated {name} diagnostic includes a different termination endpoint")
    return {name: True for name in TERMINATION_PROOFS}


def inspect(args, output):
    root = args.root.resolve(strict=True)
    artifact_root = args.artifact_root.resolve(strict=True)
    commit, tree = args.expected_commit, args.expected_tree
    source = git_source(root)
    require(source == {"commit": commit, "tree": tree, "status_porcelain": ""},
            "Inspector requires the exact clean candidate checkout")
    inputs = {"run-metadata.json": args.run_metadata.read_bytes(),
              "jobs-metadata.json": args.jobs_metadata.read_bytes(),
              "source-metadata.json": args.metadata.read_bytes()}
    run = json.loads(inputs["run-metadata.json"])
    jobs = json.loads(inputs["jobs-metadata.json"])
    metadata = json.loads(inputs["source-metadata.json"])
    job, steps = hosted_verdict(run, jobs, args.expected_run_id, commit)
    require(metadata.get("subject_revision") == commit and metadata.get("subject_tree") == tree,
            "Static review metadata has a different subject")
    require(set(metadata["allowed_axioms_for_later_compiled_audit"]) == ALLOWED,
            "Static metadata axiom allowlist changed")
    source_records = metadata_source_records(metadata)
    inventory = declaration_inventory(metadata)
    source_hashes = {}
    for item in source_records:
        require(item.get("repository") == REPOSITORY and item.get("revision") == commit,
                f"Unbound repository source metadata: {item.get('path')}")
        relative_path(item["path"])
        actual = file_sha(root / item["path"])
        require(actual == item["sha256"], f"Source metadata mismatch: {item['path']}")
        source_hashes[item["path"]] = actual
    pin = (root / "proof/PscVerif/lean-toolchain").read_text().strip()
    require(pin == metadata["lean_toolchain"] == "leanprover/lean4:v4.34.0-rc2", "Wrong Lean pin")
    lake_manifest = json.loads((root / "proof/PscVerif/lake-manifest.json").read_text())
    mathlib = [package for package in lake_manifest["packages"] if package["name"] == "mathlib"]
    require(len(mathlib) == 1 and mathlib[0]["rev"] == metadata["mathlib_revision"], "Wrong Mathlib pin")

    artifact = Artifact(artifact_root)
    require(artifact.text("revision.txt").splitlines() == [commit, tree], "Artifact revision/tree mismatch")
    archive_hash = file_sha(root / ARCHIVE)
    require(artifact.text("archive-sha256.txt").splitlines() == [archive_hash + "  " + ARCHIVE],
            "Artifact original-archive digest/name mismatch")
    archive = json.loads((root / ARCHIVE).read_text())
    addressed = json.loads((root / ADDRESSED_ARCHIVE).read_text())

    # Import only verified repository tooling. Never import or execute artifact
    # code, and never call replay.run or any compiler/oracle launch function.
    sys.path.insert(0, str(root / "tools"))
    proof_bank = load_source_module("hosted_verified_proof_bank", root / "tools/make_proof_bank.py")
    replay_tool = load_source_module("hosted_verified_replay_parser", root / "tools/replay_archived_payload_lean.py")
    replay_contract(replay_tool)
    bank = json.loads((root / "proof/proof-bank.json").read_text())
    expected_proofs = {(item["module"], item["name"]) for item in bank["lean_declarations"]}
    full = artifact.text("lean-audit.log")
    global_counts = proof_bank.check_audit(full, expected_proofs)
    acknowledgement = f"Lean axiom audit: {global_counts[0]} declarations, {global_counts[1]} theorems; all named proofs reached"
    require(full.splitlines().count(acknowledgement) == 1, "Missing/duplicate global proof-bank acknowledgement")
    completion_line = f"PSC_AUDIT_COMPLETE\t{global_counts[0]}\t{global_counts[1]}"
    require(full.index(completion_line) < full.index(acknowledgement), "Global audit acknowledgement precedes completion")
    rows = [line.split("\t") for line in full.splitlines() if line.startswith("PSC_AXIOMS\t")]
    selected = compiled_declarations(rows, inventory)

    receipt = artifact.json("lean/receipt.json")
    replay_receipt_header(receipt, pin)
    expected_hashes = {relative: file_sha(root / relative) for relative in REPLAY_SOURCES}
    require(receipt.get("source_sha256") == expected_hashes, "Concrete replay source manifest is incomplete or differs from candidate")
    require(re.fullmatch(r"[0-9a-f]{64}", receipt.get("exporter_sha256", "")) is not None,
            "Missing reported exporter executable identity")
    generated = receipt.get("sources", [])
    require([item.get("fixture") for item in generated] == [0, 1], "Missing or duplicate fixture source receipts")
    emitted = io.StringIO()
    emitted.write("schema c4-archived-payload-v1\n")
    fixture_results = []
    for index, item in enumerate(generated):
        prefix = f"lean/Source{index}"
        require(sha(artifact.read(prefix + ".lean")) == item.get("lean_sha256"), "Generated source hash mismatch")
        require(sha(artifact.read(f"lean/Audit{index}.log")) == item.get("audit_sha256"), "Fixture audit log hash mismatch")
        require(artifact.text(f"lean/Audit{index}.lean") == replay_tool.audit_source(index),
                f"Fixture {index} type/axiom audit source differs from pinned auditor")
        generated_object = artifact.read(prefix + ".olean")
        require(bool(generated_object), f"Fixture {index} has no retained compiled object")
        for required in (prefix + ".compile.log", prefix + ".exporter.log", f"lean/Audit{index}.stderr"):
            artifact.read(required)
        counts = replay_tool.extract_packet(index, artifact_root / f"lean/Audit{index}.log", emitted)
        require(all(item.get(key) == value for key, value in counts.items()), "Concrete audit counts differ from receipt")
        fixture_acknowledgement(full, index, acknowledgement)
        fixture_results.append({"fixture": index, **counts, "semantic_proofs": sorted(PROOFS),
                                "source_sha256": item["lean_sha256"], "audit_sha256": item["audit_sha256"],
                                "compiled_object_sha256": sha(generated_object)})
    packet = artifact.read("lean/lean-emitted-payload.txt")
    require(emitted.getvalue().encode() == packet, "Retained Lean-emitted packet differs from audited payload records")
    require(sha(packet) == receipt.get("complete_emitted_payload_sha256"), "Lean payload digest mismatch")
    lean_oracle_bytes = artifact.read("lean/oracle-receipt.json")
    require(sha(lean_oracle_bytes) == receipt.get("oracle_receipt_sha256"), "Lean oracle receipt digest mismatch")
    lean_oracle = json.loads(lean_oracle_bytes)
    verify_oracle(lean_oracle, packet, archive, addressed, "Lean-emitted")
    require(receipt.get("oracle_schema") == lean_oracle["schema"], "Lean oracle schema receipt mismatch")

    termination_controls = wrong_type_controls(artifact, root, replay_tool)

    native_packet = artifact.read("native-packet.txt")
    native = artifact.json("native-oracle-receipt.json")
    verify_oracle(native, native_packet, archive, addressed, "native")
    controls = native.get("observed_negative_controls", {})
    require(set(controls) == {"0", "1"}, "Missing native negative-control fixture results")
    for index in ("0", "1"):
        require(set(controls[index]) == NATIVE_CONTROLS, f"Wrong native mutation control set for fixture {index}")
        require(all(item.get("rejected") is True and bool(item.get("reason")) for item in controls[index].values()),
                f"A native mutation control did not reject for fixture {index}")
    native_tests = artifact.text("native-tests.log")
    require(re.search(r"archived payload full roundtrip\s+14233\s+69679", native_tests) is not None,
            "Native full-roundtrip test acknowledgement is missing")
    oracle_tests = artifact.text("oracle-tests.log")
    oracle_step = next(step for step in steps if step["name"] == "Independent payload and original graph replay")
    pytest_verdict = oracle_pytest_verdict(oracle_tests, oracle_step)
    pytest_verdict["log_sha256"] = sha(artifact.read("oracle-tests.log"))

    # The full checker continues after the global audit into payload replay.
    # Require its genuine final JSON summary instead of truncating that log.
    starts = [match.start() for match in re.finditer(r"(?m)^\{", full)]
    require(bool(starts), "Full gate log has no final concrete replay JSON")
    final_summary = json.loads(full[starts[-1]:])
    expected_summary = {key: value for key, value in receipt.items() if key not in {"sources", "source_sha256"}}
    require(final_summary == expected_summary, "Final full-gate summary is not the retained concrete replay receipt")
    require(starts[-1] > full.index("Original fixture 1:"), "Final replay summary precedes fixture completion")
    artifact.verify_unchanged()
    require(git_source(root) == source, "Source checkout changed during inspection")

    for name, data in inputs.items():
        (output / name).write_bytes(data)
    extracted = ("".join("\t".join(row) + "\n" for row in selected)).encode()
    (output / "compiled-new-declarations.log").write_bytes(extracted)
    manifest_bytes = json_bytes(artifact.manifest)
    (output / "artifact-manifest.json").write_bytes(manifest_bytes)
    run_fields = ("id", "run_number", "run_attempt", "name", "path", "event", "head_sha", "status",
                  "conclusion", "created_at", "updated_at", "run_started_at", "html_url", "url", "artifacts_url")
    job_fields = ("id", "run_id", "run_attempt", "name", "head_sha", "status", "conclusion",
                  "started_at", "completed_at", "html_url", "url")
    return {
        "schema": "c4-hosted-concrete-termination-inspection-v1", "inspected_at_utc": now(),
        "inspection_outcome": "verified_completed_hosted_acceptance_evidence",
        "source": source, "github_run_verdict": {key: run.get(key) for key in run_fields},
        "github_job_verdict": {key: job.get(key) for key in job_fields}, "critical_step_verdicts": steps,
        "run_metadata_sha256": sha(inputs["run-metadata.json"]),
        "jobs_metadata_sha256": sha(inputs["jobs-metadata.json"]),
        "source_metadata_sha256": sha(inputs["source-metadata.json"]),
        "artifact_identity": {"supplied_root": str(artifact_root),
            "workflow_declared_artifact_name": "original-c4-payload-" + commit,
            "file_count": len(artifact.manifest), "total_bytes": sum(item["bytes"] for item in artifact.manifest),
            "manifest_sha256": sha(manifest_bytes), "original_archive_sha256": archive_hash,
            "github_artifact_id_supplied": False,
            "binding_limit": "Input files identify the run/job and exact artifact content. GitHub artifact ID/download ZIP digest are not present in these inputs; retain the download provenance separately."},
        "global_audit": {"constants": global_counts[0], "theorems": global_counts[1],
                         "expected_named_proofs_reached": len(expected_proofs),
                         "acknowledgement": acknowledgement, "allowed_axioms": sorted(ALLOWED)},
        "new_declarations": {"all_owner_constants": len(selected),
                             "all_owner_theorems": sum(row[1] == "theorem" for row in selected),
                             "explicit_theorems_matched": 37, "explicit_definitions_matched": 4,
                             "extracted_rows_sha256": sha(extracted)},
        "concrete_fixtures": fixture_results, "exclusion_only_wrong_type_control_verified": True,
        "termination_wrong_type_controls_verified": termination_controls,
        "seed_and_reachable_termination_fixtures": [0, 1],
        "native_negative_controls_rejected": 32, "oracle_pytest": pytest_verdict,
        "native_payload_sha256": sha(native_packet), "lean_emitted_payload_sha256": sha(packet),
        "reported_exporter_sha256": receipt["exporter_sha256"],
        "lean_audit_log_sha256": sha(artifact.read("lean-audit.log")),
        "concrete_replay_receipt_sha256": sha(artifact.read("lean/receipt.json")),
        "verified_replay_source_sha256": expected_hashes, "verified_static_review_source_sha256": source_hashes,
        "workflow_source_sha256": file_sha(root / WORKFLOW), "inspector_sha256": file_sha(Path(__file__)),
        "no_local_gate_returncode_inferred": True, "lean_or_test_processes_launched_by_inspector": False,
        "scope": "Postprocessing of successful GitHub evidence for strict-system exclusion over arbitrary finite carriers of the two literal fixtures, plus coincidence termination for every ordered swap seed and its actual ChildNC descendants. No arbitrary unlisted starting block, universal path-termination bound, general C4/PSC conclusion, or independent human review.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("artifact-root", "run-metadata", "jobs-metadata", "metadata", "root", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--expected-commit", required=True)
    parser.add_argument("--expected-tree", required=True)
    parser.add_argument("--expected-run-id", type=int, required=True)
    args = parser.parse_args()
    if not re.fullmatch(r"[0-9a-f]{40}", args.expected_commit) or not re.fullmatch(r"[0-9a-f]{40}", args.expected_tree):
        parser.error("Expected commit and tree must be complete lowercase 40-character Git identities")
    if args.expected_run_id <= 0:
        parser.error("Expected run ID must be positive")
    output = args.output.resolve()
    for protected in (args.root.resolve(), args.artifact_root.resolve()):
        require(output != protected and protected not in output.parents,
                "Output must be outside both source checkout and input artifact")
    output.mkdir(parents=True, exist_ok=False)
    try:
        result = inspect(args, output)
    except Exception as exc:
        refusal = {"schema": "c4-hosted-concrete-termination-inspection-refusal-v1", "at_utc": now(),
                   "inspection_outcome": "refused", "error": f"{type(exc).__name__}: {exc}",
                   "expected_run_id": args.expected_run_id, "expected_commit": args.expected_commit,
                   "expected_tree": args.expected_tree,
                   "acceptance_claimed": False, "no_local_gate_returncode_inferred": True}
        (output / "refusal.json").write_bytes(json_bytes(refusal))
        print(json.dumps(refusal, indent=2), file=sys.stderr)
        return 1
    (output / "inspection.json").write_bytes(json_bytes(result))
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
