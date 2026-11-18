"""Contract and mutation tests for the prepared hosted-evidence inspector.

Synthetic receipts, audit rows, diagnostics, and object placeholders exercise
refusal behavior only. These tests never construct or accept a complete hosted
artifact, launch Lean, or supply mathematical acceptance evidence.
"""
from __future__ import annotations

import ast
import copy
import importlib.util
import json
import os
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest

HERE = Path(__file__).resolve().parent
ROOT = Path(os.environ.get("PSC_INSPECTOR_CANDIDATE_ROOT",
    "/workspace/scratch/91efcf4b7b58/psc-source-6021f042")).resolve()
METADATA = Path(os.environ.get("PSC_INSPECTOR_SOURCE_METADATA",
    str(HERE / "source-metadata-6021f042.json"))).resolve()
PIN = "leanprover/lean4:v4.34.0-rc2"


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


inspector = load("prepared_inspector_tests", HERE / "inspect-hosted-concrete-termination-audit.py")
replay = load("candidate_replay_contract_tests", ROOT / "tools/replay_archived_payload_lean.py")
OLD_PROOFS = {"valid", "accepted", "typed_accepted", "domain_iff", "roots_null",
              "ancestors_null", "no_strict_system"}
ENDPOINTS = ("seed_terminates", "reachable_terminates")


def receipt():
    return {
        "schema": "c4-archived-payload-lean-replay-v1",
        "both_original_fixtures_verified": True, "fixtures_verified": 2,
        "strict_system_exclusion_fixtures": [0, 1],
        "seed_and_reachable_termination_fixtures": [0, 1],
        "semantic_proofs": sorted(OLD_PROOFS | set(ENDPOINTS)),
        "allowed_axioms": ["Classical.choice", "Quot.sound", "propext"],
        "lean_toolchain": PIN,
    }


class EndpointContractTests(unittest.TestCase):
    def test_current_parser_and_nine_proof_receipt_contracts(self):
        inspector.replay_contract(replay)
        inspector.replay_receipt_header(receipt(), PIN)

    def test_old_seven_proof_contract_refused_even_with_new_flags(self):
        old_parser = SimpleNamespace(PROOFS=OLD_PROOFS, ALLOWED=replay.ALLOWED,
                                     TERMINATION_PROOFS=ENDPOINTS)
        with self.assertRaises(inspector.InspectionRefused):
            inspector.replay_contract(old_parser)
        old = receipt()
        old["semantic_proofs"] = sorted(OLD_PROOFS)
        with self.assertRaises(inspector.InspectionRefused):
            inspector.replay_receipt_header(old, PIN)

    def test_each_semantic_proof_is_required(self):
        for name in receipt()["semantic_proofs"]:
            bad = receipt()
            bad["semantic_proofs"].remove(name)
            with self.subTest(name=name), self.assertRaises(inspector.InspectionRefused):
                inspector.replay_receipt_header(bad, PIN)

    def test_termination_fixture_results_cannot_be_missing_partial_or_reversed(self):
        for value in (None, [], [0], [1], [1, 0], [0, 0], [0, 1, 2], True):
            bad = receipt()
            if value is None:
                del bad["seed_and_reachable_termination_fixtures"]
            else:
                bad["seed_and_reachable_termination_fixtures"] = value
            with self.subTest(value=value), self.assertRaises(inspector.InspectionRefused):
                inspector.replay_receipt_header(bad, PIN)

    def test_old_fixture_and_axiom_guards_remain(self):
        for key, value in (("both_original_fixtures_verified", False), ("fixtures_verified", 1),
                           ("strict_system_exclusion_fixtures", [0]),
                           ("allowed_axioms", ["sorryAx"]), ("lean_toolchain", "wrong-pin")):
            bad = receipt()
            bad[key] = value
            with self.subTest(key=key), self.assertRaises(inspector.InspectionRefused):
                inspector.replay_receipt_header(bad, PIN)

    def test_new_full_log_markers_required_once_after_global_acknowledgement(self):
        acknowledgement = "synthetic global audit acknowledgement"
        for index in (0, 1):
            new = (f"Original fixture {index}: concrete kernel checks, geometric, exclusion and "
                   "termination theorem types, and axiom audit passed")
            old = (f"Original fixture {index}: concrete kernel checks, geometric and exclusion "
                   "theorem types, and axiom audit passed")
            inspector.fixture_acknowledgement(acknowledgement + "\n" + new + "\n", index, acknowledgement)
            for full in (acknowledgement + "\n" + old + "\n",
                         new + "\n" + acknowledgement + "\n",
                         acknowledgement + "\n" + new + "\n" + new + "\n"):
                with self.subTest(index=index, full=full), self.assertRaises(inspector.InspectionRefused):
                    inspector.fixture_acknowledgement(full, index, acknowledgement)


class SourceAndDeclarationTests(unittest.TestCase):
    def setUp(self):
        self.metadata = json.loads(METADATA.read_bytes())

    def test_fresh_source_metadata_and_all_35_git_bound_bytes(self):
        records = inspector.metadata_source_records(self.metadata)
        inventory = inspector.declaration_inventory(self.metadata)
        self.assertEqual(len(records), 35)
        self.assertEqual(len(inventory), 41)
        source = inspector.git_source(ROOT)
        self.assertEqual(source, {"commit": self.metadata["subject_revision"],
                                  "tree": self.metadata["subject_tree"], "status_porcelain": ""})
        for item in records:
            with self.subTest(path=item["path"]):
                self.assertEqual(item["repository"], inspector.REPOSITORY)
                self.assertEqual(item["revision"], source["commit"])
                self.assertEqual(inspector.file_sha(ROOT / item["path"]), item["sha256"])

    def test_exact_replay_manifest_matches_actual_candidate_producer(self):
        tree = ast.parse((ROOT / "tools/replay_archived_payload_lean.py").read_text())
        assignments = [node for node in ast.walk(tree) if isinstance(node, ast.Assign)
                       and any(isinstance(target, ast.Name) and target.id == "relative_sources"
                               for target in node.targets)]
        self.assertEqual(len(assignments), 1)
        paths = ast.literal_eval(assignments[0].value)
        self.assertEqual(len(paths), 25)
        self.assertEqual(tuple(paths), inspector.REPLAY_SOURCES)

    def test_all_37_named_theorems_match_the_exact_candidate_proof_bank(self):
        bank = json.loads((ROOT / "proof/proof-bank.json").read_bytes())
        owners = set(inspector.EXPECTED_MODULE_PATHS.values())
        actual = {(d["module"], d["name"]) for d in bank["lean_declarations"] if d["module"] in owners}
        expected = {identity for identity, kind in inspector.EXPECTED_DECLARATIONS.items() if kind == "theorem"}
        self.assertEqual(len(actual), 37)
        self.assertEqual(actual, expected)

    def test_each_metadata_path_required_and_duplicates_and_extras_refused(self):
        for group in ("modules", "reviewed_repository_dependencies_and_audit_sources", "changed_nonproof_sources"):
            for index in range(len(self.metadata[group])):
                bad = copy.deepcopy(self.metadata)
                missing = bad[group].pop(index)["path"]
                with self.subTest(missing=missing), self.assertRaises(inspector.InspectionRefused):
                    inspector.metadata_source_records(bad)
        for path in (self.metadata["modules"][0]["path"], "unreviewed-extra-source.py"):
            bad = copy.deepcopy(self.metadata)
            bad["changed_nonproof_sources"].append({"path": path})
            with self.subTest(path=path), self.assertRaises(inspector.InspectionRefused):
                inspector.metadata_source_records(bad)

    def test_each_explicit_static_declaration_required(self):
        for module_index, module in enumerate(self.metadata["modules"]):
            for declaration_index, declaration in enumerate(module["declarations"]):
                bad = copy.deepcopy(self.metadata)
                del bad["modules"][module_index]["declarations"][declaration_index]
                with self.subTest(name=declaration["name"]), self.assertRaises(inspector.InspectionRefused):
                    inspector.declaration_inventory(bad)

    def test_duplicate_wrong_owner_wrong_kind_and_private_inventory_refused(self):
        for mutation in ("duplicate", "owner", "kind", "private", "module", "missing_module"):
            bad = copy.deepcopy(self.metadata)
            module = bad["modules"][0]
            declaration = module["declarations"][0]
            if mutation == "duplicate":
                module["declarations"][1] = copy.deepcopy(declaration)
            elif mutation == "owner":
                declaration["owner"] = "PscVerif.Unreviewed"
            elif mutation == "kind":
                declaration["expected_compiled_kind"] = "declaration"
            elif mutation == "private":
                declaration["private"] = True
            elif mutation == "module":
                module["module"] = "PscVerif.Unreviewed"
            else:
                del module["module"]
            with self.subTest(mutation=mutation), self.assertRaises(inspector.InspectionRefused):
                inspector.declaration_inventory(bad)

    def test_each_compiled_explicit_declaration_required(self):
        inventory = inspector.declaration_inventory(self.metadata)
        rows = [["PSC_AXIOMS", d["expected_compiled_kind"], d["owner"], d["name"], d["name"], "propext"]
                for d in inventory]
        self.assertEqual(len(inspector.compiled_declarations(rows, inventory)), 41)
        for index, declaration in enumerate(inventory):
            with self.subTest(name=declaration["name"]), self.assertRaises(inspector.InspectionRefused):
                inspector.compiled_declarations(rows[:index] + rows[index + 1:], inventory)
        with self.assertRaises(inspector.InspectionRefused):
            inspector.compiled_declarations(rows + [rows[0]], inventory)
        for column, value in ((1, "declaration"), (2, "PscVerif.OtherOwner"), (3, "private.different_name")):
            bad = copy.deepcopy(rows)
            bad[0][column] = value
            with self.subTest(column=column), self.assertRaises(inspector.InspectionRefused):
                inspector.compiled_declarations(bad, inventory)


class IndependentWrongTypeControlTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.prefix = self.root / "lean/wrong-proof-type-control"
        self.prefix.mkdir(parents=True)
        fixture = (ROOT / "tests/fixtures/c4_archived_bad_binding.lean").read_bytes()
        self.files = {
            "Source0.lean": fixture,
            # Presence-only placeholder: never passed to Lean or represented as a compiled proof.
            "Source0.olean": b"SYNTHETIC OBJECT PRESENCE PLACEHOLDER, NOT A LEAN OBJECT\n",
            "compile.log": b"",
            "Audit0.lean": replay.audit_source(0).encode(),
            "ExclusionAudit0.lean": ("import Source0\n" + replay.exclusion_type_check(0)).encode(),
            "audit.log": b"synthetic type mismatch: Source0.accepted\n",
            "exclusion-audit.log": b"synthetic type mismatch: Source0.no_strict_system\n",
        }
        flags = {"fixture_compiles": True, "typed_import_refuses": True,
                 "no_strict_system_wrong_type_refused": True, "fixture_sha256": inspector.sha(fixture)}
        for name in ENDPOINTS:
            flags[name + "_wrong_type_refused"] = True
            self.files[name + "_audit.lean"] = ("import Source0\n" + replay.termination_type_check(0, name)).encode()
            self.files[name + "-audit.log"] = f"synthetic type mismatch: Source0.{name}\n".encode()
        self.files["receipt.json"] = json.dumps(flags).encode()
        self.restore()

    def tearDown(self):
        self.temp.cleanup()

    def restore(self):
        for path in self.prefix.iterdir():
            path.unlink()
        for name, data in self.files.items():
            (self.prefix / name).write_bytes(data)

    def verify(self):
        return inspector.wrong_type_controls(inspector.Artifact(self.root), ROOT, replay)

    def test_independent_control_file_contract_only(self):
        self.assertEqual(self.verify(), {name: True for name in ENDPOINTS})
        self.assertFalse((self.root / "inspection.json").exists())

    def test_each_endpoint_flag_required_independently(self):
        for name in ENDPOINTS:
            for value in (None, False):
                self.restore()
                flags = json.loads(self.files["receipt.json"])
                if value is None:
                    del flags[name + "_wrong_type_refused"]
                else:
                    flags[name + "_wrong_type_refused"] = value
                (self.prefix / "receipt.json").write_text(json.dumps(flags))
                with self.subTest(name=name, value=value), self.assertRaises(inspector.InspectionRefused):
                    self.verify()

    def test_each_endpoint_source_and_log_required_independently(self):
        for name in ENDPOINTS:
            for suffix in ("_audit.lean", "-audit.log"):
                self.restore()
                (self.prefix / (name + suffix)).unlink()
                with self.subTest(name=name, suffix=suffix), self.assertRaises(inspector.InspectionRefused):
                    self.verify()

    def test_wrong_or_combined_control_source_is_refused(self):
        for name in ENDPOINTS:
            for source in (self.files["Audit0.lean"], self.files[ENDPOINTS[1 - ENDPOINTS.index(name)] + "_audit.lean"]):
                self.restore()
                (self.prefix / (name + "_audit.lean")).write_bytes(source)
                with self.subTest(name=name, source=source), self.assertRaises(inspector.InspectionRefused):
                    self.verify()

    def test_other_failure_or_combined_failure_cannot_credit_an_endpoint(self):
        for name in ENDPOINTS:
            other = ENDPOINTS[1 - ENDPOINTS.index(name)]
            for diagnostics in ("", "synthetic type mismatch: accepted\n",
                                f"synthetic type mismatch: {other}\n",
                                f"unknown identifier {name}\n",
                                f"type mismatch {name}; unknown constant Unavailable\n",
                                f"type mismatch {name}\ntype mismatch {other}\n"):
                self.restore()
                (self.prefix / (name + "-audit.log")).write_text(diagnostics)
                with self.subTest(name=name, diagnostics=diagnostics), self.assertRaises(inspector.InspectionRefused):
                    self.verify()

    def test_old_control_sources_logs_and_compiled_fixture_remain_required(self):
        for filename in ("Source0.lean", "Source0.olean", "Audit0.lean", "ExclusionAudit0.lean",
                         "compile.log", "audit.log", "exclusion-audit.log"):
            self.restore()
            (self.prefix / filename).unlink()
            with self.subTest(filename=filename), self.assertRaises(inspector.InspectionRefused):
                self.verify()
        self.restore()
        (self.prefix / "Source0.olean").write_bytes(b"")
        with self.assertRaises(inspector.InspectionRefused):
            self.verify()


class HostedVerdictTests(unittest.TestCase):
    def setUp(self):
        self.commit = "1" * 40
        self.run = {"id": 123, "repository": {"full_name": inspector.REPOSITORY},
                    "head_sha": self.commit, "path": inspector.WORKFLOW,
                    "name": inspector.WORKFLOW_NAME, "status": "completed",
                    "conclusion": "success", "run_attempt": 1}
        self.job = {"name": inspector.JOB_NAME, "run_id": 123, "head_sha": self.commit,
                    "run_attempt": 1, "status": "completed", "conclusion": "success",
                    "completed_at": "synthetic timestamp",
                    "steps": [{"name": name, "status": "completed", "conclusion": "success",
                               "completed_at": "synthetic timestamp"} for name in inspector.REQUIRED_STEPS]}

    def verify(self):
        return inspector.hosted_verdict(self.run, {"total_count": 1, "jobs": [self.job]}, 123, self.commit)

    def test_nonterminal_or_failed_runs_never_pass(self):
        for status, conclusion in (("in_progress", None), ("queued", None),
                                   ("completed", "failure"), ("completed", "cancelled")):
            self.run.update(status=status, conclusion=conclusion)
            with self.subTest(status=status, conclusion=conclusion), self.assertRaises(inspector.InspectionRefused):
                self.verify()

    def test_wrong_head_attempt_and_unsuccessful_critical_step_refused(self):
        for mutation in ("head", "attempt", "step"):
            job = copy.deepcopy(self.job)
            if mutation == "head":
                job["head_sha"] = "2" * 40
            elif mutation == "attempt":
                job["run_attempt"] = 2
            else:
                job["steps"][-1]["conclusion"] = "skipped"
            with self.subTest(mutation=mutation), self.assertRaises(inspector.InspectionRefused):
                inspector.hosted_verdict(self.run, {"total_count": 1, "jobs": [job]}, 123, self.commit)


if __name__ == "__main__":
    unittest.main(verbosity=2)
