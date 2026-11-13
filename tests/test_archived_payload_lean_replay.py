"""Fail-closed controls for compiled archived-payload audit orchestration.

Synthetic log controls calibrate the parser; they are not Lean proof evidence.
Actual graph/address mutations are in the independent payload oracle suite.
"""
from io import StringIO
from pathlib import Path
import importlib.util
import json
import subprocess
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("archived_replay", ROOT / "tools/replay_archived_payload_lean.py")
replay = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(replay)


class ArchivedAuditProtocol(unittest.TestCase):
    def sample(self):
        ns = "Psc.ArchivedPayloadGenerated.Source0"
        lines = [f"PSC_ARCHIVED_AXIOMS 0\t{ns}.{name}\tpropext" for name in sorted(replay.PROOFS)]
        count = len(replay.PROOFS)
        lines += [f"PSC_ARCHIVED_AUDIT_COMPLETE 0\t{count}\t{count}", "graph 0 2 16 8 0 7150"]
        lines += [f"{kind} 0 0" for kind in sorted(replay.RECORDS - {"graph"})]
        return "\n".join(lines) + "\n"

    def parse(self, content):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "audit.log"
            log.write_text(content)
            return replay.extract_packet(0, log, StringIO())

    def test_synthetic_complete_protocol(self):
        count = len(replay.PROOFS)
        self.assertEqual(self.parse(self.sample()), {"declarations": count, "theorem_declarations": count})

    def test_every_nonstandard_transitive_axiom_refused(self):
        for axiom in ("sorryAx", "Lean.ofReduceBool", "_native.native_decide.ax", "User.unproved"):
            with self.subTest(axiom=axiom), self.assertRaises(replay.ReplayIncomplete):
                self.parse(self.sample().replace("propext", axiom))

    def test_every_semantic_proof_required(self):
        for name in replay.PROOFS:
            with self.subTest(name=name), self.assertRaises(replay.ReplayIncomplete):
                self.parse(self.sample().replace(f".{name}\t", ".wrong_name\t"))

    def test_previous_protocol_without_exclusion_refused(self):
        count = len(replay.PROOFS)
        legacy = "\n".join(line for line in self.sample().splitlines()
                           if ".no_strict_system\t" not in line)
        legacy = legacy.replace(f"0\t{count}\t{count}", f"0\t{count - 1}\t{count - 1}")
        with self.assertRaises(replay.ReplayIncomplete):
            self.parse(legacy)

    def test_previous_seven_proof_protocol_without_termination_refused(self):
        count = len(replay.PROOFS)
        legacy = "\n".join(line for line in self.sample().splitlines()
                           if not any(f".{name}\t" in line for name in replay.TERMINATION_PROOFS))
        legacy = legacy.replace(f"0\t{count}\t{count}", "0\t7\t7")
        with self.assertRaises(replay.ReplayIncomplete):
            self.parse(legacy)

    def test_each_termination_proof_required_even_with_adjusted_counts(self):
        count = len(replay.PROOFS)
        for name in replay.TERMINATION_PROOFS:
            omitted = "\n".join(line for line in self.sample().splitlines()
                                if f".{name}\t" not in line)
            omitted = omitted.replace(f"0\t{count}\t{count}", f"0\t{count - 1}\t{count - 1}")
            with self.subTest(name=name), self.assertRaises(replay.ReplayIncomplete):
                self.parse(omitted)

    def test_every_data_family_is_required(self):
        for kind in replay.RECORDS:
            content = "\n".join(line for line in self.sample().splitlines()
                                if not line.startswith(kind + " "))
            with self.subTest(kind=kind), self.assertRaises(replay.ReplayIncomplete):
                self.parse(content)

    def test_wrong_source_duplicate_and_stale_output_refused(self):
        first = self.sample().splitlines()[0] + "\n"
        samples = (first + self.sample(), self.sample().replace("slot 0", "slot 1"),
                   self.sample().replace("lookup 0", "lookup 1"),
                   self.sample() + "ACCEPTED without compiled proof\n",
                   self.sample() + "graph 0 7150\n", self.sample() + first)
        for content in samples:
            with self.subTest(content=content[-70:]), self.assertRaises(replay.ReplayIncomplete):
                self.parse(content)

    def test_missing_or_false_completion_refused(self):
        count = len(replay.PROOFS)
        completion = f"0\t{count}\t{count}"
        samples = (self.sample().replace(f"PSC_ARCHIVED_AUDIT_COMPLETE {completion}\n", ""),
                   self.sample().replace(completion, f"0\t{count + 1}\t{count}"),
                   self.sample().replace(completion, f"0\t{count}\t{count - 1}"),
                   self.sample().replace(completion, f"0\tx\t{count}"))
        for content in samples:
            with self.assertRaises(replay.ReplayIncomplete):
                self.parse(content)

    def test_unsupported_fixture_refused(self):
        for index in (-1, 2, 18):
            with self.assertRaises(replay.ReplayIncomplete):
                replay.audit_source(index)
            with self.assertRaises(replay.ReplayIncomplete):
                replay.exclusion_type_check(index)
            for name in replay.TERMINATION_PROOFS:
                with self.assertRaises(replay.ReplayIncomplete):
                    replay.termination_type_check(index, name)
        with self.assertRaises(replay.ReplayIncomplete):
            replay.termination_type_check(0, "unsupported_endpoint")


class ArchivedTerminationControlOrchestration(unittest.TestCase):
    """Mock compiler outcomes test orchestration only, never mathematical acceptance."""

    def run_control(self, output, overrides=None):
        overrides = overrides or {}

        def compile_result(command, **kwargs):
            filename = Path(command[-1]).name
            if filename == "Source0.lean":
                return subprocess.CompletedProcess(command, 0, "", "")
            declaration = {
                "Audit0.lean": "accepted",
                "ExclusionAudit0.lean": "no_strict_system",
                "seed_terminates_audit.lean": "seed_terminates",
                "reachable_terminates_audit.lean": "reachable_terminates",
            }[filename]
            code, message = overrides.get(filename, (1, f"type mismatch: {declaration}"))
            return subprocess.CompletedProcess(command, code, message, "")

        with patch.object(replay.subprocess, "run", side_effect=compile_result) as runner:
            replay.validate_negative_control(ROOT, ROOT, output, "test-pin", "test-lean-path")
        return runner

    def test_both_endpoint_controls_run_independently(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            runner = self.run_control(output)
            calls = [Path(call.args[0][-1]).name for call in runner.call_args_list]
            self.assertEqual(calls[-2:], ["seed_terminates_audit.lean", "reachable_terminates_audit.lean"])
            receipt = json.loads((output / "wrong-proof-type-control/receipt.json").read_text())
            for name in replay.TERMINATION_PROOFS:
                self.assertIs(receipt[f"{name}_wrong_type_refused"], True)

    def test_endpoint_success_or_unrelated_failure_never_earns_control_credit(self):
        for name in replay.TERMINATION_PROOFS:
            outcomes = ((0, f"type mismatch: {name}"),
                        (1, f"unknown identifier: {name}"),
                        (1, "type mismatch: no_strict_system"))
            for outcome in outcomes:
                with self.subTest(name=name, outcome=outcome), tempfile.TemporaryDirectory() as directory:
                    output = Path(directory)
                    with self.assertRaises(replay.ReplayIncomplete):
                        self.run_control(output, {f"{name}_audit.lean": outcome})
                    self.assertFalse((output / "wrong-proof-type-control/receipt.json").exists())


if __name__ == "__main__":
    unittest.main()
