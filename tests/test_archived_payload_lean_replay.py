"""Fail-closed controls for compiled archived-payload audit orchestration.

Synthetic log controls calibrate the parser; they are not Lean proof evidence.
Actual graph/address mutations are in the independent payload oracle suite.
"""
from io import StringIO
from pathlib import Path
import importlib.util
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("archived_replay", ROOT / "tools/replay_archived_payload_lean.py")
replay = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(replay)


class ArchivedAuditProtocol(unittest.TestCase):
    def sample(self):
        ns = "Psc.ArchivedPayloadGenerated.Source0"
        lines = [f"PSC_ARCHIVED_AXIOMS 0\t{ns}.{name}\tpropext" for name in sorted(replay.PROOFS)]
        lines += ["PSC_ARCHIVED_AUDIT_COMPLETE 0\t6\t6", "graph 0 2 16 8 0 7150"]
        lines += [f"{kind} 0 0" for kind in sorted(replay.RECORDS - {"graph"})]
        return "\n".join(lines) + "\n"

    def parse(self, content):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "audit.log"
            log.write_text(content)
            return replay.extract_packet(0, log, StringIO())

    def test_synthetic_complete_protocol(self):
        self.assertEqual(self.parse(self.sample()), {"declarations": 6, "theorem_declarations": 6})

    def test_every_nonstandard_transitive_axiom_refused(self):
        for axiom in ("sorryAx", "Lean.ofReduceBool", "_native.native_decide.ax", "User.unproved"):
            with self.subTest(axiom=axiom), self.assertRaises(replay.ReplayIncomplete):
                self.parse(self.sample().replace("propext", axiom))

    def test_missing_geometric_proof_refused(self):
        for name in ("domain_iff", "roots_null", "ancestors_null", "typed_accepted"):
            with self.subTest(name=name), self.assertRaises(replay.ReplayIncomplete):
                self.parse(self.sample().replace(f".{name}\t", ".wrong_name\t"))

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
        samples = (self.sample().replace("PSC_ARCHIVED_AUDIT_COMPLETE 0\t6\t6\n", ""),
                   self.sample().replace("0\t6\t6", "0\t7\t6"),
                   self.sample().replace("0\t6\t6", "0\t6\t5"),
                   self.sample().replace("0\t6\t6", "0\tx\t6"))
        for content in samples:
            with self.assertRaises(replay.ReplayIncomplete):
                self.parse(content)

    def test_unsupported_fixture_refused(self):
        for index in (-1, 2, 18):
            with self.assertRaises(replay.ReplayIncomplete):
                replay.audit_source(index)


if __name__ == "__main__":
    unittest.main()
