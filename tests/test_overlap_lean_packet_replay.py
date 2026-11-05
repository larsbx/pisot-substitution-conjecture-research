"""Provenance-parser controls; synthetic logs are not native/Lean evidence."""
from io import StringIO
from pathlib import Path
import importlib.util
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("packet_replay", ROOT / "tools/replay_overlap_lean_packets.py")
replay = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(replay)


class PacketAuditProtocol(unittest.TestCase):
    def sample(self):
        return ("PSC_PACKET_AXIOMS 0\tPscVerif.OverlapGenerated.Source0.accepted\tpropext\n"
                "PSC_PACKET_AXIOMS 0\tPscVerif.OverlapGenerated.Source0.typed_accepted\t\n"
                "PSC_PACKET_AUDIT_COMPLETE 0\t2\t2\n"
                "graph 0 3 0 0 0 0 102 20\n")

    def parse(self, text):
        with tempfile.TemporaryDirectory() as d:
            log = Path(d) / "audit.log"
            log.write_text(text)
            return replay.extract_packet(0, log, StringIO())

    def test_synthetic_protocol_calibration(self):
        self.assertEqual(self.parse(self.sample()), {"declarations": 2, "theorem_declarations": 2})

    def test_admissions_and_native_reduction_axioms_refused(self):
        for ax in ("sorryAx", "Lean.ofReduceBool", "User.claim"):
            with self.subTest(ax=ax), self.assertRaises(replay.ReplayIncomplete):
                self.parse(self.sample().replace("propext", ax))

    def test_missing_proof_or_completion_refused(self):
        for bad in (self.sample().replace(".accepted\t", ".other\t"),
                    self.sample().replace("PSC_PACKET_AUDIT_COMPLETE 0\t2\t2\n", "")):
            with self.assertRaises(replay.ReplayIncomplete):
                self.parse(bad)

    def test_duplicates_stale_sources_and_unexpected_output_refused(self):
        first = self.sample().splitlines()[0]+"\n"
        for bad in (first+self.sample(), self.sample().replace("graph 0", "graph 1"),
                    self.sample()+"CERTIFIED without a proof\n"):
            with self.assertRaises(replay.ReplayIncomplete):
                self.parse(bad)

    def test_audit_counts_must_match(self):
        with self.assertRaises(replay.ReplayIncomplete):
            self.parse(self.sample().replace("0\t2\t2", "0\t3\t2"))


if __name__ == "__main__":
    unittest.main()
