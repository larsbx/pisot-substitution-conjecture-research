"""Canonical source-0 packet mutations and synthetic audit-protocol controls.

Runtime serialization tests and synthetic logs are not new Lean proof evidence.
"""
from io import StringIO
from pathlib import Path
import hashlib
import importlib.util
import json
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("packet_replay", ROOT / "tools/replay_overlap_lean_packets.py")
replay = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(replay)
sys.path.insert(0, str(ROOT / "oracles/python"))
import c4_pair_overlap_class as oracle


class CanonicalPacketMutations(unittest.TestCase):
    """Real source-0 serialization controls, through the production parity path.

    These are runtime refinement tests, not additional Lean proofs. In
    particular omission/collapse can pass the integer checker and must be
    caught by reconstruction of the complete occurrence packet.
    """
    @classmethod
    def setUpClass(cls):
        cls.graph, cls.weights, sweeps, _ = oracle.reference(0)
        cls.lines = list(oracle.packet_lines(cls.graph, cls.weights, sweeps))
        cls.parallel = next(i for i, row in enumerate(cls.graph.rows)
                            if len(row) > len(set(row)))

    def verify(self, lines):
        stream = StringIO("\n".join(lines) + "\n")
        oracle.verify_source_stream(stream, 0)
        self.assertEqual(stream.read(), "")

    def with_row(self, row_id, targets):
        lines = self.lines.copy()
        lines[2 + 2*row_id] = " ".join(map(str, ("row", 0, row_id, len(targets), *targets)))
        # Keep the original canonical header so comparison reaches the changed
        # occurrence row. A summary-only comparison would miss this mutation.
        return lines

    def test_genuine_source0_packet_matches_committed_digest(self):
        self.verify(self.lines)
        expected = json.loads((ROOT / "evidence/c4-pair-overlap-class-2026-11-05/receipt.json").read_text())
        digest = hashlib.sha256(("\n".join(self.lines)+"\n").encode()).hexdigest()
        self.assertEqual(digest, expected["sources"][0]["canonical_graph_sha256"])

    def test_omitted_duplicated_and_collapsed_occurrences_refused(self):
        row = self.graph.rows[self.parallel]
        for targets in (row[:-1], row + [row[0]], list(dict.fromkeys(row))):
            with self.subTest(target_count=len(targets)), self.assertRaises(oracle.core.InvalidCertificate):
                self.verify(self.with_row(self.parallel, targets))
        # Explicitly pin the boundary: omission and collapse only lower row
        # sums, so integer inequalities alone cannot authenticate these graphs.
        for targets in (row[:-1], list(dict.fromkeys(row))):
            self.assertLessEqual(20*sum(self.weights[j] for j in targets),
                                 102*self.weights[self.parallel])

    def test_in_range_wrong_target_refused_even_with_equal_weight(self):
        by_weight = {}
        for j, weight in enumerate(self.weights):
            by_weight.setdefault(weight, []).append(j)
        row_id, position = next((i, k) for i, targets in enumerate(self.graph.rows)
                                for k, target in enumerate(targets)
                                if len(by_weight[self.weights[target]]) > 1)
        row = self.graph.rows[row_id].copy()
        old = row[position]
        replacement = next(j for j in by_weight[self.weights[old]] if j != old)
        row[position] = replacement
        self.assertEqual(sum(self.weights[j] for j in row),
                         sum(self.weights[j] for j in self.graph.rows[row_id]))
        with self.assertRaises(oracle.core.InvalidCertificate):
            self.verify(self.with_row(row_id, row))

    def test_corrupted_positive_or_zero_weights_refused(self):
        for weight in (0, self.weights[0]+1):
            lines = self.lines.copy()
            fields = lines[1].split()
            fields[-1] = str(weight)
            lines[1] = " ".join(fields)
            with self.assertRaises(oracle.core.InvalidCertificate):
                self.verify(lines)

    def test_state_order_missing_row_and_truncation_refused(self):
        reordered = self.lines.copy()
        left, right = reordered[1].split(), reordered[3].split()
        left[3:8], right[3:8] = right[3:8], left[3:8]
        reordered[1], reordered[3] = " ".join(left), " ".join(right)
        for lines in (reordered, self.lines[:2]+self.lines[3:], self.lines[:-1], self.lines[:1]):
            with self.assertRaises(oracle.core.InvalidCertificate):
                self.verify(lines)

    def test_incomplete_full_class_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "only-source0.txt"
            path.write_text("schema "+oracle.SCHEMA+"\n"+"\n".join(self.lines)+"\n")
            with self.assertRaises(oracle.core.InvalidCertificate):
                oracle.verify_native_file(path)


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
