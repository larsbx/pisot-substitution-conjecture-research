#!/usr/bin/env python3
"""Inspect a downloaded/extracted packet artifact; never substitute for Lean.

Run at the source revision whose artifact is being inspected. The expected
revision is caller-supplied, not inferred from an artifact's own assertion.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import time

from replay_overlap_lean_packets import audit_source, extract_packet, ReplayIncomplete


def require(condition, message):
    if not condition:
        raise ReplayIncomplete(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit(root, artifact, revision, reconstruct=False):
    packet_dir = artifact / "c4-overlap-lean-packets"
    require((artifact / "c4-overlap-lean-revision.txt").read_text().strip() == revision,
            "wrong artifact revision")
    receipt = json.loads((packet_dir / "receipt.json").read_text())
    require(receipt["all_18_sources_verified"] is True and receipt["sources_verified"] == 18,
            "incomplete source domain")
    require([s["source"] for s in receipt["sources"]] == list(range(18)), "wrong source ordering")
    require(sha(root / "proof/PscVerif/PscVerif/OverlapPacket.lean") ==
            receipt["generic_packet_source_sha256"], "checker source mismatch")
    combined = io.StringIO()
    combined.write("schema c4-pair-overlap-class-v1\n")
    for record in receipt["sources"]:
        i = record["source"]
        require(sha(packet_dir / f"Source{i}.lean") == record["lean_sha256"], "source hash mismatch")
        require(sha(packet_dir / f"Source{i}.log") == record["audit_and_packet_log_sha256"],
                "log hash mismatch")
        require((packet_dir / f"Audit{i}.lean").read_text() == audit_source(i), "auditor source mismatch")
        counts = extract_packet(i, packet_dir / f"Source{i}.log", combined)
        require(all(counts[k] == record[k] for k in counts), "audit counts mismatch")
        for name in (f"Source{i}.stderr", f"Audit{i}.stderr", f"Source{i}.mojo.log"):
            require(not (packet_dir / name).read_bytes(), "nonempty diagnostics: "+name)
    packet = packet_dir / "lean-emitted-packet.txt"
    require(combined.getvalue().encode() == packet.read_bytes(), "re-extracted packet mismatch")
    require(sha(packet) == receipt["complete_packet_sha256"], "packet digest mismatch")
    expected = json.loads((root / "evidence/c4-pair-overlap-class-2026-11-05/receipt.json").read_text())
    require(json.loads((packet_dir / "oracle-receipt.json").read_text()) == expected,
            "stored oracle receipt mismatch")
    require(sum(s["states"] for s in expected["sources"]) == receipt["states"] and
            sum(s["occurrence_edges"] for s in expected["sources"]) == receipt["occurrence_edges"],
            "aggregate counts mismatch")
    result = {"schema": "c4-overlap-artifact-inspection-v1", "verified_revision": revision,
              "fresh_lean_kernel_run": False, "all_source_log_and_auditor_checks": True,
              "packet_sha256": sha(packet), "states": receipt["states"],
              "occurrence_edges": receipt["occurrence_edges"], "geometry_formalized": False,
              "independent_python_reconstruction": False,
              "hosted_per_source_combined_seconds": [s["seconds"] for s in receipt["sources"]],
              "source0_lean_bytes": (packet_dir / "Source0.lean").stat().st_size,
              "source0_olean_bytes": (packet_dir / "Source0.olean").stat().st_size}
    if reconstruct:
        start = time.monotonic()
        run = subprocess.run([sys.executable, str(root / "oracles/python/c4_pair_overlap_class.py"),
                              "--native", str(packet)], capture_output=True, text=True,
                             check=True, timeout=600)
        require(json.loads(run.stdout) == expected, "fresh oracle reconstruction mismatch")
        result["independent_python_reconstruction"] = True
        result["python_reconstruction_seconds"] = round(time.monotonic()-start, 3)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact", type=Path, required=True, help="Extracted ZIP root")
    parser.add_argument("--revision", required=True)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--reconstruct", action="store_true")
    args = parser.parse_args()
    print(json.dumps(audit(args.root.resolve(), args.artifact.resolve(), args.revision,
                           args.reconstruct), indent=2))
