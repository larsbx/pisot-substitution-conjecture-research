#!/usr/bin/env python3
"""Verify the recorded Lean audit against this checkout's actual source closure.

This is evidence administration, not an executable mathematical oracle. The
Lean entry point performs the axiom check; the existing proof-bank checker
validates its receipts. Here we additionally require complete source coverage
and exact source hashes, so a partial or stale log cannot count as acceptance.
"""

from pathlib import Path
import argparse
import gzip
import hashlib
import json
import re
import sys


PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[1]
PROJECT = ROOT / "proof/PscVerif"
sys.path.insert(0, str(ROOT / "tools"))
from make_proof_bank import check_audit, lean_code, lean_declarations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit-log", type=Path, default=PACKET / "lean-audit.log.gz")
    args = parser.parse_args()
    bindings = json.loads((PACKET / "source-bindings.json").read_text())
    for relative, expected in bindings["files"].items():
        actual = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError("source changed after binding: " + relative)

    visited = set()

    def visit(module):
        if module in visited:
            return
        visited.add(module)
        path = PROJECT / (module.replace(".", "/") + ".lean")
        code = lean_code(path.read_text())
        for match in re.finditer(r"(?m)^\s*(?:public\s+)?import\s+([^\n]+)$", code):
            for dependency in match[1].split():
                if dependency == "PscVerif" or dependency.startswith("PscVerif."):
                    visit(dependency)

    visit("EvenRankTwoAudit")
    modules = {m for m in visited if m == "PscVerif" or m.startswith("PscVerif.")}
    expected = {(d["module"], d["name"]) for d in lean_declarations(ROOT)
                if d["module"] in modules}
    recorded = json.loads((PACKET / "audit-expected.json").read_text())
    if set(recorded["modules"]) != modules:
        raise ValueError("recorded module closure differs from source")
    if {tuple(p) for p in recorded["named_theorems"]} != expected:
        raise ValueError("recorded named-proof inventory differs from source")

    log = (gzip.decompress(args.audit_log.read_bytes()).decode("utf-8")
           if args.audit_log.suffix == ".gz" else args.audit_log.read_text())
    declarations, theorems = check_audit(log, expected)
    reached = {line.split("\t")[2] for line in log.splitlines()
               if line.startswith("PSC_AXIOMS\t")}
    if reached != modules:
        raise ValueError("compiled module coverage differs from source closure")
    new_modules = {"PscVerif.EvenCompanionWords", "PscVerif.EvenCompanionFamily",
                   "PscVerif.EvenSeamCycles", "PscVerif.PeriodicPartnerEvenSolenoid"}
    new = {p for p in expected if p[0] in new_modules}
    if {tuple(p) for p in recorded["new_named_theorems"]} != new:
        raise ValueError("recorded new-proof inventory differs from source")
    print("PSC_EVEN_SOURCE_BINDINGS_VERIFIED", len(bindings["files"]), sep="\t")
    print("PSC_EVEN_AUDIT_VERIFIED", len(modules), declarations, theorems,
          len(expected), len(new), sep="\t")
    for module in sorted(new_modules):
        print("PSC_EVEN_NEW_NAMED_PROOFS", module,
              sum(m == module for m, _ in new), sep="\t")
    print("PSC_EVEN_ACCEPTANCE_COMPLETE\tcomplete-local-closure\tstandard-axioms-only")


if __name__ == "__main__":
    main()
