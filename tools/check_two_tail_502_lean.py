#!/usr/bin/env python3
"""Governance runner only: Lean, not Python, decides all mathematics."""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PROJECT = ROOT / "proof/PscVerif"
SOURCES = PROJECT / "PscVerif/TwoTail502"

def command(args, cwd=ROOT):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--expected-revision", required=True)
    parser.add_argument("--output", required=True, type=pathlib.Path)
    args = parser.parse_args()
    if not re.fullmatch(r"[0-9a-f]{40}", args.expected_revision):
        raise SystemExit("expected revision must be a full commit SHA")
    revision = command(["git", "rev-parse", "HEAD"])
    if revision != args.expected_revision or command(["git", "status", "--porcelain"]):
        raise SystemExit("refusing a dirty or unreviewed starting revision")
    args.output.mkdir(parents=True, exist_ok=True)
    files = sorted(SOURCES.glob("*.lean"))
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    receipt = {"revision": revision, "source_sha256": hashes, "status": "running",
               "scope": "PR502 exact source words only; no PSC promotion",
               "lean": command(["lean", "--version"], PROJECT), "commands": []}
    receipt_path = args.output / "receipt.json"
    def save():
        receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    save()
    try:
        for p in files:
            # This source set admits no unproved declaration or alternate evaluator.
            source = p.read_text()
            if re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", source):
                raise RuntimeError("forbidden proof escape in " + str(p))
        modules = ["PscVerif.TwoTail502." + p.stem for p in files]
        cmd = ["lake", "build"] + modules
        receipt["commands"].append(cmd)
        with (args.output / "build.log").open("w") as log:
            result = subprocess.run(cmd, cwd=PROJECT, stdout=log, stderr=subprocess.STDOUT)
        print((args.output / "build.log").read_text(), end="")
        if result.returncode:
            raise RuntimeError("Lean build failed")
        names = []
        for p in files:
            names += re.findall(r"^(?:@\[[^\n]*\]\s*)?theorem\s+(\w+)", p.read_text(), re.M)
        # Each source uses this one namespace. Audit all named proof declarations.
        audit = "\n".join("import " + m for m in modules) + "\n"
        audit += "\n".join("#print axioms TwoTail502." + n for n in names) + "\n"
        audit_path = args.output / "AxiomAudit.lean"
        audit_path.write_text(audit)
        cmd = ["lake", "env", "lean", str(audit_path)]
        receipt["commands"].append(cmd)
        with (args.output / "axioms.log").open("w") as log:
            result = subprocess.run(cmd, cwd=PROJECT, stdout=log, stderr=subprocess.STDOUT)
        audit_log = (args.output / "axioms.log").read_text()
        print(audit_log, end="")
        if result.returncode or "sorryAx" in audit_log:
            raise RuntimeError("Lean axiom audit failed")
        for line in audit_log.splitlines():
            if "depends on axioms:" in line:
                axioms = line.split("depends on axioms:", 1)[1].strip(" []")
                if any(a.strip() not in {"propext", "Classical.choice", "Quot.sound"}
                       for a in axioms.split(",") if a.strip()):
                    raise RuntimeError("unapproved axiom: " + line)
        if hashes != {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}:
            raise RuntimeError("sources changed during validation")
        if command(["git", "rev-parse", "HEAD"]) != revision or command(["git", "status", "--porcelain"]):
            raise RuntimeError("checkout changed during validation")
        receipt.update(status="passed", named_proofs=len(names), audited_names=names,
                       axiom_log_sha256=hashlib.sha256(audit_log.encode()).hexdigest())
    except Exception as exc:
        receipt.update(status="failed", error=str(exc))
        raise
    finally:
        save()

if __name__ == "__main__":
    main()
