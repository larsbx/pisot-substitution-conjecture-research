#!/usr/bin/env python3
"""Inspect complete isolated Lean audit output without compiling or changing the repo.

Inventory mode produces source metadata only. Inspection requires a committed
revision, the complete raw gate log, every named declaration exactly once, and
the final proof-bank acknowledgement. An inspection pass is not an independent
attestation of the enclosing process exit status or the log's execution lineage.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import re
import subprocess
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    "StrictCutCount": {
        "theorem": (
            "factorStart_injective", "card_startVectors", "markAtFactorStart",
            "exists_balanced_marks_of_mem", "physicalLength_le_mul_length",
            "physicalLength_le_card_reduction_starts", "offset_mem_strip_of_mem",
            "repeated_factor_control", "empty_startVectors",
        ),
        "def": ("factorStart", "startVectors"),
    },
    "NamedCutCount": {
        "theorem": ("physicalLength_iterate", "integerStarts_count_and_strip",
                    "eventually_integerStarts_mem"),
        "def": ("integerStarts",),
    },
}
PRIVATE = {
    "StrictCutCount": {"markAtFactorStart", "physicalLength_le_mul_length"},
    "NamedCutCount": {"physicalLength_iterate"},
}
DECL = re.compile(r"^(?P<private>private\s+)?(?:noncomputable\s+)?(?P<kind>theorem|def)\s+(?P<short>[A-Za-z_][A-Za-z_0-9']*)", re.M)
BANK = re.compile(r"Proof bank: (\d+) claims, (\d+) named Lean proofs, (\d+) source openings")
ACK = re.compile(r"Lean axiom audit: (\d+) declarations, (\d+) theorems; all named proofs reached")


class Refused(Exception):
    pass


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(repo: Path, *args: str) -> bytes:
    result = subprocess.run(["git", *args], cwd=repo, capture_output=True, check=False)
    if result.returncode:
        raise Refused("Git source read failed: " + result.stderr.decode(errors="replace").strip())
    return result.stdout


def write_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    os.replace(temporary, path)


def inventory(repo: Path, revision: str | None) -> dict:
    head = git(repo, "rev-parse", "HEAD").decode().strip()
    commit = None
    tree = None
    if revision is not None:
        commit = git(repo, "rev-parse", "--verify", "--end-of-options", revision + "^{commit}").decode().strip()
        if not re.fullmatch(r"[0-9a-f]{40}", commit):
            raise Refused("Expected a resolved 40-character Git commit ID")
        tree = git(repo, "rev-parse", commit + "^{tree}").decode().strip()
    modules = []
    for module, wanted in EXPECTED.items():
        path = f"proof/PscVerif/PscVerif/{module}.lean"
        source = git(repo, "show", f"{commit}:{path}") if commit else (repo / path).read_bytes()
        text = source.decode("utf-8")
        if text.count(f"namespace Psc.{module}\n") != 1:
            raise Refused(f"Unexpected namespace layout in {path}")
        matches = list(DECL.finditer(text))
        found = Counter((m["kind"], m["short"]) for m in matches)
        expected = Counter((kind, name) for kind, names in wanted.items() for name in names)
        if found != expected:
            raise Refused(f"Explicit source inventory mismatch in {path}: expected {dict(expected)}, found {dict(found)}")
        found_private = {m["short"] for m in matches if m["private"]}
        if found_private != PRIVATE[module]:
            raise Refused(f"Private source inventory mismatch in {path}")
        declarations = []
        for match in matches:
            kind, short = match["kind"], match["short"]
            declarations.append({
                "name": f"Psc.{module}.{short}",
                "owner": f"PscVerif.{module}",
                "source_kind": kind,
                "private": bool(match["private"]),
                "expected_compiled_kind": "theorem" if kind == "theorem" else "declaration",
                "line": text.count("\n", 0, match.start()) + 1,
                "opening": text[match.start():].splitlines()[0],
            })
        modules.append({
            "module": f"PscVerif.{module}",
            "source_path": path,
            "source_sha256": digest(source),
            "source_git_blob_sha": hashlib.sha1(f"blob {len(source)}\0".encode() + source).hexdigest(),
            "source_bytes": len(source),
            "explicit_theorem_count": len(wanted["theorem"]),
            "explicit_definition_count": len(wanted["def"]),
            "explicit_public_theorem_count": len(wanted["theorem"]) - len(PRIVATE[module]),
            "explicit_private_theorem_count": len(PRIVATE[module]),
            "declarations": declarations,
        })
    theorem_count = sum(m["explicit_theorem_count"] for m in modules)
    definition_count = sum(m["explicit_definition_count"] for m in modules)
    if (theorem_count, definition_count) != (12, 3):
        raise Refused("Expected exactly 12 explicit theorems and three definitions")
    public_count = sum(m["explicit_public_theorem_count"] for m in modules)
    private_count = sum(m["explicit_private_theorem_count"] for m in modules)
    if (public_count, private_count) != (9, 3):
        raise Refused("Expected nine public theorems and three private helpers")
    return {
        "schema": "psc-finite-cut-count-source-inventory-v1",
        "scope": "Source inventory only; no compilation, log inspection, or acceptance is claimed by this file.",
        "source_origin": "committed_revision" if commit else "working_tree_candidate",
        "code_revision": commit,
        "code_tree": tree,
        "head_at_inventory": head,
        "explicit_theorem_count": theorem_count,
        "explicit_public_theorem_count": public_count,
        "explicit_private_theorem_count": private_count,
        "explicit_definition_count": definition_count,
        "modules": modules,
    }


def inspect(args: argparse.Namespace, source_inventory: dict) -> dict:
    raw = args.log.read_bytes()
    lines = raw.decode("utf-8").splitlines()
    completions = [(i, line.split("\t")) for i, line in enumerate(lines)
                   if line.startswith("PSC_AUDIT_COMPLETE")]
    if len(completions) != 1 or len(completions[0][1]) != 3:
        raise Refused("No unique, well-formed PSC_AUDIT_COMPLETE marker")
    completion_index, completion = completions[0]
    if completion[0] != "PSC_AUDIT_COMPLETE" or not all(re.fullmatch(r"[0-9]+", x) for x in completion[1:]):
        raise Refused("Malformed completion counts")
    completed_constants, completed_theorems = map(int, completion[1:])
    acknowledgements = [(i, ACK.fullmatch(line)) for i, line in enumerate(lines) if ACK.fullmatch(line)]
    banks = [(i, BANK.fullmatch(line)) for i, line in enumerate(lines) if BANK.fullmatch(line)]
    if lines.count("Prepared isolated Lean workspace from source/configuration only") != 1:
        raise Refused("The full isolated-source preparation marker is missing or repeated")
    if len(acknowledgements) != 1 or acknowledgements[0][0] <= completion_index:
        raise Refused("The final all-named-proofs acknowledgement is missing or out of order")
    nonempty = [line for line in lines if line.strip()]
    if len(banks) < 2 or banks[-1][0] <= acknowledgements[0][0] or not BANK.fullmatch(nonempty[-1]):
        raise Refused("The complete raw gate log must end with its post-audit proof-bank summary")

    errors = []
    records = []
    record_lines = []
    for line_index, line in enumerate(lines):
        if not line.startswith("PSC_AXIOMS"):
            continue
        fields = line.split("\t")
        if len(fields) != 6 or fields[0] != "PSC_AXIOMS":
            errors.append({"kind": "malformed_record", "line": line_index + 1, "record": line})
            continue
        _, kind, owner, name, user_name, axiom_csv = fields
        axioms = axiom_csv.split(",") if axiom_csv else []
        record = {"kind": kind, "owner": owner, "name": name, "user_name": user_name, "axioms": axioms}
        records.append(record)
        record_lines.append(line)
        if line_index >= completion_index:
            errors.append({"kind": "record_after_completion", "name": name})
        if kind not in {"theorem", "declaration"} or not owner or not name or not user_name:
            errors.append({"kind": "invalid_constant_record", "record": record})
        unexpected = sorted(set(axioms) - ALLOWED)
        if unexpected:
            errors.append({"kind": "nonstandard_axioms", "name": name, "axioms": unexpected})
        if len(axioms) != len(set(axioms)):
            errors.append({"kind": "duplicate_axiom_entry", "name": name})

    counts = Counter(record["name"] for record in records)
    for name, count in counts.items():
        if count != 1:
            errors.append({"kind": "duplicate_compiled_constant", "name": name, "count": count})
    parsed_theorems = sum(record["kind"] == "theorem" for record in records)
    actual_counts = (len(records), parsed_theorems)
    if not records or (completed_constants, completed_theorems) != actual_counts:
        errors.append({"kind": "completion_count_mismatch", "completion": completion[1:], "parsed": actual_counts})
    acknowledged_counts = tuple(map(int, acknowledgements[0][1].groups()))
    if acknowledged_counts != actual_counts:
        errors.append({"kind": "acknowledgement_count_mismatch", "acknowledged": acknowledged_counts, "parsed": actual_counts})
    if banks[0][1].groups() != banks[-1][1].groups():
        errors.append({"kind": "source_inventory_summary_changed_during_gate"})

    by_user = {}
    for record in records:
        by_user.setdefault((record["owner"], record["user_name"]), []).append(record)
    module_results = []
    for module in source_inventory["modules"]:
        explicit = []
        for declaration in module["declarations"]:
            name = declaration["name"]
            candidates = by_user.get((declaration["owner"], name), [])
            actual = candidates[0] if len(candidates) == 1 else None
            private_identity = bool(actual and actual["name"].startswith("_private.")
                                    and actual["name"].endswith("." + name))
            expected_identity = (private_identity if declaration["private"]
                                 else bool(actual and actual["name"] == name))
            matched = bool(actual and counts[actual["name"]] == 1
                           and expected_identity
                           and actual["kind"] == declaration["expected_compiled_kind"]
                           and actual["owner"] == declaration["owner"]
                           and actual["user_name"] == name)
            if not matched:
                errors.append({"kind": "explicit_declaration_mismatch", "expected": declaration,
                               "actual": actual, "record_count": len(candidates)})
            explicit.append({**declaration, "compiled_record_count": len(candidates),
                             "compiled_record_matches": matched, "actual": actual})
        owned = [record for record in records if record["owner"] == module["module"]]
        module_results.append({**module, "declarations": explicit,
                               "compiled_owned_constant_count": len(owned),
                               "compiled_owned_theorem_count": sum(r["kind"] == "theorem" for r in owned)})

    owners = {module["module"] for module in source_inventory["modules"]}
    new_records = [record for record in records if record["owner"] in owners]
    extracted = "\n".join(line for line in record_lines if line.split("\t")[2] in owners) + "\n"
    args.extracted.parent.mkdir(parents=True, exist_ok=True)
    args.extracted.write_text(extracted, encoding="utf-8")
    return {
        "schema": "psc-finite-cut-count-compiled-audit-inspection-v1",
        "inspected_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "scope": "Independent inspection of a complete isolated ProofBankAudit log and committed sources. No recompilation. The revision is caller-supplied; execution lineage and enclosing process exit status require the separate gate receipt.",
        "subject_revision": source_inventory["code_revision"],
        "subject_tree": source_inventory["code_tree"],
        "head_at_inspection": source_inventory["head_at_inventory"],
        "inspector_sha256": digest(Path(__file__).read_bytes()),
        "required_gate_log_path": str(args.log.resolve()),
        "required_gate_log_sha256": digest(raw),
        "source_inventory_path": str(args.inventory.resolve()),
        "source_inventory_sha256": digest(args.inventory.read_bytes()),
        "extracted_new_module_log_path": str(args.extracted.resolve()),
        "extracted_new_module_log_sha256": digest(extracted.encode()),
        "allowed_axioms": sorted(ALLOWED),
        "global_encountered_axioms": sorted({a for r in records for a in r["axioms"]}),
        "global_compiled_constant_count": len(records),
        "global_compiled_theorem_count": parsed_theorems,
        "completion_marker": "\t".join(completion),
        "completion_counts_match": actual_counts == (completed_constants, completed_theorems),
        "post_audit_acknowledgement": lines[acknowledgements[0][0]],
        "final_proof_bank_summary": lines[banks[-1][0]],
        "explicit_new_theorem_count": source_inventory["explicit_theorem_count"],
        "explicit_public_theorem_count": source_inventory["explicit_public_theorem_count"],
        "explicit_private_theorem_count": source_inventory["explicit_private_theorem_count"],
        "explicit_new_definition_count": source_inventory["explicit_definition_count"],
        "new_module_compiled_constant_count": len(new_records),
        "new_module_compiled_theorem_count": sum(r["kind"] == "theorem" for r in new_records),
        "new_module_encountered_axioms": sorted({a for r in new_records for a in r["axioms"]}),
        "modules": module_results,
        "errors": errors,
        "status": "failed" if errors else "passed",
        "passed": not errors,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=HERE / "psc-count")
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--revision", help="Original committed code revision whose sources were compiled")
    source.add_argument("--working-tree-inventory", action="store_true", help="Inventory preparation only; never compiled acceptance")
    parser.add_argument("--inventory-only", action="store_true")
    parser.add_argument("--log", type=Path, help="Complete raw ./tools/check_lean.sh output, not a filtered excerpt")
    parser.add_argument("--inventory", type=Path, default=HERE / "count-source-inventory.json")
    parser.add_argument("--output", type=Path, default=HERE / "count-compiled-audit-inspection.json")
    parser.add_argument("--extracted", type=Path, default=HERE / "count-compiled-new-declarations.log")
    args = parser.parse_args()
    if args.working_tree_inventory and not args.inventory_only:
        parser.error("--working-tree-inventory requires --inventory-only")
    if not args.inventory_only and args.log is None:
        parser.error("Inspection requires --log")
    try:
        source_inventory = inventory(args.repo.resolve(), args.revision)
        write_json(args.inventory, source_inventory)
        if args.inventory_only:
            print(json.dumps({"status": "source_inventory_only", "code_revision": source_inventory["code_revision"],
                              "source_origin": source_inventory["source_origin"],
                              "theorems": source_inventory["explicit_theorem_count"],
                              "definitions": source_inventory["explicit_definition_count"],
                              "inventory": str(args.inventory.resolve())}, indent=2))
            return 0
        report = inspect(args, source_inventory)
    except (Refused, OSError, UnicodeError, ValueError) as exc:
        report = {"schema": "psc-finite-cut-count-compiled-audit-inspection-v1",
                  "status": "refused", "passed": False,
                  "scope": "Input or completeness checks refused; no compiled acceptance is claimed.",
                  "requested_revision": args.revision, "errors": [{"kind": "inspection_refused", "detail": str(exc)}]}
    write_json(args.output, report)
    keys = ("status", "passed", "subject_revision", "global_compiled_constant_count", "global_compiled_theorem_count",
            "explicit_new_theorem_count", "explicit_public_theorem_count", "explicit_private_theorem_count",
            "explicit_new_definition_count", "new_module_compiled_constant_count",
            "new_module_compiled_theorem_count", "global_encountered_axioms", "errors")
    print(json.dumps({k: report[k] for k in keys if k in report}, indent=2))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
