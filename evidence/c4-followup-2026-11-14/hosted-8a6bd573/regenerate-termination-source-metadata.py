#!/usr/bin/env python3
"""Derive fresh static metadata from an explicitly identified clean commit.

No old receipt is copied or relabeled. No compiler or hosted acceptance is
claimed. This helper writes only its requested output outside the repository.
"""
from __future__ import annotations

import argparse
import ast
import datetime as dt
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
INSPECTOR = "evidence/c4-named-termination-2026-11-13/prepared-inspector/inspect-hosted-concrete-termination-audit.py"
INSPECTOR_SHA256 = "fb9805719e3966383d8b28ffd43342611f26ed51cce6ec6290d7fe0a1f424ab3"
REPOSITORY = "larsbx/pisot-substitution-conjecture-research"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def git(root, *args):
    return subprocess.check_output(
        ["git", "--no-optional-locks", "--no-replace-objects", "-C", str(root), *args]
    )


def identity(root):
    return {
        "commit": git(root, "rev-parse", "HEAD").decode().strip(),
        "tree": git(root, "rev-parse", "HEAD^{tree}").decode().strip(),
        "status_porcelain": git(root, "status", "--porcelain=v1", "--untracked-files=all").decode().strip(),
    }


def source_declarations(text, owner, lean_code):
    """Strict static scanner for the unchanged five explicit source modules."""
    code = lean_code(text)
    headers = re.compile(
        r"(?m)^[ \t]*(?P<modifiers>(?:(?:private|public|protected|meta|noncomputable|unsafe|partial|nonrec)\s+)*)"
        r"(?P<kind>theorem|lemma|def)\s+(?P<name>[^\s(:]+)"
    )
    matches = list(headers.finditer(code))
    for token in re.finditer(r"\b(?:theorem|lemma|def)\s+[^\s(:]+", code):
        require(any(m.start() <= token.start() < m.end() for m in matches),
                f"Unaccounted declaration opening in {owner}")
    positions = {code.count("\n", 0, m.start()) + 1: m for m in matches}
    stack, declarations = [], []
    original_lines = text.splitlines()
    for number, line in enumerate(code.splitlines(), 1):
        opening = re.fullmatch(r"\s*(namespace|section)(?:\s+(\S+))?\s*", line)
        if opening:
            stack.append(opening[2] if opening[1] == "namespace" else None)
        elif re.fullmatch(r"\s*end(?:\s+\S+)?\s*", line):
            require(bool(stack), f"Unmatched end in {owner}:{number}")
            stack.pop()
        if number in positions:
            m = positions[number]
            declarations.append({
                "name": ".".join([part for part in stack if part] + [m["name"]]),
                "owner": owner,
                "private": "private" in m["modifiers"].split(),
                "expected_compiled_kind": "declaration" if m["kind"] == "def" else "theorem",
                "line": number,
                "opening": original_lines[number - 1].strip(),
            })
    require(not stack, f"Unclosed namespace in {owner}")
    return sorted(declarations, key=lambda d: d["name"])


def derive(args):
    root = args.root.resolve(strict=True)
    output = args.output.resolve()
    require(not output.is_relative_to(root), "Output must be outside the source checkout")
    require(not output.exists(), "Refusing to overwrite existing metadata")
    for label, value in (("commit", args.expected_commit), ("tree", args.expected_tree)):
        require(re.fullmatch(r"[0-9a-f]{40}", value) is not None,
                f"Expected {label} must be supplied as full lowercase Git identity")
    expected = {"commit": args.expected_commit, "tree": args.expected_tree, "status_porcelain": ""}
    require(identity(root) == expected, "Requires the exact committed clean checkout")
    observed = {}

    def read_source(relative):
        path = root / relative
        require(not path.is_symlink() and path.is_file(), f"Nonregular source: {relative}")
        require(path.resolve().is_relative_to(root), f"Escaping source: {relative}")
        data = path.read_bytes()
        committed = git(root, "show", args.expected_commit + ":" + relative)
        require(data == committed, f"Working bytes differ from committed source: {relative}")
        require(relative not in observed or observed[relative] == data,
                f"Source changed during preparation: {relative}")
        observed[relative] = data
        return data

    inspector_bytes = read_source(INSPECTOR)
    require(digest(inspector_bytes) == INSPECTOR_SHA256,
            "Historical inspector bytes changed; independently review a successor")
    spec = importlib.util.spec_from_file_location("psc_prepared_inspector", root / INSPECTOR)
    inspector = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = inspector
    spec.loader.exec_module(inspector)

    # Reuse only the committed lexical masking function, without importing or
    # executing the proof-bank module and its dependencies.
    bank_tool = ast.parse(read_source("tools/make_proof_bank.py").decode())
    mask_functions = [node for node in bank_tool.body if isinstance(node, ast.FunctionDef) and node.name == "lean_code"]
    require(len(mask_functions) == 1, "Missing unique committed Lean lexical masker")
    lexical_namespace = {}
    exec(compile(ast.Module(body=mask_functions, type_ignores=[]), "committed_lean_code", "exec"), lexical_namespace)
    lean_code = lexical_namespace["lean_code"]

    records = {}
    for relative in sorted(inspector.REQUIRED_METADATA_PATHS):
        data = read_source(relative)
        records[relative] = {
            "path": relative, "repository": REPOSITORY, "revision": args.expected_commit,
            "canonical_url": f"https://github.com/{REPOSITORY}/blob/{args.expected_commit}/{relative}",
            "sha256": digest(data), "source_bytes": len(data), "working_bytes_match_commit": True,
        }
    modules = []
    for relative, owner in sorted(inspector.EXPECTED_MODULE_PATHS.items()):
        item = dict(records[relative])
        item["module"] = owner
        item["declarations"] = source_declarations(observed[relative].decode(), owner, lean_code)
        modules.append(item)

    bank = json.loads(observed["proof/proof-bank.json"])
    named = bank["lean_declarations"]
    require(len(named) == 3597 and len({(d["module"], d["name"]) for d in named}) == 3597,
            "Candidate named-proof inventory differs from the unchanged 3597-proof contract")
    owners = set(inspector.EXPECTED_MODULE_PATHS.values())
    bank_selected = {(d["module"], d["name"]): d for d in named if d["module"] in owners}
    parsed_selected = {(d["owner"], d["name"]): d for item in modules for d in item["declarations"]
                       if d["expected_compiled_kind"] == "theorem"}
    require(set(bank_selected) == set(parsed_selected), "Proof-bank identity inventory differs from source")
    for key, declaration in parsed_selected.items():
        actual = bank_selected[key]
        require(actual["private"] == declaration["private"] and actual["line"] == declaration["line"]
                and actual["declaration"] == declaration["opening"],
                f"Stale proof-bank source locator: {key}")

    pin = read_source("proof/PscVerif/lean-toolchain").decode().strip()
    require(pin == "leanprover/lean4:v4.34.0-rc2", "Unexpected Lean pin")
    manifest = json.loads(observed["proof/PscVerif/lake-manifest.json"])
    mathlib = [p for p in manifest["packages"] if p["name"] == "mathlib"]
    require(len(mathlib) == 1, "Missing unique Mathlib pin")
    replay_ast = ast.parse(observed["tools/replay_archived_payload_lean.py"].decode())
    replay_lists = [n for n in ast.walk(replay_ast) if isinstance(n, ast.Assign)
                    and any(isinstance(t, ast.Name) and t.id == "relative_sources" for t in n.targets)]
    require(len(replay_lists) == 1 and tuple(ast.literal_eval(replay_lists[0].value)) == inspector.REPLAY_SOURCES,
            "Candidate replay manifest differs from the exact 25-path inspector contract")

    metadata = {
        "schema": "psc-concrete-termination-source-binding-v1",
        "repository": REPOSITORY,
        "created_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "subject_revision": args.expected_commit, "subject_tree": args.expected_tree,
        "source_binding_only": True, "kernel_acceptance_claimed": False,
        "full_hosted_acceptance_claimed": False, "human_review_performed": False,
        "scope": "Fresh mechanical source binding derived from the explicit clean committed candidate. No earlier receipt is relabeled; no compilation or hosted acceptance is supplied by this metadata.",
        "lean_toolchain": pin, "mathlib_revision": mathlib[0]["rev"],
        "allowed_axioms_for_later_compiled_audit": sorted(inspector.ALLOWED),
        "modules": modules,
        "reviewed_repository_dependencies_and_audit_sources": [records[p] for p in sorted(records) if p not in inspector.EXPECTED_MODULE_PATHS],
        "changed_nonproof_sources": [],
        "counts": {"source_paths": 35, "explicit_declarations": 41, "explicit_theorems": 37,
                   "explicit_definitions": 4, "candidate_named_proof_inventory": len(named)},
        "derivation": {"helper_sha256": digest(Path(__file__).read_bytes()),
                       "inspector_path": INSPECTOR, "inspector_sha256": INSPECTOR_SHA256,
                       "source_identification": "Explicit expected commit/tree; working bytes checked against Git blobs",
                       "source_declarations": "Fresh lexical source inventory cross-checked against candidate proof bank"},
    }
    inspector.metadata_source_records(metadata)
    inspector.declaration_inventory(metadata)
    for relative, data in observed.items():
        require((root / relative).read_bytes() == data, f"Source changed during preparation: {relative}")
    require(identity(root) == expected, "Candidate checkout changed during preparation")
    output.parent.mkdir(parents=True, exist_ok=True)
    encoded = (json.dumps(metadata, sort_keys=True, indent=2) + "\n").encode()
    with output.open("xb") as stream:
        stream.write(encoded)
    print(json.dumps({"output": str(output), "sha256": digest(encoded), "subject": expected,
                      "counts": metadata["counts"], "source_binding_only": True}, indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--expected-commit", required=True)
    parser.add_argument("--expected-tree", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        derive(args)
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        print(f"Metadata preparation refused: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
