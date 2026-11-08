#!/usr/bin/env python3
"""Replay the independent physical-mass Quint model and audit execution.

This is a verification/provenance runner, not a numerical implementation.
All finite matrix, graph and transition predicates are evaluated in Quint.
The finite forall domains are not described as random simulator coverage.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
MODEL = ROOT / "proof/quint/PhysicalMass.qnt"
VERSION = "0.33.1"
BACKEND = "typescript"
SEED = "20261108"
EXPECTED = {
    "PhysicalMassFinite2": [
        "directMatrixEntryCalibrationTest",
        "domainCountTest",
        "exhaustiveNumericalImplicationTest",
        "acceptedAndConservativeInputsTest",
    ],
    "PhysicalMassGraph3": [
        "graphDomainCountTest",
        "exactReachabilityTest",
        "everyVertexHasSourceAncestorTest",
        "exhaustiveSourceLossCoverageTest",
        "exhaustiveNoPrematureTerminalTest",
    ],
    "PhysicalMassPropagation": [
        "losingSourceInitializationTest",
        "forwardZeroPropagationTest",
        "reverseAndAbsentEdgesRefusedTest",
    ],
    "PhysicalMassAdversarial": [
        "conservativeSourceRefusedTest",
        "losingSinkIsNotLosingSourceTest",
        "omittedRepeatedOccurrenceRefusedTest",
        "incorrectTransposeRefusedTest",
        "zeroMassBreaksSaturationTest",
        "incompleteRootReachabilityRefusedTest",
        "negativeMatrixEntryRefusedTest",
        "signedOverlapRefusedTest",
    ],
}

# Each deliberately weakened model must reach, and fail, its named assertion.
# Syntax errors, zero selected tests, download errors and timeouts do not count.
MUTATIONS = [
    (
        "conservative-source-ignored",
        "  pure def sourceLoss(t, e) = vertices(t).forall(i =>\n"
        "    not(source(t, i)) or vertices(t).exists(j => sameScc(t, i, j) and e[j] > 0))",
        "  pure def sourceLoss(t, e) = losing(t, e).size() > 0",
        "conservativeSourceRefusedTest",
    ),
    (
        "sources-replaced-by-sinks",
        "    not(reaches(t, j, i)) or reaches(t, i, j))",
        "    not(reaches(t, i, j)) or reaches(t, j, i))",
        "losingSinkIsNotLosingSourceTest",
    ),
    (
        "occurrences-collapsed-to-support",
        "  pure def sameOccurrences(expected, supplied) = expected == supplied",
        "  pure def sameOccurrences(expected, supplied) = "
        "occurrenceSupport(expected) == occurrenceSupport(supplied)",
        "omittedRepeatedOccurrenceRefusedTest",
    ),
    (
        "transpose-replaced-by-rows",
        "    out.append(vertices(t).fold(0, (sum, i) => sum + t[i][j] * h[i])))",
        "    out.append(vertices(t).fold(0, (sum, i) => sum + t[j][i] * h[i])))",
        "incorrectTransposeRefusedTest",
    ),
    (
        "zero-mass-allowed",
        "  pure def positive(v) = 0.to(v.length() - 1).forall(i => v[i] > 0)",
        "  pure def positive(v) = 0.to(v.length() - 1).forall(i => v[i] >= 0)",
        "zeroMassBreaksSaturationTest",
    ),
    (
        "partial-root-coverage-allowed",
        "  pure def fullRootCoverage(t, roots) = vertices(t).forall(i =>",
        "  pure def fullRootCoverage(t, roots) = vertices(t).exists(i =>",
        "incompleteRootReachabilityRefusedTest",
    ),
]


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def source_inventory(source: str) -> dict[str, list[str]]:
    chunks = re.split(r"(?m)^module ([A-Za-z_][A-Za-z_0-9]*) \{", source)
    result = {}
    for index in range(1, len(chunks), 2):
        names = re.findall(r"(?m)^  run ([A-Za-z_][A-Za-z_0-9]*)\s*=", chunks[index + 1])
        if names:
            result[chunks[index]] = names
    return result


def run(command: list[str], destination: Path) -> subprocess.CompletedProcess[str]:
    env = dict(os.environ, NO_COLOR="1", FORCE_COLOR="0")
    try:
        completed = subprocess.run(
            command,
            cwd=ROOT,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=180,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        captured = exc.stdout or b""
        if isinstance(captured, bytes):
            captured = captured.decode("utf-8", errors="replace")
        destination.write_text(captured + "\nRUNNER_TIMEOUT: no mathematical verdict\n")
        raise RuntimeError(f"verification command timed out: {destination.name}") from exc
    destination.write_text(completed.stdout, encoding="utf-8")
    return completed


def require_unchanged(path: Path, expected: bytes, label: str) -> None:
    if path.read_bytes() != expected:
        raise RuntimeError(f"{label} changed during verification; refusing stale source binding")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="directory for logs and receipt")
    parser.add_argument(
        "--quint-command",
        default=f"npx --yes @informalsystems/quint@{VERSION}",
        help="optional installed CLI command; version must still be exactly 0.33.1",
    )
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    command = shlex.split(args.quint_command)
    if not command:
        parser.error("--quint-command must not be empty")
    receipt = {
        "schema": "psc-physical-mass-quint-receipt-v1",
        "status": "started",
        "model": str(MODEL.relative_to(ROOT)),
        "source_snapshot_used": True,
        "quint_version": VERSION,
        "backend": BACKEND,
        "seed": SEED,
        "scope": "bounded exhaustive predicates and deterministic transition/adversarial tests",
        "finite_domain_cardinalities": {
            "two_by_two_integer_tuples": 11664,
            "three_vertex_directed_graphs_including_loops": 512,
            "graph_and_loss_set_pairs": 4096,
            "graph_loss_and_known_set_triples": 32768,
        },
        "domain_note": (
            "These are fully quantified finite domain sizes, not sampled execution counts. "
            "Conditional consequences are required only when their explicit antecedents hold. "
            "No universal real-matrix theorem or unbounded temporal model check is claimed."
        ),
        "executed_tests": [],
        "rejected_mutations": [],
    }
    receipt_path = output / "quint-receipt.json"

    def save_receipt() -> None:
        receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")

    save_receipt()
    try:
        # Clear an earlier successful receipt before source reads or Git queries,
        # so initialization failures cannot leave a stale successful verdict.
        source_bytes = MODEL.read_bytes()
        source = source_bytes.decode("utf-8")
        runner_path = Path(__file__).resolve()
        runner_bytes = runner_path.read_bytes()
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        status_command = [
            "git", "status", "--porcelain", "--", str(MODEL.relative_to(ROOT)),
            str(runner_path.relative_to(ROOT)),
        ]
        status = subprocess.check_output(status_command, cwd=ROOT, text=True).strip()
        receipt.update({
            "git_head": revision,
            "worktree_dirty": bool(status),
            "worktree_status_for_model_and_runner": status,
            "model_sha256": sha256(source_bytes),
            "runner_sha256": sha256(runner_bytes),
        })
        save_receipt()
        declared = source_inventory(source)
        if declared != EXPECTED:
            raise RuntimeError(f"test inventory mismatch: declared={declared!r}; expected={EXPECTED!r}")
        version = run(command + ["--version"], output / "quint-version.log")
        if version.returncode or VERSION not in version.stdout.splitlines():
            raise RuntimeError("Quint version did not match exact pin")
        common = [f"--backend={BACKEND}", "--max-samples=1", f"--seed={SEED}"]
        # All modules and mutants are evaluated from the same captured source.
        # The model is self-contained, so copying it does not change imports.
        with tempfile.TemporaryDirectory(prefix="psc-physical-mass-snapshot-") as temporary:
            snapshot = Path(temporary) / "PhysicalMass.qnt"
            snapshot.write_bytes(source_bytes)
            snapshot.chmod(0o444)
            checked = run(command + ["typecheck", str(snapshot)], output / "quint-typecheck.log")
            if checked.returncode:
                raise RuntimeError("Quint typecheck failed")

            for module, expected_names in EXPECTED.items():
                logfile = output / f"{module}.log"
                completed = run(command + ["test", str(snapshot), f"--main={module}"] + common, logfile)
                observed = re.findall(r"\bok ([A-Za-z_][A-Za-z_0-9]*) passed (\d+) test\(s\)", completed.stdout)
                if completed.returncode or observed != [(name, "1") for name in expected_names]:
                    raise RuntimeError(f"missing, unexpected or failed Quint tests in {module}: {observed!r}")
                receipt["executed_tests"].append({
                    "module": module,
                    "names": expected_names,
                    "count": len(observed),
                    "log_sha256": sha256(logfile.read_bytes()),
                })
                save_receipt()
                print(f"PHYSICAL_MASS_QUINT_OK {module}: {len(observed)} tests", flush=True)

            for name, before, after, test_name in MUTATIONS:
                if source.count(before) != 1:
                    raise RuntimeError(f"mutation {name} must have exactly one matching source location")
                mutated = source.replace(before, after, 1)
                model = Path(temporary) / f"{name}.qnt"
                model.write_text(mutated)
                logfile = output / f"mutation-{name}.log"
                completed = run(command + [
                    "test", str(model), "--main=PhysicalMassAdversarial", f"--match=^{test_name}$",
                ] + common, logfile)
                failures = re.findall(r"\d+\) ([A-Za-z_][A-Za-z_0-9]*) failed after (\d+) test\(s\)", completed.stdout)
                if completed.returncode == 0 or failures != [(test_name, "1")] or "Error [QNT508]" not in completed.stdout:
                    raise RuntimeError(f"mutation {name} did not reach the expected failing assertion")
                receipt["rejected_mutations"].append({
                    "name": name,
                    "test": test_name,
                    "replace_once": {"before": before, "after": after},
                    "mutant_sha256": sha256(mutated.encode()),
                    "log_sha256": sha256(logfile.read_bytes()),
                })
                save_receipt()
                print(f"PHYSICAL_MASS_QUINT_MUTATION_REJECTED {name}", flush=True)

            require_unchanged(snapshot, source_bytes, "private model snapshot")

        require_unchanged(MODEL, source_bytes, "model source")
        require_unchanged(runner_path, runner_bytes, "verification runner")
        final_revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        if final_revision != revision:
            raise RuntimeError("Git HEAD changed during verification; refusing stale revision binding")
        final_status = subprocess.check_output(status_command, cwd=ROOT, text=True).strip()
        receipt["worktree_status_for_model_and_runner_at_completion"] = final_status
        receipt["worktree_dirty"] = bool(status or final_status)
        receipt["source_and_revision_recheck"] = "unchanged"

        receipt["status"] = "passed"
        receipt["executed_test_count"] = sum(len(names) for names in EXPECTED.values())
        receipt["rejected_mutation_count"] = len(MUTATIONS)
        save_receipt()
        print(f"PHYSICAL_MASS_QUINT_ACCEPTED {receipt['executed_test_count']} tests; {len(MUTATIONS)} mutations")
        return 0
    except (OSError, RuntimeError, subprocess.SubprocessError, UnicodeError) as exc:
        receipt["status"] = "failed"
        receipt["failure"] = str(exc)
        save_receipt()
        print(f"PHYSICAL_MASS_QUINT_REFUSED {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
