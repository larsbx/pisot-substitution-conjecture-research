#!/usr/bin/env python3
"""Run and bind the independent bounded named-chart Quint controls.

This file is a provenance runner. Matrix-norm and chart predicates execute in
Quint; no Python implementation of the mathematical implication is used.
All finite forall domains are exhaustive, not random simulator coverage.
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
MODEL = ROOT / "proof/quint/C4NamedStableChart.qnt"
VERSION = "0.33.1"
BACKEND = "typescript"
SEED = "20261111"
EXPECTED = {'C4NamedChartExhaustive': ['matrixDomainCountTest',
                            'exhaustiveRowBoundTest',
                            'exhaustiveRationalContractionTest',
                            'exactSignedExtremizerTest',
                            'nonvacuousBoundaryTest'],
 'C4NamedChartAlgebra': ['completeSectionFamilyTest',
                         'correctedSectionTest',
                         'fullReconstructionTest',
                         'basisCommutationFamilyTest'],
 'C4NamedChartAdversarial': ['columnNormRefusedTest',
                             'entrywiseNormRefusedTest',
                             'signedCancellationRefusedTest',
                             'secondRowRefusedTest',
                             'unitContractionRefusedTest',
                             'invalidDenominatorRefusedTest',
                             'wrongMatrixRefusedTest',
                             'wrongBlockRefusedTest',
                             'zeroProjectionRefusedTest',
                             'missingCommutationRefusedTest',
                             'coordinateRescalingRefusedTest',
                             'quotientNormNotIsometryTest',
                             'rawSectionNotStablePlaneTest']}

# A mutation is rejected only by the expected reached mathematical assertion.
# A parser/typechecker error, missing test, timeout or tool failure is not a kill.
MUTATIONS = [('substitute-column-norm',
  '  pure def rowsSafe(m, den, num, qden) = all {\n'
  '    qden * row0(m) <= num * den,\n'
  '    qden * row1(m) <= num * den,\n'
  '  }',
  '  pure def rowsSafe(m, den, num, qden) = qden * columnNorm(m) <= num * den',
  'columnNormRefusedTest'),
 ('substitute-entrywise-norm',
  '  pure def rowsSafe(m, den, num, qden) = all {\n'
  '    qden * row0(m) <= num * den,\n'
  '    qden * row1(m) <= num * den,\n'
  '  }',
  '  pure def rowsSafe(m, den, num, qden) = qden * entryNorm(m) <= num * den',
  'entrywiseNormRefusedTest'),
 ('drop-absolute-values',
  '  pure def rowsSafe(m, den, num, qden) = all {\n'
  '    qden * row0(m) <= num * den,\n'
  '    qden * row1(m) <= num * den,\n'
  '  }',
  '  pure def rowsSafe(m, den, num, qden) = all {\n'
  '    qden * (m[0][0] + m[0][1]) <= num * den,\n'
  '    qden * (m[1][0] + m[1][1]) <= num * den,\n'
  '  }',
  'signedCancellationRefusedTest'),
 ('omit-second-row',
  '  pure def rowsSafe(m, den, num, qden) = all {\n'
  '    qden * row0(m) <= num * den,\n'
  '    qden * row1(m) <= num * den,\n'
  '  }',
  '  pure def rowsSafe(m, den, num, qden) = qden * row0(m) <= num * den',
  'secondRowRefusedTest'),
 ('admit-unit-contraction',
  '    den > 0, qden > 0, num >= 0, num < qden,',
  '    den > 0, qden > 0, num >= 0, num <= qden,',
  'unitContractionRefusedTest'),
 ('admit-zero-denominator',
  '    den > 0, qden > 0, num >= 0, num < qden,',
  '    den >= 0, qden > 0, num >= 0, num < qden,',
  'invalidDenominatorRefusedTest'),
 ('ignore-matrix-identity',
  '  pure def sameMatrix(expected, supplied) = expected == supplied',
  '  pure def sameMatrix(expected, supplied) = true',
  'wrongMatrixRefusedTest'),
 ('ignore-block-identity',
  '  pure def sameBlock(expected, supplied) = expected == supplied',
  '  pure def sameBlock(expected, supplied) = true',
  'wrongBlockRefusedTest'),
 ('omit-section-authentication',
  '    sectionIdentity(w),',
  '    true,',
  'zeroProjectionRefusedTest'),
 ('omit-incidence-commutation',
  '    basisCommutation(w),',
  '    true,',
  'missingCommutationRefusedTest')]


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
        raise RuntimeError(f"verification timed out: {destination.name}") from exc
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
        help="installed CLI command; the exact version pin is still enforced",
    )
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    command = shlex.split(args.quint_command)
    if not command:
        parser.error("--quint-command must not be empty")

    receipt = {
        "schema": "psc-c4-named-stable-chart-quint-receipt-v1",
        "status": "started",
        "model": str(MODEL.relative_to(ROOT)),
        "source_snapshot_used": True,
        "quint_version": VERSION,
        "backend": BACKEND,
        "seed": SEED,
        "scope": "bounded exhaustive matrix-norm and chart implications with deterministic adversarial controls",
        "finite_domain_cardinalities": {
            "two_by_two_integer_matrices": 81,
            "integer_vectors_two": 25,
            "integer_vectors_three": 125,
            "matrix_vector_tuples": 2025,
            "rational_contraction_tuples": 54675,
            "projection_section_tuples": 625,
            "basis_commutation_extension_tuples": 3125,
        },
        "domain_note": (
            "These are exact forall-domain sizes, not accepted-premise or random sample counts. "
            "The rational matrix action is represented by its numerator and positive denominator. "
            "The chart controls are separate integer examples, not the named algebraic Pisot chart. "
            "This model does not select a real root, prove the named power identity, authenticate "
            "an infinite word, prove compactness, or decode native numerical certificates."
        ),
        "executed_tests": [],
        "rejected_mutations": [],
    }
    receipt_path = output / "quint-receipt.json"

    def save_receipt() -> None:
        receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")

    # Clear any previous successful verdict before reading sources or Git.
    save_receipt()
    try:
        source_bytes = MODEL.read_bytes()
        source = source_bytes.decode("utf-8")
        runner_path = Path(__file__).resolve()
        runner_bytes = runner_path.read_bytes()
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        tree = subprocess.check_output(["git", "rev-parse", "HEAD^{tree}"], cwd=ROOT, text=True).strip()
        status_command = [
            "git", "status", "--porcelain", "--", str(MODEL.relative_to(ROOT)),
            str(runner_path.relative_to(ROOT)),
        ]
        status = subprocess.check_output(status_command, cwd=ROOT, text=True).strip()
        receipt.update({
            "git_head": revision,
            "git_tree": tree,
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
        with tempfile.TemporaryDirectory(prefix="psc-c4-named-chart-snapshot-") as temporary:
            snapshot = Path(temporary) / "C4NamedStableChart.qnt"
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
                print(f"C4_NAMED_CHART_QUINT_OK {module}: {len(observed)} tests", flush=True)

            for name, before, after, test_name in MUTATIONS:
                if source.count(before) != 1:
                    raise RuntimeError(f"mutation {name} must have exactly one matching source location")
                mutated = source.replace(before, after, 1)
                model = Path(temporary) / f"{name}.qnt"
                model.write_text(mutated, encoding="utf-8")
                logfile = output / f"mutation-{name}.log"
                completed = run(command + [
                    "test", str(model), "--main=C4NamedChartAdversarial", f"--match=^{test_name}$",
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
                print(f"C4_NAMED_CHART_QUINT_MUTATION_REJECTED {name}", flush=True)
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
        print(f"C4_NAMED_CHART_QUINT_ACCEPTED {receipt['executed_test_count']} tests; {len(MUTATIONS)} mutations")
        return 0
    except Exception as exc:
        receipt["status"] = "failed"
        receipt["failure"] = str(exc)
        save_receipt()
        print(f"C4_NAMED_CHART_QUINT_REFUSED: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
