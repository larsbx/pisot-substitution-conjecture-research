#!/usr/bin/env python3
"""Verify the bounded C4 Quint model, exact test inventory and weakened controls.

This runner records provenance; all mathematical predicates execute in Quint.
It reports no universal theorem and refuses download, parse or timeout failures.
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
MODEL = ROOT / "proof/quint/C4OccurrenceBridge.qnt"
VERSION = "0.33.1"
EXPECTED = [
    "domainCountTest",
    "allSingletonsGiveNewbornTest",
    "alignedLetterIsSingletonTest",
    "interiorOverlapKeepsOrdinalTest",
    "boundaryTouchIsInsufficientTest",
    "repeatedFactorValuesLoseOccurrenceTest",
    "erasureAndSingletonParentControlsTest",
    "parentIrreducibilityIsNecessaryTest",
    "bothNewbornSidesTest",
    "existentialRouteAllowsAvoidingCycleTest",
    "lookupDomainCountTest",
    "globalToLocalReconstructionTest",
    "exteriorAddressRejectedTest",
    "balancedFactorLookupTest",
    "transportDomainCountTest",
    "literalAffineSquareTest",
    "balancedPrefixTrimmingTest",
    "trackSwapCovarianceTest",
    "affineTermsAreNecessaryTest",
    "sameLetterSplitStaysSplitTest",
]
MUTATIONS = [
    (
        "touch-replaces-interior",
        "weightPrefix(v, j + 1, lengths),\n"
        "    weightPrefix(v, j, lengths) < weightPrefix(u, i + 1, lengths),",
        "weightPrefix(v, j + 1, lengths),\n"
        "    weightPrefix(v, j, lengths) <= weightPrefix(u, i + 1, lengths),",
        "boundaryTouchIsInsufficientTest",
    ),
    (
        "ordinal-erased",
        "pure def ordinal(cs, i) = cs.select(k => k <= i).length() - 1",
        "pure def ordinal(cs, i) = 0",
        "repeatedFactorValuesLoseOccurrenceTest",
    ),
    (
        "inherited-cut-ignored",
        "pure def inherited(s, u, v, k) = cuts(u, v)\n"
        "    .select(i => inflate(s, prefix(u, i)).length() == k).length() > 0",
        "pure def inherited(s, u, v, k) = false",
        "parentIrreducibilityIsNecessaryTest",
    ),
    (
        "factor-prefix-offset-ignored",
        "pure def localPosition(chunks, k, i) = i - offset(chunks, k)",
        "pure def localPosition(chunks, k, i) = i",
        "globalToLocalReconstructionTest",
    ),
    (
        "incidence-action-omitted",
        "pure def affineNext(s, r, forcing) = add2(incidence(s, r), forcing)",
        "pure def affineNext(s, r, forcing) = add2(r, forcing)",
        "affineTermsAreNecessaryTest",
    ),
    (
        "digit-forcing-omitted",
        "pure def affineNext(s, r, forcing) = add2(incidence(s, r), forcing)",
        "pure def affineNext(s, r, forcing) = incidence(s, r)",
        "affineTermsAreNecessaryTest",
    ),
    (
        "track-swap-sign-ignored",
        "pure def orientedResidual(sign, r) = if (sign == 1) r else (-r._1, -r._2)",
        "pure def orientedResidual(sign, r) = r",
        "trackSwapCovarianceTest",
    ),
]


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--quint-command", default=f"npx --yes @informalsystems/quint@{VERSION}")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    command = shlex.split(args.quint_command)
    if not command:
        parser.error("--quint-command must not be empty")
    receipt = {
        "schema": "psc-c4-occurrence-quint-v2", "status": "started",
        "quint_version": VERSION, "backend": "typescript", "seed": "20261110",
        "scope": "exhaustive bounded literal-word predicates and explicit negative controls",
        "strict_binary_parents_length_2_through_4": 16,
        "nonerasing_binary_substitutions_image_length_1_through_2": 36,
        "parent_substitution_inputs": 576,
        "lookup_chunks_binary_length_0_through_2": 7,
        "ordered_chunk_lists_length_0_through_3": 400,
        "in_range_global_indices_across_chunk_lists": 1620,
        "balanced_binary_word_pairs_length_0_through_4": 99,
        "transport_binary_words_length_1_through_2": 6,
        "transport_word_pair_substitution_inputs": 1296,
        "transport_valid_source_index_and_digit_inputs": 10400,
        "note": "Finite forall domains, not random sample counts or a Pisot census.",
        "executed_tests": [], "rejected_mutations": [],
    }

    def save() -> None:
        (output / "quint-receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")

    def run(arguments: list[str], name: str) -> subprocess.CompletedProcess[str]:
        try:
            result = subprocess.run(
                command + arguments, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=180, check=False,
                env=dict(os.environ, NO_COLOR="1", FORCE_COLOR="0"),
            )
        except subprocess.TimeoutExpired as exc:
            captured = exc.stdout or b""
            if isinstance(captured, bytes):
                captured = captured.decode("utf-8", errors="replace")
            (output / f"{name}.log").write_text(captured + "\nTIMEOUT: no verdict\n")
            raise RuntimeError(f"Quint timed out: {name}") from exc
        (output / f"{name}.log").write_text(result.stdout)
        return result

    save()
    try:
        source = MODEL.read_bytes()
        runner = Path(__file__).resolve()
        runner_source = runner.read_bytes()
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        status_command = ["git", "status", "--porcelain", "--", str(MODEL), str(runner)]
        initial_status = subprocess.check_output(status_command, cwd=ROOT, text=True).strip()
        receipt.update({
            "git_head": revision, "model_sha256": digest(source),
            "runner_sha256": digest(runner_source), "worktree_dirty": bool(initial_status),
        })
        save()
        text = source.decode()
        names = re.findall(r"(?m)^  run (\w+)\s*=", text)
        if names != EXPECTED:
            raise RuntimeError(f"test inventory mismatch: {names!r}")
        version = run(["--version"], "version")
        if version.returncode or VERSION not in version.stdout.splitlines():
            raise RuntimeError("Quint release does not match pin")
        common = ["--main=C4OccurrenceBridge", "--backend=typescript", "--max-samples=1", "--seed=20261110"]
        with tempfile.TemporaryDirectory(prefix="psc-c4-occurrence-") as temporary:
            snapshot = Path(temporary) / "C4OccurrenceBridge.qnt"
            snapshot.write_bytes(source)
            snapshot.chmod(0o444)
            if run(["typecheck", str(snapshot)], "typecheck").returncode:
                raise RuntimeError("Quint typecheck failed")
            result = run(["test", str(snapshot)] + common, "tests")
            passed = re.findall(r"\bok (\w+) passed (\d+) test\(s\)", result.stdout)
            if result.returncode or passed != [(name, "1") for name in EXPECTED]:
                raise RuntimeError(f"failed or missing executed tests: {passed!r}")
            receipt["executed_tests"] = EXPECTED
            save()
            for name, before, after, test in MUTATIONS:
                if text.count(before) != 1:
                    raise RuntimeError(f"mutation {name} does not have exactly one site")
                mutant = Path(temporary) / f"{name}.qnt"
                mutant.write_text(text.replace(before, after, 1))
                result = run(["test", str(mutant)] + common + [f"--match=^{test}$"], name)
                failed = re.findall(r"\d+\) (\w+) failed after (\d+) test\(s\)", result.stdout)
                if result.returncode == 0 or failed != [(test, "1")] or "Error [QNT508]" not in result.stdout:
                    raise RuntimeError(f"mutation {name} did not reach its expected assertion")
                receipt["rejected_mutations"].append({"name": name, "test": test, "sha256": digest(mutant.read_bytes())})
                save()
            if snapshot.read_bytes() != source:
                raise RuntimeError("private source snapshot changed")
        if MODEL.read_bytes() != source or runner.read_bytes() != runner_source:
            raise RuntimeError("model or runner changed during verification")
        if subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip() != revision:
            raise RuntimeError("Git revision changed during verification")
        receipt["worktree_dirty"] |= bool(subprocess.check_output(status_command, cwd=ROOT, text=True).strip())
        receipt["source_and_revision_recheck"] = "unchanged"
        receipt["status"] = "passed"
        save()
        print(f"C4_OCCURRENCE_QUINT_ACCEPTED {len(EXPECTED)} tests; {len(MUTATIONS)} mutations")
        return 0
    except (OSError, RuntimeError, UnicodeError, subprocess.SubprocessError) as exc:
        receipt.update({"status": "failed", "failure": str(exc)})
        save()
        print(f"C4_OCCURRENCE_QUINT_REFUSED {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
