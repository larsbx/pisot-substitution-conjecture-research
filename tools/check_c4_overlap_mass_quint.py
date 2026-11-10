#!/usr/bin/env python3
"""Replay bounded overlap-mass controls and bind every expected mutation.

Mathematics executes in Quint. This tool only authenticates source, revision,
test inventory and assertion-failing controls; no finite run proves C4.
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
MODEL = ROOT / "proof/quint/C4OverlapMass.qnt"
VERSION = "0.33.1"
EXPECTED = [
    "domainCountTest",
    "finiteIntervalPartitionTest",
    "finiteScaledSubdivisionTest",
    "affineTranslationTest",
    "strictCompleteCarrierConservativeTest",
    "occurrenceMultiplicityTest",
    "boundaryAndDegenerateTest",
    "positiveWrongRowTest",
    "omittedOccurrenceBudgetTest",
    "literalMixedOrbitCountsTest",
    "finiteQuotientCountsTest",
    "uniformityIsNecessaryTest",
    "allFixedAndFreeOrbitsTest",
    "transposeOrientationTest",
    "mixedConservativeWeightedTest",
    "mixedStrictWeightedTest",
]
MUTATIONS = [
    (
        "equal-packet-occurrences-deduplicated",
        "pure def sumMass(ps, ls) = ps.foldl(0, (out, p) => out + packetMass(p, ls))",
        "pure def sumMass(ps, ls) = ps.foldl(Set(), (out, p) => out.union(Set(p)))\n"
        "    .fold(0, (out, p) => out + packetMass(p, ls))",
        "occurrenceMultiplicityTest",
    ),
    (
        "boundary-contact-counted-positive",
        "if (right > left) right - left else 0",
        "if (right > left) right - left else (if (right == left) 1 else 0)",
        "boundaryAndDegenerateTest",
    ),
    (
        "incidence-scaling-omitted",
        "add3(incidence(s, r), sub3(prefixVector(s[a], i), prefixVector(s[b], j)))",
        "add3(r, sub3(prefixVector(s[a], i), prefixVector(s[b], j)))",
        "affineTranslationTest",
    ),
    (
        "image-length-equations-ignored",
        "ls[a] >= 0 and prefixMass(s[a], s[a].length(), ls) == beta * ls[a])",
        "ls[a] >= 0)",
        "positiveWrongRowTest",
    ),
    (
        "omitted-positive-mass-erased",
        "pure def omittedMass(ps, ls, mask) = ps.indices().filter(i => not(selected(mask, i)))\n"
        "    .fold(0, (out, i) => out + packetMass(ps[i], ls))",
        "pure def omittedMass(ps, ls, mask) = 0",
        "omittedOccurrenceBudgetTest",
    ),
    (
        "orbit-size-weights-ignored",
        "pure def weighted(h, m) = range(0, h.length()).foldl(List(), (out, i) => out.append(m[i] * h[i]))",
        "pure def weighted(h, m) = h",
        "mixedConservativeWeightedTest",
    ),
    (
        "transpose-indices-reversed",
        "columns.append(range(0, t.length()).foldl(0, (out, i) => out + t[i][j] * h[i])))",
        "columns.append(range(0, t.length()).foldl(0, (out, i) => out + t[j][i] * h[i])))",
        "transposeOrientationTest",
    ),
    (
        "incoming-count-direction-reversed",
        "pure def incoming(edges, labels, x, j) = edges.select(e => e._2 == x and labels[e._1] == j).length()",
        "pure def incoming(edges, labels, x, j) = edges.select(e => e._1 == x and labels[e._2] == j).length()",
        "literalMixedOrbitCountsTest",
    ),
    (
        "fiber-uniformity-ignored",
        "pure def uniformCounts(edges, labels, representatives) = labels.indices().forall(x => representatives.indices().forall(j =>\n"
        "    outgoing(edges, labels, x, j) == outgoing(edges, labels, representatives[labels[x]], j) and\n"
        "    incoming(edges, labels, x, j) == incoming(edges, labels, representatives[labels[x]], j)))",
        "pure def uniformCounts(edges, labels, representatives) = true",
        "uniformityIsNecessaryTest",
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
        "schema": "psc-c4-overlap-mass-quint-v1", "status": "started",
        "quint_version": VERSION, "backend": "typescript", "seed": "20261110",
        "scope": "exhaustive bounded interval, actual digit and literal quotient-count controls",
        "binary_words_length_0_through_2": 7,
        "nonnegative_binary_length_rows_0_through_2": 9,
        "integer_displacements_minus_2_through_2": 5,
        "interval_partition_inputs": 2205,
        "constant_length_two_binary_substitutions": 16,
        "scaled_source_type_residual_inputs": 1600,
        "strict_nonpip_actual_marks": 16,
        "strict_nonpip_positive_packet_labels": 12,
        "four_digit_occurrence_retention_masks": 16,
        "directed_three_state_graphs_with_loops": 512,
        "note": "Every finite forall is exhausted; no random samples, Pisot census, geometric loss or C4 conclusion.",
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
        tree = subprocess.check_output(["git", "rev-parse", "HEAD^{tree}"], cwd=ROOT, text=True).strip()
        status_command = ["git", "status", "--porcelain"]
        initial_status = subprocess.check_output(status_command, cwd=ROOT, text=True).strip()
        receipt.update({
            "git_head": revision, "git_tree": tree, "model_sha256": digest(source),
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
        common = ["--main=C4OverlapMass", "--backend=typescript", "--max-samples=1", "--seed=20261110"]
        with tempfile.TemporaryDirectory(prefix="psc-c4-overlap-mass-") as temporary:
            snapshot = Path(temporary) / "C4OverlapMass.qnt"
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
                mutant_source = text.replace(before, after, 1).encode()
                mutant.write_bytes(mutant_source)
                mutant.chmod(0o444)
                result = run(["test", str(mutant)] + common + [f"--match=^{test}$"], name)
                failed = re.findall(r"\d+\) (\w+) failed after (\d+) test\(s\)", result.stdout)
                if result.returncode == 0 or failed != [(test, "1")] or "Error [QNT508]" not in result.stdout:
                    raise RuntimeError(f"mutation {name} did not reach its expected assertion")
                if mutant.read_bytes() != mutant_source:
                    raise RuntimeError(f"private mutation snapshot changed: {name}")
                receipt["rejected_mutations"].append({"name": name, "test": test, "sha256": digest(mutant.read_bytes())})
                save()
            if snapshot.read_bytes() != source:
                raise RuntimeError("private source snapshot changed")
        if MODEL.read_bytes() != source or runner.read_bytes() != runner_source:
            raise RuntimeError("model or runner changed during verification")
        if subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip() != revision:
            raise RuntimeError("Git revision changed during verification")
        if subprocess.check_output(["git", "rev-parse", "HEAD^{tree}"], cwd=ROOT, text=True).strip() != tree:
            raise RuntimeError("Git tree changed during verification")
        receipt["worktree_dirty"] |= bool(subprocess.check_output(status_command, cwd=ROOT, text=True).strip())
        receipt["source_and_revision_recheck"] = "unchanged"
        receipt["status"] = "passed"
        save()
        print(f"C4_OVERLAP_MASS_QUINT_ACCEPTED {len(EXPECTED)} tests; {len(MUTATIONS)} mutations")
        return 0
    except (OSError, RuntimeError, UnicodeError, subprocess.SubprocessError) as exc:
        receipt.update({"status": "failed", "failure": str(exc)})
        save()
        print(f"C4_OVERLAP_MASS_QUINT_REFUSED {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
