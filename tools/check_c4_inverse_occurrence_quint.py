#!/usr/bin/env python3
"""Replay bounded inverse-occurrence controls and bind every expected mutation.

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
MODEL = ROOT / "proof/quint/C4InverseOccurrence.qnt"
VERSION = "0.33.1"
EXPECTED = ['domainCountTest',
 'literalInverseIdentityTest',
 'incomingMarkGuardsTest',
 'swappedLiteralDigitsTest',
 'interiorPullbackTest',
 'diagonalInteriorDescendantsTest',
 'boundaryDiagonalCountercontrolTest',
 'wrongScalingPullbackCountercontrolTest',
 'swapFixedIffDiagonalTest',
 'scalarZeroIsNotFixedTest',
 'finiteTwoStepAncestryTest',
 'actualFreeDomainSwapCountsTest',
 'allSwapClosedSubdomainsTest',
 'missingSwapEdgeCountercontrolTest',
 'actualMixedOrbitWeightsTest',
 'repeatedOccurrenceIdentityTest',
 'nonSwapClosedDomainCountercontrolTest',
 'inverseClosedForwardLeakTest']
MUTATIONS = [('inverse-prefix-sign-reversed',
  'incidence(s, p._3) == add(q._3, sub(prefix(s[p._2], j), prefix(s[p._1], i)))',
  'incidence(s, p._3) == add(q._3, sub(prefix(s[p._1], i), prefix(s[p._2], j)))',
  'literalInverseIdentityTest'),
 ('incoming-selected-letter-ignored',
  's[p._1][i] == q._1 and s[p._2][j] == q._2 and',
  'true and',
  'incomingMarkGuardsTest'),
 ('swap-digit-indices-not-swapped',
  'pure def swapEdge(e) = (swap(e._1), e._3, e._2, swap(e._4))',
  'pure def swapEdge(e) = (swap(e._1), e._2, e._3, swap(e._4))',
  'swappedLiteralDigitsTest'),
 ('forward-incidence-omitted',
  'add(incidence(s, p._3), sub(prefix(s[p._1], i), prefix(s[p._2], j))))',
  'add(p._3, sub(prefix(s[p._1], i), prefix(s[p._2], j))))',
  'literalInverseIdentityTest'),
 ('diagonal-residual-ignored',
  'pure def diagonal(p) = p._1 == p._2 and p._3 == (0, 0, 0)',
  'pure def diagonal(p) = p._1 == p._2',
  'scalarZeroIsNotFixedTest'),
 ('boundary-contact-counted-positive',
  'if (right > left) right - left else 0',
  'if (right > left) right - left else (if (right == left) 1 else 0)',
  'boundaryDiagonalCountercontrolTest'),
 ('exact-scaling-ignored',
  'ls[a] > 0 and dot(ls, prefix(s[a], s[a].length())) == beta * ls[a])',
  'ls[a] > 0)',
  'wrongScalingPullbackCountercontrolTest'),
 ('edge-swap-closure-ignored',
  'pure def edgeSwapClosed(es) = es.indices().forall(i =>\n'
  '    es.select(e => e == swapEdge(es[i])).length() == 1)',
  'pure def edgeSwapClosed(es) = true',
  'missingSwapEdgeCountercontrolTest'),
 ('outgoing-occurrences-deduplicated',
  'pure def outgoing(es, p, q) = es.select(e => e._1 == p and canonical(e._4) == q).length()',
  'pure def outgoing(es, p, q) = es.select(e => e._1 == p and canonical(e._4) == q)\n'
  '    .foldl(Set(), (out, e) => out.union(Set((e._1, e._4)))).size()',
  'repeatedOccurrenceIdentityTest'),
 ('incoming-count-direction-reversed',
  'pure def incomingCount(es, p, q) = es.select(e => e._4 == p and canonical(e._1) == q).length()',
  'pure def incomingCount(es, p, q) = es.select(e => e._1 == p and canonical(e._4) == q).length()',
  'actualMixedOrbitWeightsTest'),
 ('all-orbit-weights-forced-two',
  'pure def weight(ps, q) = ps.select(p => canonical(p) == q).length()',
  'pure def weight(ps, q) = 2',
  'actualMixedOrbitWeightsTest'),
 ('domain-swap-closure-ignored',
  'pure def swapClosed(ps) = ps.indices().forall(i => hasPacket(ps, swap(ps[i])))',
  'pure def swapClosed(ps) = true',
  'nonSwapClosedDomainCountercontrolTest'),
 ('inverse-closure-treated-as-forward-closure',
  'pure def positiveForwardClosed(s, ps) = ps.indices().forall(k => {\n'
  '    val cs = children(s, ps[k])\n'
  '    cs.indices().forall(i => mass(cs[i], lengths) == 0 or hasPacket(ps, cs[i]))\n'
  '  })',
  'pure def positiveForwardClosed(s, ps) = boundedInverseClosed(s, ps)',
  'inverseClosedForwardLeakTest')]


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
        "schema": "psc-c4-inverse-occurrence-quint-v1", "status": "started",
        "quint_version": VERSION, "backend": "typescript", "seed": "20261110",
        "scope": "finite literal inverse digits, interior ancestry and actual swap-orbit edge counts",
        "constant_length_two_binary_substitutions": 16,
        "source_type_residual_inputs": 1600,
        "ordered_one_step_occurrences": 6400,
        "ordered_two_step_histories": 25600,
        "strict_nonpip_positive_packet_labels": 12,
        "strict_nonpip_free_swap_orbits": 6,
        "swap_closed_induced_subdomains": 64,
        "mixed_actual_ordered_states": 3,
        "mixed_actual_occurrence_edges": 6,
        "leaking_inverse_candidate_occurrences": 9000,
        "note": "Every finite forall is exhausted; no compact inverse domain, Pisot census, geometric loss or C4 conclusion.",
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
        common = ["--main=C4InverseOccurrence", "--backend=typescript", "--max-samples=1", "--seed=20261110"]
        with tempfile.TemporaryDirectory(prefix="psc-c4-inverse-occurrence-") as temporary:
            snapshot = Path(temporary) / "C4InverseOccurrence.qnt"
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
        print(f"C4_INVERSE_OCCURRENCE_QUINT_ACCEPTED {len(EXPECTED)} tests; {len(MUTATIONS)} mutations")
        return 0
    except (OSError, RuntimeError, UnicodeError, subprocess.SubprocessError) as exc:
        receipt.update({"status": "failed", "failure": str(exc)})
        save()
        print(f"C4_INVERSE_OCCURRENCE_QUINT_REFUSED {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
