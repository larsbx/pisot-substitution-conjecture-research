#!/usr/bin/env python3
"""Replay bounded normalized-slot and discovery controls with bound mutations.

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
MODEL = ROOT / "proof/quint/C4LiteralInverseBinding.qnt"
VERSION = "0.33.1"
EXPECTED = ['boundedDomainTest',
 'normalizedLiteralRoundTripTest',
 'normalizedSwapMateTest',
 'geometricTranslationTest',
 'orientationBitRequiredTest',
 'repeatedPositionInventoryTest',
 'earlierBirthsReachBothOrientationsTest',
 'circularBirthsRejectedTest',
 'swappedBirthMateRequiredTest']
MUTATIONS = [('target-orientation-erased',
  'pure def raw(slot) = if (slot._5) swap(slot._2) else slot._2',
  'pure def raw(slot) = slot._2',
  'normalizedLiteralRoundTripTest'),
 ('swap-indices-unexchanged',
  'pure def swapEdge(e) = (swap(e._1), e._3, e._2, swap(e._4))',
  'pure def swapEdge(e) = (swap(e._1), e._2, e._3, swap(e._4))',
  'normalizedLiteralRoundTripTest'),
 ('canonical-piece-translation-uncorrected',
  'pure def translation(s, slot) = if (slot._5)\n'
  '    add(slot._1._3, prefix(s[raw(slot)._2], slot._4))\n'
  '    else prefix(s[raw(slot)._1], slot._3)',
  'pure def translation(s, slot) = prefix(s[raw(slot)._1], slot._3)',
  'geometricTranslationTest'),
 ('inventory-compares-only-targets',
  'pure def sameSlots(expected, submitted) = expected.length() == submitted.length() and\n'
  '    expected.indices().forall(i => submitted.select(x => x == expected[i]).length() == 1)',
  'pure def sameSlots(expected, submitted) = sameTargets(expected, submitted)',
  'repeatedPositionInventoryTest'),
 ('slot-equation-ignored',
  'child(s, p, slot._3, slot._4) == slot._1',
  'true',
  'orientationBitRequiredTest'),
 ('earlier-birth-order-ignored',
  'pure def validBirths(bs) = bs.indices().forall(k => bs[k]._1 >= 0 and bs[k]._1 < k + 1)',
  'pure def validBirths(bs) = bs.indices().forall(k => bs[k]._1 >= 0)',
  'circularBirthsRejectedTest'),
 ('swapped-birth-mate-omitted',
  '((bs[k]._1, false), (k + 1, bs[k]._2)),\n    ((bs[k]._1, true), (k + 1, not(bs[k]._2))))))',
  '((bs[k]._1, false), (k + 1, bs[k]._2)))))',
  'earlierBirthsReachBothOrientationsTest')]


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
        "schema": "psc-c4-literal-inverse-binding-quint-v1", "status": "started",
        "quint_version": VERSION, "backend": "typescript", "seed": "20261110",
        "scope": "finite normalized literal slots, translation correction and discovery ancestry",
        "constant_length_two_binary_substitutions": 16,
        "ordered_occurrences_per_substitution": 144,
        "ordered_occurrences": 2304,
        "mixed_inventory_slots": 6,
        "three_state_oriented_birth_trees": 8,
        "note": "All finite quantifiers exhausted; no compact coverage, positivity or twelve-source certification.",
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
        common = ["--main=C4LiteralInverseBinding", "--backend=typescript", "--max-samples=1", "--seed=20261110"]
        with tempfile.TemporaryDirectory(prefix="psc-c4-literal-inverse-binding-") as temporary:
            snapshot = Path(temporary) / "C4LiteralInverseBinding.qnt"
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
        print(f"C4_LITERAL_INVERSE_BINDING_QUINT_ACCEPTED {len(EXPECTED)} tests; {len(MUTATIONS)} mutations")
        return 0
    except (OSError, RuntimeError, UnicodeError, subprocess.SubprocessError) as exc:
        receipt.update({"status": "failed", "failure": str(exc)})
        save()
        print(f"C4_LITERAL_INVERSE_BINDING_QUINT_REFUSED {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
