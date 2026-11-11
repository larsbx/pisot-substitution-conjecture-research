#!/usr/bin/env python3
"""Historical, restricted integration helper for PSC PR #487.

The current PR487 acceptance workflow only tests the checked-out revision and
does not invoke this helper's prepare or publish operations. Preserve these
guards for replay of the original reconciliation attempt.

Runs in a complete checkout. Resolves only the three known integration files,
regenerates the Proof Bank with the repository generator, and never changes
claim status. Publishing is a separate explicit operation with a head lease.
No network credentials or authorization are stored in the receipt.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import urllib.request

REPOSITORY = "larsbx/pisot-substitution-conjecture-research"
BRANCH = "research/c4-return-induction-prefix-satellite-2026-11-04"
PR = 487
LEDGER = "docs/side-notes-ledger.md"
BANK_JSON = "proof/proof-bank.json"
BANK_MD = "docs/proof-bank.md"
ALLOWED_CONFLICTS = {LEDGER, BANK_JSON, BANK_MD}
RETURN_TESTS = [
    "tests/test_c4_return_induction_prefix_satellite_oracle.py",
    "tests/test_c4_return_boundary_carrier_oracle.py",
    "tests/test_c4_return_overlap_closure_oracle.py",
]
LEDGER_ADDITION = """
- **2026-11-05 — PR #487 return-boundary carrier integration locator.** The specimen sigma=(01,121,012) has an exact 28-state local return-cut carrier with all 80 ordered child occurrences and literal decoding identities; the two-phase Q/V recurrence retains unbounded word registers. Matching local cuts alone does not imply balanced full prefixes. Source: [return-boundary carrier](c4-return-boundary-carrier-2026-11-04.md). This integration entry supplies the previously missing central locator; it does not promote general C4 or PSC.

- **2026-11-05 — PR #487 complete rooted return-overlap closure integration locator.** The fixed aligned-return root family has 118 initial strict overlaps, 1,134 reachable decorated states, 3,106 child occurrences and a sharp maximum minimum coincidence depth of five; the occurrence-complete physical quotient has 87 types and 230 occurrences. Queue exhaustion, complete rows and genuine paths are checked independently; the observed defect range is not an input cutoff. Source: [rooted overlap closure](c4-return-overlap-closure-2026-11-04.md), `evidence/c4-return-overlap-closure-2026-11-04/receipt.json`. This is specimen/root-specific, not an arbitrary-carrier transfer or a universal C4/PSC theorem. Native/hosted acceptance must be read from the exact integrated revision's workflow, not inferred from this ledger entry.
"""
README_ADDITION = """

## Return-word family integration (#487)

The fixed Pisot specimen `sigma=(01,121,012)` now has linked
[return-induction](docs/c4-return-induction-prefix-satellite-counterexample-2026-11-04.md),
[boundary-carrier](docs/c4-return-boundary-carrier-2026-11-04.md), and
[complete rooted overlap](docs/c4-return-overlap-closure-2026-11-04.md) records.
The 1,134-state graph is scoped to the stated aligned-return roots: its
five-step productivity bound does not prove an arbitrary strict-carrier
transfer or general PSC. Written proofs, independent Python replay, native
Mojo execution, and independent mathematical review remain distinct evidence.
"""


def merge_append_only(base: str, ours: str, theirs: str) -> str:
    """Preserve both complete append histories; refuse an edited old ledger."""
    if not ours.startswith(base) or not theirs.startswith(base):
        raise ValueError("ledger is not append-only relative to its merge base")
    left, right = ours[len(base):], theirs[len(base):]
    if left == right or right.endswith(left):
        return theirs
    if left.endswith(right):
        return ours
    return base + right + left


def headings(bank: dict) -> set[tuple[str, str]]:
    return {(row["source"], row["statement_heading"])
            for row in bank["source_statements"]}


def verify_inventory(main: dict, branch: dict, generated: dict) -> None:
    """Retain mainline statements and all branch-only source inventories."""
    current = headings(generated)
    if headings(main) - current:
        raise ValueError("regeneration lost a mainline source statement")
    main_sources = {source for source, _ in headings(main)}
    branch_only = {entry for entry in headings(branch)
                   if entry[0] not in main_sources}
    if branch_only - current:
        raise ValueError("regeneration lost a branch-only source statement")
    for field in ("claims", "lean_declarations", "pins", "input_digests"):
        if generated[field] != main[field]:
            raise ValueError(f"integration unexpectedly changed {field}")


def run(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(args, text=True, capture_output=True)
    if result.stdout:
        print(result.stdout, end="", flush=True)
    if result.stderr:
        print(result.stderr, end="", file=sys.stderr, flush=True)
    if check and result.returncode:
        raise RuntimeError(f"command failed with exit {result.returncode}: {args[0]}")
    return result


def git(*args: str) -> str:
    result = subprocess.run(["git", *args], text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f"git {args[0]} failed: {result.stderr.strip()}")
    return result.stdout


def read_at(ref: str, path: str) -> str:
    return git("show", f"{ref}:{path}")


def pr_metadata() -> dict:
    token = os.environ.get("GH_TOKEN")
    if not token:
        raise RuntimeError("GH_TOKEN is required for exact PR/head verification")
    request = urllib.request.Request(
        f"https://api.github.com/repos/{REPOSITORY}/pulls/{PR}",
        headers={"Authorization": f"Bearer {token}",
                 "Accept": "application/vnd.github+json",
                 "X-GitHub-Api-Version": "2022-11-28"},
    )
    with urllib.request.urlopen(request, timeout=30) as response:
        return json.load(response)


def assert_pr(expected: str) -> None:
    data = pr_metadata()
    if (data["state"] != "open" or data["base"]["ref"] != "main"
            or data["head"]["ref"] != BRANCH
            or data["head"]["repo"]["full_name"] != REPOSITORY
            or data["head"]["sha"] != expected):
        raise RuntimeError("PR identity, base or expected head changed; refuse write")


def write_outputs(path: str | None, receipt: dict) -> None:
    if path:
        with open(path, "a", encoding="utf-8") as output:
            for key in ("integrated_sha", "main_sha", "expected_head"):
                output.write(f"{key}={receipt[key]}\n")


def prepare(expected: str, receipt_path: Path, output_path: str | None) -> None:
    if os.environ.get("GITHUB_REPOSITORY") != REPOSITORY:
        raise RuntimeError("restricted workflow requires the exact source repository")
    if git("rev-parse", "HEAD").strip() != expected:
        raise RuntimeError("checkout differs from the requested exact head")
    if git("status", "--porcelain").strip():
        raise RuntimeError("worktree must be clean before reconciliation")
    assert_pr(expected)
    run("git", "fetch", "--no-tags", "origin", "main", BRANCH)
    main_sha = git("rev-parse", "origin/main").strip()
    base = git("merge-base", expected, main_sha).strip()
    before_main = json.loads(read_at(main_sha, BANK_JSON))
    before_branch = json.loads(read_at(expected, BANK_JSON))
    ledger = merge_append_only(read_at(base, LEDGER),
                              read_at(expected, LEDGER), read_at(main_sha, LEDGER))
    run("git", "config", "user.name", "github-actions[bot]")
    run("git", "config", "user.email", "41898282+github-actions[bot]@users.noreply.github.com")
    result = run("git", "merge", "--no-commit", "--no-ff", main_sha, check=False)
    conflicts = set(filter(None, git("diff", "--name-only", "--diff-filter=U").splitlines()))
    if conflicts - ALLOWED_CONFLICTS or (result.returncode and not conflicts):
        raise RuntimeError("unexpected merge failure/conflict; preserve inputs and stop")
    # Choose no handwritten generated output: clear stages, then regenerate.
    for path in (BANK_JSON, BANK_MD):
        if path in conflicts:
            run("git", "checkout", "--theirs", "--", path)
    if "PR #487 return-boundary carrier integration locator" not in ledger:
        ledger += LEDGER_ADDITION
    Path(LEDGER).write_text(ledger, encoding="utf-8")
    readme = Path("README.md")
    text = readme.read_text(encoding="utf-8")
    if "## Return-word family integration (#487)" not in text:
        readme.write_text(text + README_ADDITION, encoding="utf-8")
    run(sys.executable, "tools/make_proof_bank.py")
    generated = json.loads(Path(BANK_JSON).read_text(encoding="utf-8"))
    verify_inventory(before_main, before_branch, generated)
    run("git", "add", "--", LEDGER, BANK_JSON, BANK_MD, "README.md")
    if git("diff", "--name-only", "--diff-filter=U").strip():
        raise RuntimeError("unresolved merge stages remain")
    run("git", "diff", "--cached", "--check")
    run(sys.executable, "tools/make_proof_bank.py", "--check")
    run(sys.executable, "-m", "pytest", "-q", "tests/test_pr487_integration.py", *RETURN_TESTS)
    # Commit the actual merged source tree before native execution. The native
    # job below tests this SHA, not a mutable branch name or synthesized counts.
    staged = git("diff", "--cached", "--name-only").strip()
    if staged or Path(".git/MERGE_HEAD").exists():
        run("git", "commit", "-m",
            "Merge current main into PR #487; regenerate source inventories and retain both ledgers")
    integrated = git("rev-parse", "HEAD").strip()
    if git("merge-base", "--is-ancestor", expected, integrated) != "":
        raise RuntimeError("expected head is not an ancestor of the integration")
    if git("merge-base", "--is-ancestor", main_sha, integrated) != "":
        raise RuntimeError("current main is not an ancestor of the integration")
    receipt = {
        "schema": "psc-pr487-integration-v1",
        "expected_head": expected, "main_sha": main_sha,
        "merge_base": base, "integrated_sha": integrated,
        "resolved_conflicts": sorted(conflicts),
        "main_source_statements": len(before_main["source_statements"]),
        "integrated_source_statements": len(generated["source_statements"]),
        "claims_unchanged": True, "python_preflight": "passed",
        "native_acceptance": "not_yet_executed", "published": False,
    }
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    write_outputs(output_path, receipt)


def publish(receipt_path: Path) -> None:
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    expected, integrated = receipt["expected_head"], receipt["integrated_sha"]
    if git("rev-parse", "HEAD").strip() != integrated:
        raise RuntimeError("tested integration SHA changed")
    if git("status", "--porcelain").strip():
        raise RuntimeError("worktree changed after exact revision validation")
    assert_pr(expected)
    # A normal fast-forward also preserves history; the explicit lease rejects
    # a concurrent writer even if an unusual ancestor relationship would permit it.
    run("git", "push", f"--force-with-lease=refs/heads/{BRANCH}:{expected}",
        "origin", f"{integrated}:refs/heads/{BRANCH}")
    receipt["published"] = True
    # This operation is called only after every native and governance step has
    # succeeded; it does not create a claim of independent mathematical review.
    receipt["native_acceptance"] = "workflow_native_and_parity_steps_passed"
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("prepare", "publish"))
    parser.add_argument("--expected-head")
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--github-output")
    args = parser.parse_args()
    if args.mode == "prepare":
        if not args.expected_head:
            parser.error("prepare needs --expected-head")
        prepare(args.expected_head, args.receipt, args.github_output)
    else:
        publish(args.receipt)


if __name__ == "__main__":
    main()
