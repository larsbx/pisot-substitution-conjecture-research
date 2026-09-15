"""Forbidden numerical or analytic primitives in executable source."""

from __future__ import annotations

from claim_governance.findings import Finding
from claim_governance.policy import Policy
from claim_governance.repo import Repo

CHECK = "numerics"


def check(policy: Policy, repo: Repo) -> tuple[Finding, ...]:
    findings = []
    for rule in policy.numerics:
        regex = rule.regex()
        for rel in repo.files(rule.paths):
            if rel in rule.allow_files:
                continue
            for lineno, line in enumerate(repo.masked(rel).split("\n"), start=1):
                if line.strip() in rule.allow_lines or not regex.search(line):
                    continue
                findings.append(Finding(rel, lineno, CHECK, rule.name, f"{rule.message or 'forbidden primitive'}: {line.strip()}"))
    return tuple(findings)
