# PR 659: main integration and verification record

## Recorded scope

This packet records integration of main
`47db0f142573ebdd75cab7ecdaf1345e2e149df2` into the existing PR head
`ab71641a847fbce0f1044ecaa968a363eb4c4042`. It is a local integration record,
not a completed hosted acceptance receipt. The PR records the published
integration commit, exact tree, and subsequent hosted outcomes separately.

Main adds `PscVerif.BetaGoldenEndpoint`, its explanatory note and root import.
The combined generated inventory retains all 7,396 declaration names from
both parents, without a changed declaration statement. Both root-import
lists and the append-only side ledger are preserved. All 136 governed claims
remain unchanged from the PR parent; the general conjecture remains open.

All 18 BH gate modules and all 1,364 pre-existing Lean theorem, Mojo kernel
and Python oracle source files are byte-identical to the PR parent.
The golden-base source and explanatory note are byte-identical to main.
See [the reproducible source comparison](source-preservation.json).
These comparisons establish source continuity, not completion of a new
combined-tree formal audit.

The only workflow change raises the physical-mass full Lean job allowance
from 35 to 180 minutes. Commands, checks, pins, audit requirements and all
other job settings are unchanged. The separate historical runner-loss
incident has no identified compiler error; its exact cause remains unknown.

## Local integration checks

- [Focused regression receipt](local-tests.json): 302 passed, no skipped
  tests, before this receipt packet was added; [complete output](local-tests.log).
- [All six claim-governance checks](claim-governance.log) passed.
- [Nine recorded checks](local-checks.json) passed: proof inventory, ledger,
  mathematical catalogue, manuscript, Markdown source, vendored pins,
  polyglot rendering, worktree whitespace and staged whitespace.
  [Complete command output](local-checks.log) retains each exit status.
- The proof inventory reports 136 claims, 7,396 named Lean proofs and 546
  source openings. Inventory counts are not claims of that many new results.

The checks cover the resolved integration source, not a new isolated build
of every Lean dependency. The original isolated BH proof and exact native
replay packet remains unchanged at
[bh-diagonal-closure-2026-11-27](../bh-diagonal-closure-2026-11-27/README.md).
Its original 8,211-file source bindings must not be relabelled as covering
this new module, root import, inventory, workflow or receipt packet.

## Historical hosted outcomes

| Head and run | Observed result | Credit |
| --- | --- | --- |
| `ab71641`, [BH closure 46047919445](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/46047919445) | Succeeded | Dedicated BH gate for that exact historical head |
| `ab71641`, [overlap 46047918850](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/46047918850/job/140671718261) | Runner lost communication; no downloadable complete log | No full-gate acceptance |
| `ab71641`, [physical mass 46047919125](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/46047919125/job/140671724888) | 35-minute timeout after 9,242 of 9,250 build jobs | Partial compilation only; no completed full audit |

[The diagnosis](ci-diagnosis.md) preserves the exact annotation texts,
timestamps, scope and the observed successful partial builds. It does not
rewrite either interruption as a passing run. Hosted checks for the new
integration head remain pending at this packet's creation.

## Integrity and non-claims

`SHA256SUMS` pins every file in this packet other than itself. The previous
closure packet is not overwritten. Post-archive integrity/link checks and
new-head CI are reported with their own actual revisions in PR 659.

No mathematical claim is promoted by this integration. The distinction
between Lean family arithmetic and three-band BPA, written spectral transfer,
and the still-open general PSC/BH/A1-prime/C4 obligations is retained.
Independent human review remains pending; no such review is asserted.
