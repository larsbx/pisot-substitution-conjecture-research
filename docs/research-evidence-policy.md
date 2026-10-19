# Research evidence policy: show your work

The repository requires theorem-facing work to expose the **inspectable work**
behind the claim. This means repository-visible mathematical derivations,
hypotheses, exact evidence, replay instructions and claim boundaries. It does
**not** mean publishing private chain-of-thought or hidden scratch reasoning.

## Required evidence surface

Every theorem-facing pull request must contain a **Work shown** section with
all five subsections below.

### Assumptions and hypotheses

State every standing, imported and local hypothesis actually used. Say which
facts are derived rather than assumed. Explicitly call out legality,
independence, finite injectivity, unimodularity, realization, finite-domain
and non-unit representation assumptions when relevant.

### Derivation / reduction

Show enough of the derivation, reduction or proof skeleton that another
researcher can reconstruct the mathematical step. A final formula, verdict or
green workflow without the argument that connects inputs to conclusion is not
sufficient.

For computer-assisted work, identify the finite mathematical object, the
quantifiers the certificate covers, and why the executable check is complete
for those quantifiers.

### Evidence and replay

Name the exact source files, theorem statements and evidence packets. Give
deterministic replay commands for executable results, or point to formal proof
artifacts. Record caps, thresholds and fail-closed behavior. A CI status alone
is not the evidence; the receipt must be tied to a stated mathematical
contract.

### Negative controls

Record the counterexamples and rejected stronger variants that delimit the
result. If a route failed, preserve the failure. If a bounded computation
cannot distinguish exhausted budget from mathematical absence, say so and
ensure the executable does the same.

### Non-claims / remaining gaps

State what the contribution does **not** prove. Keep finite-domain, family,
conditional, imported and universal claims distinct. Name the next unresolved
quantifier or bridge rather than allowing a reader to infer closure from
proximity.

## Enforcement

The policy is machine-readable in `research_evidence_policy.toml`.

For pull requests that touch theorem-facing paths, the
`Show your work policy` workflow fails unless the PR body contains the five
required headings. Repository tests also pin the policy, this document,
`AGENTS.md`, and the PR template to the same heading contract.

This is a minimum evidence gate, not a proof checker. A PR can satisfy the
headings and still be mathematically wrong; ordinary review, exact tests,
formal checks and claim governance remain responsible for correctness and
status.

## Relationship to other policies

- `claim_governance.toml` governs claim status and promotion.
- `AGENTS.md` governs implementation, research gates and evidence practice.
- Independent human review remains a final validation gate under the existing
  review policy.
- This policy governs **inspectability**: a result used by the project must
  leave enough evidence for another researcher to audit what was done and why.
