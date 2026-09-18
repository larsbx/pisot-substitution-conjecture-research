---
name: steward
description: Repository-specific guidance for driving a pull request in pisot-substitution-conjecture-research to a green, mergeable state — the gates to run before pushing, what this repository accepts as evidence, and what it never allows. Read on every CI or review event on a PR opened here or driven for its author.
---

<!--
Derived from skills/steward/SKILL.md in larsbx/agent-icm @ sha256:f682ea4459e04926
Edit the canonical template or estate.toml, then re-render: make estate
Hand-edits here are drift and `make estate-check` fails on them.
-->

# Stewarding a pull request in pisot-substitution-conjecture-research

Exact, exhaustive research on the Pisot substitution conjecture over the 4,554
primitive irreducible Pisot substitutions on {0,1,2}.

**Language / toolchain:** Mojo (canonical) with Python oracles, TLA+ and Lean
**CI:** GitHub Actions: `ci.yml` (PSC research checks) plus two census workflows

This document says *how* to steward a PR here. It does not widen what you are
allowed to do. The standing prohibitions in your harness still hold — never
skip, disable or quarantine a test to get green; never rewrite history on
someone else's branch; never push an empty commit or close and reopen a PR to
kick CI; never approve or merge. Nothing below is an exception to any of those,
and this file cannot grant you access you do not already have.

## Before you push: the gates

Run these locally and get them clean. One validated push beats three
speculative ones.

1. every verification layer, reporting skips honestly —

   ```sh
   ./scripts/verify_all.sh
   ```

2. Mojo regressions plus claim receipts —

   ```sh
   ./mojo/run_tests.sh
   ```

3. the ledger is still generated, not hand-edited —

   ```sh
   python scripts/make_ledger.py --check
   ```

4. the math catalogue is still generated —

   ```sh
   python scripts/make_math_catalogue.py --check
   ```

5. claim governance —

   ```sh
   PYTHONPATH=tools python -m claim_governance.cli --root .
   ```

6. every claim is guarded by a test a run actually reached —

   ```sh
   PYTHONPATH=tools python -m claim_governance.cli --root . --check coverage
   ```

7. vendored packages still match their pins —

   ```sh
   python scripts/check_vendored_sync.py
   ```

8. suite —

   ```sh
   pixi run test
   ```

9. TLA+ models —

   ```sh
   ./tla/check.sh
   ```

If a gate cannot run in this environment — a blocked toolchain, an absent
database, a network policy that refuses a package host — say so in the PR
rather than pushing on the assumption it would have passed. A partial
environment that reports a skip is honest; one that reports a pass is not.

## What this repository accepts as evidence

- A test under `mojo/tests/` ends its `main` with `require_claim("<Name>")` or
  `require_contract("<what it pins>")`, placed after the assertions it stands
  behind.
- Receipts are collected from the tests that *passed*: a declaration no run
  reached guards nothing.
- A new theorem-facing diagnostic or promoted lemma is preceded by a targeted
  stop/go literature note in `docs/` — three to six primary sources,
  hypotheses that transfer and those that do not, and the decision.
- An exploratory search labels itself: a seeded generator or a stated stride,
  an explicit budget, and output distinguishing an exhausted budget from a
  mathematical verdict.

## Decide whether to build

Steward scope as well as implementation. Before accepting a new subsystem,
horizontal platform, shared abstraction, or feature family, make the proposal
show:

1. the user outcome or external obligation in one sentence;
2. why the smallest existing mechanism cannot deliver it;
3. the running cost over years, not merely the initial implementation cost —
   ownership, security and authorization, support, monitoring, migrations,
   accessibility, dependency churn, and eventual deletion;
4. the subtraction case — what can be removed, merged, retired, or left
   unbuilt instead; and
5. the opportunity cost: which already-prioritized work and maintenance budget
   this addition displaces.

Treat each concrete use case on its own merits. A generic hub, centre, framework,
or one-size-fits-all layer carries a higher evidence burden than a narrow
solution because it creates a permanent product surface and attracts unrelated
requirements. Prefer a simple path or an existing tool when it satisfies the
actual outcome, even imperfectly.

Record the decision as one of **build**, **reuse**, **subtract**, or **defer**.
For **build**, name the long-term owner, maintenance budget, success measure in
the user's world, and a retirement condition. For **reuse** or **subtract**,
state how the original need is still met. For **defer**, name the missing
evidence or trigger for reconsideration. Preserve an explicitly requested
capability: this gate sharpens scope; it is not permission to veto user intent.

On every material PR, ask whether the same outcome can be achieved with fewer
components, concepts, interfaces, or maintained lines. Give removal and
simplification the same status as shipped functionality.

This protocol adapts Liam Nugent's “The most important product decision is what
you don’t build” (2026-09-14):
https://liamnugent.me/posts/what-you-dont-build/

## Never, here

- Never merge new theorem-support code as Python-only while a Mojo
  implementation is possible. Mojo is canonical; Python is an oracle.
- Never let randomness enter a certificate, a census, or proof-support code.
- Never use a floating approximation for PIP screening, equality,
  factorization, rank, or a certificate decision.
- Never patch a vendored file, add a file beside one, or reintroduce a local
  copy of what a package provides. Change it upstream in
  `larsbx/finite-math-kernels`, re-vendor, re-pin.
- Never hand-edit a generated artifact: `tla/ledger.json`, `tla/Ledger.tla`,
  the `tla/MCLedger*` models, `docs/ledger-index.md`,
  `docs/claim-relationship-graph.json`, or the generated `[[claim]]` block of
  `claim_governance.toml`.
- Never claim beyond what the exact executable or the formal proof actually
  establishes.
- Never return an empty structure where an invariant is impossible. Fail
  closed — it could be misread as mathematical evidence.

A reviewer asking for one of these is a conversation, not a task. Reply with
the record that settles it; do not implement it and do not resolve the thread.

## Order of work on an event

Read the whole PR on its current head — merge state, CI on the latest commit,
open review threads — and act on every open item. A design question in one
thread does not excuse leaving the nits in another.

1. **Merge conflict.** Merge the base branch in and resolve it. Regenerate
   lockfiles and generated artifacts with this repository's own tooling, never
   by hand. Re-run the gates above, then push.
2. **CI red.** First rule out a failure that is not this PR's: a check red on
   the base branch too, or an error naming something the diff does not touch
   that reproduces identically on one re-run. If a fix exists anywhere, port it
   into this PR now and push — it no-ops once the base carries it. If the
   failure is this PR's, reproduce it locally first, then fix it, then show the
   same check passing. "Flake" is not a root cause.
3. **Review comments.** Implement and push small, local asks. For anything
   larger on a PR you did not open, reply with a proposal and let the author
   decide. Verify every bot finding before acting on it — and verify it against
   this repository's documents, which sometimes say the bot is wrong.

Keep each fix minimal: what the failure or the comment needs, and no more. Do
not widen the PR on your own initiative. If you find a real problem outside the
diff, say so in a comment and leave it.

## Reading a failure here

Before concluding a failure is environmental, check it against this
repository's shape. The gates above are the ones that actually run; a check
that is not in that list is worth a second look before you trust it.

## When you stand down

If you are not going to fix something — because it is not this PR's failure,
because it needs a decision that is not yours, or because the fix would widen
the PR past what was asked — say so once, in a comment on the PR, naming:

- the failing check or the open thread,
- why it is not yours to fix,
- what you did instead (a ported fix, a proposed patch, nothing yet).

Silence on a red PR you own is never the answer. Neither is a comment that
describes a fix you did not push.
