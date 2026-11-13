# Exclude strict systems for the two named substitutions

This increment connects the positive-overlap bridge to the original
kernel-checked root certificates for `1/021/001` and `1/012/001`.
The new source excludes every finite strict system for either authenticated
fixture, independently of the number of states. Complete acceptance is
reported separately from source construction below. General C4 and PSC
retain their existing status.

## Work shown

### Assumptions and hypotheses

The generic consumer takes an original `ArchivedPayload.Packet` and its
`Valid` proof. That proof authenticates the literal fixture, full positional
rows, exhaustive decoded closure, original roots and integer potential.
The generated consumers discharge `Valid` by kernel evaluation on each
actual archived payload.

The final `Packet.no_strictSystem` theorem takes only that validated packet
and an arbitrary finite word-pair carrier `C`. It has no extra root-coverage,
positive-measure, maximum-word-length, or Haar-existence premise. The
statement remains restricted to the two literal fixture substitutions.

### Derivation / reduction

1. `intersection_eq_archivedRoot` covers all six ordered distinct-letter
   pairs by the three original zero-offset roots `01`, `02`, and `12`.
   Reversing the letter order uses commutativity of intersection. It does
   not identify arbitrarily displaced, swapped overlaps.
2. A supplied `StrictSystem` makes every represented `CutPair` distinct.
   `carrierOverlap_subset_archivedRoots` therefore places its whole
   overlap union inside the finite union of those three root overlaps.
3. `NamedPositiveOverlap.carrierOverlap_measure_pos` forces this same
   carrier overlap to have positive measure. `Packet.roots_null` makes
   each covering root null. Both use exactly
   `(volume : Measure Stable).prod nu`; the `internalMeasure` abbreviation
   changes no normalization.
4. `OverlapContraction.no_positive_subset_of_null` gives a contradiction
   from the finite cover, nullity and positivity. No inference from
   nullity to emptiness is made.
5. Compactness of the original matrix-adic carrier supplies its whole
   space as a positive compact set. Mathlib's `Measure.addHaarMeasure`
   normalized on that set has mass one. The final consumer constructs
   this measure internally and discharges the probability Haar premise.

`Packet.no_strictComponent` and `Packet.no_bpaStrictComponent` then apply
the existing projections to `StrictSystem`. They supply no global
extraction theorem.

The [pre-code source decision](c4-named-strict-exclusion-literature-2026-11-12.md)
records the standard measure argument, geometric hypotheses and rejected
overextensions. No new census or numerical source-loss search is needed.

### Evidence and replay

The canonical Mojo exporter now emits a `no_strict_system` proof for each
complete actual fixture. The independent Lean auditor requires its exact
unconditional statement at literal fixture `0` or `1`, audits its transitive
axioms, and continues to reconstruct the emitted positional data with the
independent Python oracle. The semantic proof set grows from six to seven;
earlier archived receipts remain historical records with their original
scope.

Canonical replay from the repository root:

```sh
python3 tools/make_proof_bank.py --check
python3 -m unittest discover -s tests -p test_archived_payload_lean_replay.py -v
(cd kernel && pixi run --locked mojo build -I . c4_archived_lean_export.mojo -o /tmp/c4-archived-export)
./tools/check_lean.sh --archived-packets /tmp/c4-archived-export /tmp/c4-named-exclusion-replay
```

The output directory for the concrete replay must be fresh. The complete
gate uses isolated sources and the pinned Lean/Mathlib revisions, rebuilds
the aggregate, audits the whole compiled proof bank, and then checks both
actual generated payloads. A source inventory or a focused development
build alone does not complete that gate.

Acceptance verified on 2026-11-13 at 06:45:19 UTC: **mechanically certified
for the two named substitutions at the recorded scope**. The
[exact-head hosted run](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43365333027)
completed the full archived-payload gate on attempt `1`, job
`131688284776`, for commit
`bb6cbac16a620da4784f5b30d0a9a242618aef22`, tree
`42472cf9f43d2e13bb999fd5c339abfea782d690`. The retained
[acceptance evidence](../evidence/c4-named-strict-exclusion-2026-11-13/accepted-bb6cbac/README.md) binds the
successful run and job, exact sources, artifact download provenance and
bytes, and completed inspection. Its compiled proof-bank audit reached
6,805 declarations and 4,996 theorems. The inspector matched all ten
explicit new theorems and both control definitions, and checked both
actual generated fixtures against all seven semantic proof types,
including the unconditional `no_strict_system` statement. The separate
wrong-type exclusion control and all 32 native mutation controls were
also verified. All 126 governed claim statuses remain unchanged;
independent human review remains separate validation debt.

Acceptance was pending at source construction. The incomplete and failed
attempts below retain their original outcomes and supply no acceptance
credit; the result above comes from the separate successful exact-head
gate and its inspected evidence.

The native payload reconstruction has passed for both original fixtures,
including all 32 mutation controls. The first isolated Lean run ended with
exit 137 after dependency provisioning and supplied no acceptance result.
A second run progressed into the project build and was deliberately
interrupted after source inspection found that the wrong-type control
needed an explicit `StrictSystem` import. That import was added so the
isolated exclusion check would test the intended type mismatch. Neither
incomplete run is credited as theorem acceptance; a fresh complete run
at the corrected revision was required.

The [nonterminal checkpoint](../evidence/c4-named-strict-exclusion-2026-11-13/pending/README.md)
preserves the later source checks, native receipts, static reviews and
incomplete local execution history. A third ordinary run was deliberately
interrupted to try external compiler scheduling. The scheduled run at
`16dd825648d1a1bcdba9038e079463a9bebbaf3d` recorded 49 completed project
modules, but its execution handle became unavailable without a terminal
receipt. Its present liveness and final outcome are unknown; the retained
log prefixes supply no full-gate acceptance.

The [hosted full-library run at that same revision](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43345576693)
completed compilation of `NamedPositiveOverlap`, then failed on an
unsolved reversed-intersection goal in `NamedStrictExclusion`. The goal
was precisely `x ∈ K 1 ∧ x ∈ K 0 ↔ x ∈ K 0 ∧ x ∈ K 1`; adding
`and_comm` to the simplifier had not closed it. The independent
[archived-payload workflow](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43345576753)
failed at the same goal after native construction and graph/oracle replay
passed. Its payload bytes match the earlier development output, and all
32 oracle mutation controls were rejected. The exact failed verdicts,
logs and digest-verified downloaded artifacts are retained in the
[failed-head evidence](../evidence/c4-named-strict-exclusion-2026-11-13/failed-head16dd/README.md).
The repair invokes commutativity explicitly in all three reversed cases,
preserving the statement, roots, measure and fixture scope. Static review
had missed the original elaboration error. The corrected source required
the separate complete hosted acceptance recorded above; neither partial
module compilation nor either failed hosted run receives acceptance
credit.

### Negative controls

Two Lean counterexamples use a unit point mass on integer singleton tiles.
One makes all distinct-letter roots null while a diagonal tile intersection
has mass one. The other makes roots `01` and `02` null while the omitted
root `12` has mass one. These test why distinctness and all three roots
are required. The pre-code note described equivalent counting-measure
controls; the implemented witnesses use `Measure.dirac 0` explicitly.

The audit protocol rejects a missing exclusion declaration, a legacy
six-proof transcript, incomplete output and disallowed axioms. A separate
compiled control gives `no_strict_system` the type `True`; its isolated
type check must fail even without the older negative checks. Existing
wrong-source, wrong-root, positional-multiplicity and original-archive
identity controls remain in the complete replay.

### Non-claims / remaining gaps

This is a two-substitution specialization. It is uniform over the finite
carrier `C`, but not over arbitrary primitive irreducible Pisot
substitutions. It does not establish a universal C4 theorem, G1, pure
discrete spectrum, PSC, all-`strictPackets` archive coverage or odd-ancestry
closure. None of those is a premise of this narrower root contradiction.
All governed claim statuses remain unchanged. Independent human review
remains separate validation debt.
