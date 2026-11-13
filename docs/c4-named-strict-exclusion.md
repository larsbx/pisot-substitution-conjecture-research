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

Acceptance status at source construction: **pending**. Terminal results,
exact source identities and preserved failed attempts will be recorded in
the PR evidence before any acceptance statement is made.

The native payload reconstruction has passed for both original fixtures,
including all 32 mutation controls. The first isolated Lean run ended with
exit 137 after dependency provisioning and supplied no acceptance result.
A second run progressed into the project build and was deliberately
interrupted after source inspection found that the wrong-type control
needed an explicit `StrictSystem` import. That import is now present, so
the isolated exclusion check can test the intended type mismatch. Neither
incomplete run is credited as theorem acceptance; a fresh complete run
at the corrected revision is required.

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
