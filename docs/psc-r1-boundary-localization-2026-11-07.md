# R1F boundary localization and productive-source adversarial control — 2026-11-07

**Scope:** R1 and integrated R1F branch `research/bprime-r1-ancestry-rigidity-20261107`. Baseline source/head: `f1f230de71882d1f9b9330d003950b45c3570e6a`. Proof-first research only; no universal PSC, C4, BH, A1′, or geometric claim promotion.

## Work shown

### Assumptions and hypotheses

Let `label : A → V` take literal source letters into an additive group and let a sequence of ordered child pairs be individually balanced in word mass. An irreducible child has no strict interior index with equal top/bottom Parikh prefixes. This is the **same-child** hypothesis. The exact source ancestry may be asynchronous and may cross many balanced child boundaries; a germ whose within-image correction is valid is **not** thereby a globally source-realizable strict SCC.

### Derivation / reduction

The new Lean `R1Source.lean` theorems `balanced_child_list_mass`, `balanced_child_prefix_cancel`, and `irreducible_child_rules_out_internal_aligned_return` prove, over *any* additive mass group, that concatenating balanced ordered child pairs gives balanced total mass and that a zero-return cut after any already balanced prefix, **strictly inside** the next irreducible child, would contradict that child's irreducibility. This localizes the possible aligned balanced returns of a genuine irreducible factorization to child boundaries, provided the source-interval location is certified; it does **not** identify which child contains an arbitrary desubstituted asynchronous germ.

The separate universal `unit_source_defect_forces_aligned_interior_return` theorem explains the most useful local configuration: top source prefix one letter longer than bottom, source Parikh difference equal to the next bottom letter's mass, and both source-parent words equal in total length. The bottom catches up at a proper aligned balanced cut. The factorization-boundary lemma is essential before using this conditional impossibility against any alleged strict recurrent component.

### Evidence and replay

- `proof/psc_routes/R1Source.lean`: 16 scoped declarations, individually named in the fail-closed axiom audit.
- `proof/quint/PscR1Source.qnt`: two deterministic literal-word tests, including `001/010` reducible and `001/100` irreducible.
- `proof/quint/PscR1ChildBoundary.qnt`: three new deterministic assertions for two irreducible balanced child pairs `01|01 / 10|10`. The only intermediate balanced return lies exactly at the shared child boundary, not at indices 1 or 3. The exact-head workflow `.github/workflows/psc-bprime-r1-source.yml` requires **16** Lean axiom receipts and both Quint modules to execute nonempty tests.
- `proof/psc_routes/R1OrderedAncestry.lean` and `proof/quint/PscR1OrderedAncestry.qnt`: two additional literal-source productivity controls (6 named Lean declarations, 4 Quint deterministic tests). Exact first inflation of the seed `01/10` yields `0102/0201` with matching letters at indices 0 and 2. Therefore the **nine** depth-six ancestry cycles recorded for this seed come from a *productive* source, and may not be counted as witnesses for a **strict nonproductive child-closed SCC**. This is a classification of the observed finite candidate provenance, not exclusion of arbitrary legal recurrent strict components.
- `proof/quint/PscR1.qnt`: the concrete three-step Tribonacci matrix control was renamed to `threeStepActualMatrixCycleTest` and `.github/workflows/psc-bprime-r1.yml` now checks nonempty test output. This repairs a Codex P1 finding where `quint test` silently selected no tests because the original name lacked `Test`.

The current revision requires **fresh exact-head** Lean, Quint and canonical Mojo-versus-Lean occurrence-packet receipts. No previous commit's green workflow is acceptance for these new declarations.

### Negative controls

1. Genuine, locally admissible Tribonacci proper cut-germ three-cycle survives next-letter and offset checks; it can cross derived-child boundaries and is **not** automatically a valid strict SCC.
2. An irreducible balanced child has no aligned internal return, but a concatenation of irreducible balanced children has return boundaries, as the `01|01 / 10|10` Quint case explicitly demonstrates. A balanced boundary is **not** itself a diagonal letter coincidence.
3. The literal swap seed `01/10` producing the depth-six nine ancestry cycles is already *productive* after one inflation. Do not use that finite sample to contradict or establish existence of a strict recurrent system.
4. Quint default test selection without a `Test` suffix can produce an empty passing invocation. Every deterministic test requires a positive executed-count gate.

### Non-claims / remaining gaps

The user’s proof-driven development framework remains: Lean and Quint first, independent exact replay and negative controls before a canonical Mojo enumeration extension; no human review as a research-progress blocker. The open **mathematical** bridge is an all-source statement: a recurrent strict child-closed occurrence ancestry must either yield an interior return *within one irreducible child* or a sufficiently strong synchronizing event at a derived-child boundary. A return at a boundary alone is insufficient, and a finite experimental search bounded to the productive swap seed cannot supply the universal quantifier.

**Merge state:** nested PR #512 was merged into parent R1 #507 at commit `a5f04144b3d2d5a358e21e2881c1a53490a4b228` on 2026-11-07, but PR #507 remains open against main. This note does not authorize any additional merge. Integrations require fresh revision-bound acceptance.

## Prior-art and claim boundary correction — 2026-11-07

The underlying **mathematical** fact that a complete irreducible balanced-pair factorization has no extra aligned balanced cuts inside its children is already part of this repository's [derived-factorization theorem](c4-derived-cut-address.md), §2–§3. Its distinction between inherited and newborn cuts also predates R1F. The [bilateral newborn rigidity theorem](c4-bilateral-birth-rigidity-2026-11-02.md), §2–§3, already proves that a newborn interior zero-return boundary in an irreducible pair cannot be aligned to source-image letter boundaries on **both** tracks, assuming injective incidence. R1F therefore contributes a **Lean-compiled proof interface** and adversarial controls for the more specific unit source-defect/next-letter configuration, not a newly discovered global decomposition theorem.

The repository's [ordered-word completion contract](c4-ordered-word-completion-interface-2026-11-02.md) demands a *one-step interior newborn* in `Sync_+` or `Sync_-` from a supplied complete strict child-closed SCC. The R1F boundary localization by itself does not supply that synchronization. In addition, the [legal ancestry tower theorem](c4-legal-ancestry-towers.md) already supplies long legal contexts under its strict-component hypotheses; repeatedly proving legality rather than the hierarchy/ordered-occurrence interaction is not the closure bottleneck.

**Proceed narrowed:** the next genuinely load-bearing theorem must bind recurrence to the **same actual ordered child**, preserve raw sign and indexed occurrence addresses, and obtain synchronization or a rigorously incompatible recognized hierarchy. Do not use the productive `01/10` swap-seed's finite ancestry cycles as negative strict-SCC evidence. A queued or parent-head green CI run is not sufficient for the new source and occurrence Lean theorems.

## Physical-length boundary certificate correction — 2026-11-07

A mass equality for arbitrary additive letter labels is **not by itself** an equal physical word-length statement. Accordingly the Lean source module now separately proves `equal_length_child_list`, assuming that each actual child pair has equal physical top/bottom word length, and `balanced_children_canonical_boundary`, which combines length equality **and** Parikh/mass equality across all completed children. This is required before classifying a cut as an aligned physical zero return of a complete irreducible factorization.

The new scope has **18** `R1Source` theorem declarations, all listed in the exact-declaration axiom inventory; the related CI gate now checks **18** kernel receipts. Across this R1 branch there are **70** scoped Lean theorem declarations (13 R1 + 19 modular + 14 Smith + 18 source + 6 ordered ancestry) and **35** explicitly named deterministic Quint tests, including the earlier silently skipped Tribonacci cycle now properly selected and checked. These are *source inventories*, not accepted verification counts; new exact-head CI remains pending.

The mathematical decomposition statement already appears in `docs/c4-derived-cut-address.md`; the contribution here is an explicit Lean/Quint refinement interface and adversarial classifications. Universal C4/BH/PSC, including the newborn `Sync_±` obligation and occurrence-compatible strict-component coverage, remain open.

## Raw orientation-cocycle robustness correction — 2026-11-07

The normalized balanced-pair state may be realized as `(u,v)` or `(v,u)` along different occurrence edges, with the sign carried by the existing `Z/2` orientation cocycle. A proof that excludes an internal zero return only in one arbitrarily selected orientation would not bind the actual child factorization.

The Lean `noAlignedInteriorReturn_swap` theorem now proves, **with an explicit equal-length hypothesis**, that a no-interior-return property survives exchange of raw top and bottom words. This means the preceding balanced-prefix cancellation and irreducible-child localization remain applicable to either raw orientation, without assuming a global trivial gauge. Quint independently tests both raw orientations of `01|01 / 10|10`; both exhibit the shared balanced child boundary at index 2 and neither has an aligned return strictly inside a child at indices 1 or 3.

The new source module therefore has **19** Lean theorem declarations (18 before this correction); the exact-head workflow now requires 19 named axiom receipts and **eight** deterministic Quint tests: two legal-word controls, three normal-orientation child-boundary cases and three raw-swapped controls. The R1 branch total is **71** scoped Lean declarations and **38** named deterministic Quint tests across six model files. These are source counts pending exact-revision hosted acceptance, not acceptance receipts.

**Unproved interaction:** For a hypothetical *strict* PIP child-closed SCC, show that a repeated legal source/derived address with a unit defect must be localizable inside one irreducible child, or creates a specifically synchronizing one-step newborn `Sync_+`/`Sync_-` boundary. The previously proved signed orientation cocycle ensures raw order is tracked; it does not itself imply this dichotomy.

## Correction to productive-source classification — 2026-11-07

**The earlier inference from root productivity to descendant classification was too strong.** Productivity means existence of a path to a diagonal; it propagates backward to ancestors, not forward to every child. The root's productivity alone therefore does not prove that the nine recorded Tribonacci ancestry loops avoid all strict nonproductive descendant components. The safe statement is only that the root itself is not a strict nonproductive state and that the existing finite data do not yet certify such a component. A separate, complete occurrence-support/SCC-specific argument is required.

A literal, source-legal control now records the precise failure: for `0->01,1->10`, the irreducible balanced pair `001/100` has the complete child row `(01/10), (0/0), (1/1), (10/01)`. Thus it is productive, while its two oriented noncoincident children form a strict closed recurrent class, with child rows `(01/10)->(01/10),(10/01)` and `(10/01)->(10/01),(01/10)`. Both root words occur in the same third iterate `01101001`. The incidence polynomial `x(x-2)` is reducible: this refutes an unrestricted source/graph shortcut, **not PSC**.

This dated correction preserves the historical text above and corrects the side-notes-ledger entry whose evidence locator is this document. Full derivation, fifteen staged Lean theorems, six named Quint controls, prior-art stop/go and exact-head acceptance gates are in [the productivity-scope correction](psc-r1-productivity-scope-2026-11-07.md). The new sources have not yet earned hosted Lean/Quint acceptance. No existing universal claim is promoted, and none of the nine Tribonacci loops is newly classified as strict or nonstrict by this control.
