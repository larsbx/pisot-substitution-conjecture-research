# PSC audit continuation — 17 November 2026

**Status:** current-source reconciliation and bounded verification work;
universal C4 and PSC remain open. No governed claim status changes.

## Snapshot and purpose

This note reconciles the saved **PSC current-state audit — 10 November
2026**, whose baseline was
[`67921a747a16b6998156f807f7f391ecfa3fcd88`](https://github.com/larsbx/pisot-substitution-conjecture-research/commit/67921a747a16b6998156f807f7f391ecfa3fcd88),
with source inspected at
[`main@2d831230c9b5a2f7b21165df6756532b3f598e37`](https://github.com/larsbx/pisot-substitution-conjecture-research/commit/2d831230c9b5a2f7b21165df6756532b3f598e37),
the merge of [#601](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/601).
The audit's historical receipts and findings retain their original scope.
This is a continuation crosswalk, not a fresh whole-estate or whole-library
formal audit.

## What has moved since the audit

| Audit item | Present source | Remaining boundary |
| --- | --- | --- |
| Construct the compact matrix-adic carrier and prove integral range reflection. | [MadicResidue and OccurrenceResidue](c4-madic-residue-2026-11-11.md) construct the compatible quotient carrier, derive integral lifting, and provide compactness and action injectivity under their explicit arithmetic hypotheses. | An arbitrary supplied tile family is not thereby authenticated as the intended substitution's prefix tiles. |
| Construct actual compact prefix tiles. | [PrefixClosure](c4-prefix-closure-2026-11-11.md) and [StablePrefixWindow](c4-stable-prefix-window-2026-11-11.md) give the general literal-prefix and contraction interfaces. [NamedPrefixCompact](c4-named-stable-chart-2026-11-11.md) instantiates compact actual tiles for `1/021/001` and `1/012/001`, retaining their different words and period-two scale. | The two named instances are not a construction for every PIP substitution. |
| Justify finite covers, scaling and positive compact overlap measure. | [Bounded history covers](c4-bounded-compact-cover-2026-11-11.md), [Haar scaling](c4-madic-haar-2026-11-11.md), [actual cut witnesses](c4-cut-prefix-embedding-2026-11-12.md), and [compact neighborhoods](c4-compact-neighborhood-2026-11-12.md) now supply substantial parts of that chain. | General finite-domain exclusion, fixed-origin lattice counting with the matched covolume, strict-cut density and positive compact overlap measure remain distinct obligations. A complete cover supplies subinvariance, not disjointness or a strict loss. |
| B′ has only a small cancellation bridge in Lean. | The subsequent [B′ formalization and November 15 acceptance update](c4-bprime-lean-2026-11-09.md) include `BPrimeCore`, `BPrimeBinding` and `BPrime`, with the corrected prefix-seeded theorem and Corollary B(i) registered. | Its termination-to-Pisot-or-Salem implication supplies no positive-Pisot productivity theorem. Native BPA refinement remains separate. |
| Seven divergent PRs require reconciliation. | Fresh GitHub metadata reports all seven merged through [`198e9540954f97e6aa16eb98e655ed16b08f4a7e`](https://github.com/larsbx/pisot-substitution-conjecture-research/commit/198e9540954f97e6aa16eb98e655ed16b08f4a7e) on November 11. | A merge record is not a fresh replay on the November 17 source tree. The old queue must not be described as still open. |

The seven resolved queue entries are
[#526](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/526),
[#510](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/510),
[#509](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/509),
[#487](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/487),
[#472](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/472),
[#459](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/459),
and [#305](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/305).
This disposition was read from current PR metadata; it is not inferred from
branch age or matching titles.

## The newer C4 frontier

| Merged work | Result and scope | What it does not close |
| --- | --- | --- |
| [#595](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/595), merge `392f5ac9`; [#596](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/596), merge `0c1bdb52` | [Zero-fibre occurrence reduction](psc-zero-fibre-coincidence-2026-11-17.md), [phase displacement](overlap-phase-displacement-2026-11-17.md), and the follow-up governance repair. Lean proves the unit-step cardinality bound from signs and connectivity; the geometric centring argument has a written proof. | Existence of a literal exit from every candidate diagonal-free support. |
| [#597](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/597), merge `e93aed96`; [#598](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/598), merge `84ca3770` | [Larger periodic-fibre bound](c4-periodic-fibre-bound-2026-11-17.md) and [ordinary/exchanged overlap returns](c4-periodic-overlap-returns-2026-11-17.md), with literal occurrence controls. The strict joining interpretation preserves its unit rank-two hypotheses. | The neutral unit-weight sector and its literal compatibility obstruction. |
| [#599](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/599), merge `5498aac2` | [FC2 orientation transfer](c4-fc2-orientation-2026-11-17.md) removes the need for a separately supplied reversed integer rank. | One geometric realization of coincidence rank is still needed; integer orientation equality does not establish rank one. |
| [#600](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/600), merge `bee02301` | [Round four](c4-round4-2026-11-17.md) records failures of degree-two sign laws, a conditional covering obstruction, and elementary (F) lemmas in Lean. | A universal positivity law or universal noncovering assertion. Unreplayable scratch observations remain labelled as such. |
| [#601](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/601), merge `2d831230` | [One-track seam spectrum](c4-one-track-seam-spectrum-2026-11-17.md) computes the cyclotomic correction from legal seam and endpoint cycles, conditional on the strict-carrier identification. | Uniform exclusion of the required corrected odd multiplicity. Every tested PIP3 control has no aligned nonproductive sink. |

The previously unlocated commit `6e2149caf8bd2238f189593479ecb99dee04eb00`
is now published in rebased form as
[`57d5862671c9bdfec780fbdbe71d0f7ab257be60`](https://github.com/larsbx/pisot-substitution-conjecture-research/commit/57d5862671c9bdfec780fbdbe71d0f7ab257be60),
as that commit's message records. Its seam correction is already in #601;
it is not an outstanding implementation task.

## Chosen continuation

The immediate verification target is an independent replay of **literal
periodic seam identities**, beyond the existing product-count comparison.
The baseline regression multiplies the number of periodic interior states
by fixed endpoint-letter or legal-seam counts. Agreement of those totals
alone cannot detect every substituted occurrence identity.

The continuation scans actual iterated words, retains each self-occurrence's
position and full prefix Parikh vector, and checks the integral equation
`(M^n - I)v = prefix`. It then compares individual endpoint germs and adjacent
cell pairs with the saturated overlap graph. Arithmetic rejection or an
exhausted word budget produces no verdict. The [completed bounded
replay](c4-literal-seam-replay-2026-11-17.md) passes all 48 declared
specimen/power comparisons and fourteen mutation or input-refusal checks.
Its [evidence packet](../evidence/literal-seam-replay-2026-11-17/README.md)
records source hashes, local commands and results separately from hosted CI.

This is an evidence improvement for the existing conditional correction.
It does not produce a strict PIP3 component. The productive `01/12/021`
control already has correction `+1` at `-1`, so the seam contribution cannot
be discarded by assuming universal nonpositivity.

The next uniform mathematical statement remains: for every eligible
literal rank-two sink, its corrected swap-odd multiplicity at
`epsilon = (det M)^m` is smaller than the rank required by a nonzero neutral
first-defect image of weight `(m,m,m)`, or another literal constraint excludes
that sink. The [side-notes ledger](side-notes-ledger.md) records why abstract
child matrices and the tested degree-two sign laws do not supply this step.

The shorter universal seed route still requires A1′
([#138](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/138))
and BH
([#139](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/139))
to establish
[#84](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/84).
Supplied-component C4
([#461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461)),
global G1, Concentration and PSC retain their recorded open scopes.

## Verification boundaries

The source review distinguishes implemented declarations, their recorded
historical acceptance, and fresh execution. It does not credit a previous
green head as a new whole-library Lean run.

At the initial November 17 inspection, the connector's first page for #601
head `f5e2aab7d434f24dcbe618d4948984daa1e1a123` returned 31 queued
PR-triggered workflow executions, including
[PSC research checks](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/44161849759).
That is a bounded observation of the PR head, not a complete workflow
inventory or acceptance of merge commit `2d831230`. Any subsequent results
need their own dated observation.

The November 10 finding about absent required-check enforcement on `main`
has not been reverified here. No repository settings are changed by this
continuation. Independent human review remains final validation debt;
missing hypotheses and missing execution receipts remain substantive gaps.
