# Lean roadmap: the literal C4 family's dynamical theorem

**Status:** planning only. No Lean, Mojo or governed claim changes. The family statement
remains: *family criterion inputs proved in Lean; spectral conclusion obtained by a published
theorem.* C4 and PSC remain open. Independent human review is pending on every cited module.

Starting revision: `main@c4cc728` (through #644). The family is

\[
\sigma_k(0)=1,\qquad \sigma_k(1)=0\,1^k\,2,\qquad \sigma_k(2)=001,
\]

with arithmetic endpoint `Psc.ParameterFamilyBridge.spectral_criterion_inputs`
(premises: `k`, `2 ≤ k`) and external application in the
[spectral-closure note](c4-family-spectral-closure-2026-11-14.md), §3. This note refines the
family ordering of the [live roadmap](research-roadmap-2026-09-21.md) and the
[research review](psc-sigma-k-research-review-2026-11-20.md), §11; it does not replace them.

**Rebase note.** The first draft was written against `8bbc05b`. Main then merged the
[family hull](c4-family-tiling-2026-11-21.md) (#639) and the
[legal-patch transfer](c4-family-legal-coincidence-2026-11-21.md) (#641), which complete
most of F1 and several items of F2 below. Completed items are kept and marked, with their
declarations, so the remaining order stays readable.

## Finite-automaton continuation after `main@bbe0640d`

The [finite-fibre continuation](c4-finite-fibre-obligations-2026-11-21.md)
advances F4(c): universal zero-fibre witnesses now feed ordinary
proximality, nonproximal fibre rank one and intrinsic maximal-factor
descent. Finite synchronization and a positive origin-displacement gap
give a nonempty open set of fibres with a common positive window.
Explicit full-history characters give continuous eigenfunctions and
dense continuous span on the solenoid. Haar preservation/inflation
ergodicity, almost-everywhere singleton fibres, and the invariant-measure
`L2` endpoint remain to be proved. These current endpoints supersede the
open F4(c) entries in the historical table below. The top-level family
spectral status remains partly external; the separate symbolic transfer
also remains open.

## Historical status at `main@fbaa2ef` (through #647)

Main moved again after the rebase note above: the
[solenoid factor](c4-family-solenoid-factor-2026-11-21.md) (#643/#646), the
[zero-fibre interface](c4-zero-fibre-spectral-interface-2026-11-21.md) and the
[finite tile-chain automaton](c4-finite-tile-automaton-2026-11-21.md) (#647). Where the
sections below disagree with this table, the table is current; the sections are kept as
the record of the order that was proposed. Names are in `Psc.ParameterFamilySolenoid`
unless qualified, read from source and not rebuilt here.

| Stage | Status | Declarations, or what remains |
| --- | --- | --- |
| F1 | **done**, `k ≥ 1` | `mat_eq`, `charpoly_map`, `spectral : SpectralPisot (geometry k hk)`, `pisotData` |
| F2 compact | done | `localHull_compactSpace` (`PeriodicPartnerRealizationOnto`), from `isCompact_origin_fibre` and `totallyBounded_origin_fibre`, by the transversal route |
| F2 recognizability | done, `k ≥ 1` | `inflateH_bijective`, proved from the literal markers; `continuous_desub` |
| F2 Hausdorff, packaged action laws | not located as named instances | state `T2Space (LocalHull S)` and the action structure, or record where they are implied |
| F3 | open, unchanged | one `FullFactorCriterion` structure consumed by the final theorem |
| F4(a) | **done**, `k ≥ 1` | `continuous_solenoidRealize`, `solenoidRealize_surjective`, `solenoidRealize_finite_fibres`, `solenoidRealize_translate`, `solenoidRealize_inflate` |
| F4(b) | partly | `denseRange_translate`; uniqueness of the invariant measure on the target is not stated |
| F4(c) | open | the four interfaces of the zero-fibre note: witnesses for *every* pair over zero (`k ≥ 2`), propagation to coincidence rank one, rank one to a.e. singleton fibres, and the `L²` endpoint. `common_tile_of_zero_fibre_witnesses` and `exactProximal_of_periodic_common_tile` consume the witnesses and do not construct them |
| F4(d) | open | no measure, Koopman representation or `PureDiscrete` definition yet |
| F5 | open, unchanged | separate tiling and symbolic theorems with a visible transfer |

The continuity problem of §0 is closed: `continuous_realizeLocal` holds from bijective
inflation and `PisotData`, by exactly the two ingredients listed there
(`continuous_desub`, `isLocallyConstant_cs_of_continuous_desub`, uniform convergence of the
series). Main's working method for F4(c) is the finite-kernel automaton route, and the
[live roadmap](research-roadmap-2026-09-21.md) owns that ordering. What this note still
adds is F3, the F4(d) definitions and the F5 separation. The status sentence at the top is
unchanged: no coincidence-rank or invariant-measure conclusion is in Lean.

## 0. Baseline, with two stale descriptions corrected

Declaration names below were read from the sources at the starting revision; nothing was
rebuilt for this note. `PT` abbreviates `Psc.ParameterFamilyTiling`.

| Topic | Stale description | Baseline at `8bbc05b` | Still open |
| --- | --- | --- | --- |
| Stable contraction | "`PisotData` is an assumed analytic input" | Derived: `SpectralPisot.toPisotData` from `χ_M = (X − β)Q`, `Q(β) ≠ 0`, roots of `Q` in the open unit disc; `SpectralPisot.ofIrreducible` produces that from an irreducible rational `χ_M` and the root condition ([contraction note](c4-pisot-contraction-2026-11-19.md)). | `SpectralPisot (PT.geometry k hk)` is not yet stated. The length-≤3 census certificate does not cover `σ_k`, `k ≥ 2`. |
| Source continuity | "hull continuity is open" | `LocalHull S` carries the ordinary topology; `continuous_translate` (joint in `(t, T)`), `continuous_inflate`, `isOpenQuotientMap_chart`, `nhds_patch_basis` ([ordinary-hull note](c4-ordinary-hull-topology-2026-11-19.md)). | Continuity of the *constructed* `realize`: `continuous_realizeLocal_iff` reduces it to the exact presentation, and neither side is proved. |
| Family hull | "the family has no geometric object in Lean" | `PT.geometry`, `fixed_hull_tiling`, `aperiodic`, `finite_local_complexity`, `continuous_action` for `k ≥ 1`; `hull_dense_eventual`, `periodic_fibre_common_tiles` for `k ≥ 2`. | Compactness, Hausdorffness, recognizability, the factor map and its fibres. |
| Target | — | `solenoid_compactSpace`, `solenoid_t2Space`, `shiftHomeomorph`, `continuous_flow` ([realization note](c4-geometric-realization-2026-11-19.md)). | Surjectivity, finite fibres, identification with BBK's map. |

The remaining continuity problem is specific. `realize T = ([G(Tₙ)])ₙ`, where `Tₙ` is the
`n`-th desubstitution and `G` is a series in the prefix counts `cₙ` of the origin tile at each
level. Continuity therefore needs (i) each `T ↦ Tₙ` continuous, i.e. inverse inflation
continuous, which bare `Bijective inflateH` does not give, and (ii) local constancy of
`(c₀, …, c_N)` up to the small-translation direction, with the tail controlled uniformly by
`C · offsetBound · ρⁿ`.

Not in Lean for any substitution: compactness or Hausdorffness of `LocalHull`,
recognizability, an invariant measure, a Koopman representation.
The pinned Mathlib has `MeasurePreserving` and `Ergodic` and no Koopman file.

## 1. Order of work

Each stage is theorem-facing, so each needs its own short stop/go note before code
(AGENTS.md). Sources named below from memory are marked †; they are to be re-read at that
stage and are not relied on here.

### F1. The literal family as a `LengthSubst` — done except the contraction

Done (#639): `PT.expansion`, `PT.geometry k hk : LengthSubst (Fin 3)` with
`σ = substitution k`, `ℓ = (β, β², β + 2)`, `expansion_gt_one`, `expansion_pisot`, for
`1 ≤ k`.

Remaining: `SpectralPisot (PT.geometry k hk)`, hence `PisotData`, through
`SpectralPisot.ofIrreducible`. This needs `mat (geometry k hk)` identified with the cast of
`inc (substitution k)` so that `ParameterFamilyPisot.irreducible` and `expansion_pisot`
apply to its characteristic polynomial. No new contraction assumption. Control:
`zero_no_root_above_two` (`k = 0`).

### F2. The legal hull and its properties

`PT.TilingSpace k hk` is `LocalHull (PT.geometry k hk)`.

| Item | Status | Declarations or gap |
| --- | --- | --- |
| nonempty | done, `k ≥ 1` | `fixed_hull_tiling` (seam `1.1`, fixed by squared inflation), `tiling_space_nonempty` |
| finite local complexity | done, generic | `LengthSubst.finite_local_complexity`; family form `PT.finite_local_complexity` |
| nonperiodic | done, `k ≥ 1` | `aperiodic`, `action_aperiodic`, through `aperiodic_of_inflate_fixed` and `window_occurs` |
| joint continuity | done | `continuous_action` |
| action laws | open, small | `translate 0 = id` on `LocalHull`; package with `translate_translate` and `inflate ∘ translate t = translate (β t) ∘ inflate` |
| compact | open | `S.Hull` with the exact metric is not compact. Go through the transversal `Ξ` of tilings with a tile starting at 0: totally bounded by FLC, complete because `Legal` and `IsTiling` are patchwise; then `LocalHull = chart '' ([0, max ℓ] × Ξ)` |
| Hausdorff | open | separate distinct tilings by patch neighbourhoods; `small_translate_eq_zero_of_agree` supplies the local rigidity |
| recognizability | open, only where F4 needs it | `Injective inflateH` and `Surjective inflateH` as separate facts. With a compact Hausdorff source the continuous bijection is a homeomorphism, so compactness pays for continuity of inverse inflation. Solomyak's unique-composition theorem is the candidate named in the review; aperiodicity and FLC, its standing hypotheses, are now in Lean |

Compactness and Hausdorffness are substitution-generic and should be stated for every
`LengthSubst` with a finite alphabet. The `a ↦ aa` boundary example (periodic, inflation not
injective) should be formalized as the negative control for recognizability.

### F3. One criterion definition

Target: a single structure over actual substituted words, replacing the unbundled conjunction
in `spectral_criterion_inputs`.

```lean
structure FullFactorCriterion (s : α → List α) (T : List α × List α) : Prop where
  finite     : {U | ∃ n, U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2)}.Finite
  productive : ∀ U, (∃ n, U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2)) →
                 ∃ m a, ([a], [a]) ∈ red ((subst s)^[m] U.1) ((subst s)^[m] U.2)
```

`TerminationFactors.terminates_iff_finite_factors_and_coincidences` already gives
`TerminatesWithCoincidence s T ↔ FullFactorCriterion s T` for irreducible balanced `T`, and
`full_factor_termination` gives the family instance at `([0,1],[1,0])`, `2 ≤ k`. The two
fields stay separate: `identity_finite_without_coincidence` refutes dropping `productive`, and
the non-Pisot productive-but-infinite control refutes dropping `finite`.
`full_factor_need_not_be_terminal_reachable` stays as the guard on the factor set. The
definition must be the one F4 consumes; no second criterion predicate.

### F4. The spectral implication

Definitions to fix first, for a compact Hausdorff `X` with continuous `ℝ`-action `φ`:

- measure: any `φ`-invariant Borel probability `μ` on `X`;
- Koopman representation: `U_t f = f ∘ φ_t` on `L²(μ; ℂ)`, built locally from
  measure-preserving composition;
- `PureDiscrete φ μ`: the closed span of `{f | ∃ λ : ℝ, ∀ t, U_t f = e^{2πiλt} f}` is `⊤`.

Decomposition, with the criterion entering only at (c):

| Step | Statement | Uses |
| --- | --- | --- |
| (a) | `realizeLocal` is continuous, equivariant and onto the solenoid | F2 compactness and recognizability, `PisotData`, §0 (i)–(ii) |
| (b) | the solenoid flow `z ↦ z + [tβ⁻ⁿu]` is a minimal translation flow on a compact abelian group; its only invariant probability is Haar | irreducibility of `χ_M` |
| (c) | `FullFactorCriterion` at one unequal-letter seed ⇒ the set of solenoid points with more than one preimage is Haar-null | Barge–Štimac–Williams, Cor. 2 |
| (d) | an equivariant, measure-preserving, a.e.-injective map onto a compact abelian translation flow gives `PureDiscrete` | characters separate points; Stone–Weierstrass |

Already available for (c), for `k ≥ 2`: `hull_dense_eventual` (dense eventual coincidence
for hull tilings sharing a tile) and `periodic_fibre_common_tiles`, which gives one nonempty
fibre with pairwise common tiles from four premises: injective inflation, semiconjugacy,
finite fibres and same-fibre closed-origin witnesses. The first comes from F2, the second
from (a). Finite fibres and the witnesses are the two premises still to discharge, and the
step from one such fibre to a Haar-null multi-preimage set (coincidence rank one) is not yet
stated. So non-claim 3 below is superseded on finite fibres: they are on this path.

If (b) holds, every invariant `μ` pushes forward to Haar and the conclusion can quantify over
all invariant `μ`, which avoids proving unique ergodicity of the hull. That design choice is
unverified and is the first question for this stage's stop/go. (c) is the mathematical core
and the largest formalization; (d) is generic and can be developed in parallel with F1–F3.
Until (a)–(d) are all checked the status sentence at the top stands unchanged.

### F5. Symbolic and tiling conclusions, separately

Two theorems, never one:

- `family_tiling_pureDiscrete`: the `ℝ`-action on `LocalHull (PT.geometry k hk)`;
- `family_shift_pureDiscrete`: the `ℤ`-shift on the two-sided subshift of `σ_k`.

The tiling flow is the suspension of the shift under the roof `x ↦ ℓ(x₀)`, which is not
constant since `β, β², β + 2` are distinct. The transfer splits into a constant-roof step
(suspension under roof `1` ↔ shift, elementary) and a change of tile lengths `ℓ → 1`, which is
the genuine step. The expected visible hypothesis is contraction on the complement of the
Perron direction, which `SpectralPisot` supplies (Clark–Sadun†). The transfer theorem carries
that hypothesis in its statement.

## 2. End-to-end target

```lean
theorem family_tiling_pureDiscrete (k : ℕ) (hk : 2 ≤ k) :
    ∀ μ, IsProbabilityMeasure μ → Invariant (translate (PT.geometry k _)) μ →
      PureDiscrete (translate (PT.geometry k _)) μ
```

No finiteness, coincidence, root, recognizability or spectral premise is supplied by the
caller. The request's quantifier symbol was lost in transit; it is read here as `k`. The Lean
termination proof needs `2 ≤ k` (`terminates_with_coincidence`), so `k = 1` is either a
separate finite certificate or stays external through the cubic trace-at-most-two theorem.

Remaining order: F1 contraction; F2 compact → Hausdorff → recognizability → F4(a); F3 →
F4(c); F4 → F5. Compactness, Hausdorffness, the action laws and F4(d) have no family
dependency and can start immediately.

## 3. Non-claims

1. Nothing here is proved; the signatures are targets and may change at each stop/go.
2. No universal PIP3 statement: every stage is for `σ_k` or for a generic `LengthSubst`, and
   F4(c) is the family's criterion, not a strict-system exclusion.
3. Finite fibres are on this path through `periodic_fibre_common_tiles`. BDS periodicization
   and the BBK identification are not, unless the finite-fibre proof turns out to need the
   latter; if so that is recorded at the stage's stop/go.
4. Lean is the deductive layer here. No executable census or certificate is planned, so no
   Mojo module is owed; if a stage adds a finite computation it goes to `kernel/` first.
