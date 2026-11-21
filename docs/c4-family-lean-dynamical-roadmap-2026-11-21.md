# Lean roadmap: the literal C4 family's dynamical theorem

**Status:** planning only. No Lean, Mojo or governed claim changes. The family statement
remains: *family criterion inputs proved in Lean; spectral conclusion obtained by a published
theorem.* C4 and PSC remain open. Independent human review is pending on every cited module.

Starting revision: `main@8bbc05b`. The family is

\[
\sigma_k(0)=1,\qquad \sigma_k(1)=0\,1^k\,2,\qquad \sigma_k(2)=001,
\]

with current Lean endpoint `Psc.ParameterFamilyBridge.spectral_criterion_inputs`
(premises: `k`, `2 ≤ k`) and external application in the
[spectral-closure note](c4-family-spectral-closure-2026-11-14.md), §3.

## 0. Baseline, with two stale descriptions corrected

Declaration names below were read from the sources at the starting revision; nothing was
rebuilt for this note.

| Topic | Stale description | Baseline at `8bbc05b` | Still open |
| --- | --- | --- | --- |
| Stable contraction | "`PisotData` is an assumed analytic input" | Derived: `SpectralPisot.toPisotData` from `χ_M = (X − β)Q`, `Q(β) ≠ 0`, roots of `Q` in the open unit disc; `SpectralPisot.ofIrreducible` produces that from an irreducible rational `χ_M` and the root condition ([contraction note](c4-pisot-contraction-2026-11-19.md)). | Instantiation for `σ_k`. The length-≤3 census certificate does not cover `σ_k`, `k ≥ 2`. |
| Source continuity | "hull continuity is open" | `LocalHull S` carries the ordinary topology; `continuous_translate` (joint in `(t, T)`), `continuous_inflate`, `isOpenQuotientMap_chart`, `nhds_patch_basis` ([ordinary-hull note](c4-ordinary-hull-topology-2026-11-19.md)). | Continuity of the *constructed* `realize`: `continuous_realizeLocal_iff` reduces it to the exact presentation, and neither side is proved. |
| Target | — | `solenoid_compactSpace`, `solenoid_t2Space`, `shiftHomeomorph`, `continuous_flow` ([realization note](c4-geometric-realization-2026-11-19.md)). | Surjectivity, finite fibres, identification with BBK's map. |

The remaining continuity problem is specific. `realize T = ([G(Tₙ)])ₙ`, where `Tₙ` is the
`n`-th desubstitution and `G` is a series in the prefix counts `cₙ` of the origin tile at each
level. Continuity therefore needs (i) each `T ↦ Tₙ` continuous, i.e. inverse inflation
continuous, which bare `Bijective inflateH` does not give, and (ii) local constancy of
`(c₀, …, c_N)` up to the small-translation direction, with the tail controlled uniformly by
`C · offsetBound · ρⁿ`.

Not in Lean for any substitution: compactness or Hausdorffness of `LocalHull`, finite local
complexity, nonperiodicity, recognizability, an invariant measure, a Koopman representation.
The pinned Mathlib has `MeasurePreserving` and `Ergodic` and no Koopman file.

## 1. Order of work

Each stage is theorem-facing, so each needs its own short stop/go note before code
(AGENTS.md). Sources named below from memory are marked †; they are to be re-read at that
stage and are not relied on here.

### F1. The literal family as a `LengthSubst`

Target: `familySubst (k) (hk : 1 ≤ k) : LengthSubst (Fin 3)` with
`σ = ParameterFamilyRows.substitution k`, `ℓ = (β, β², β + 2)`, and
`familySpectral k hk : SpectralPisot (familySubst k hk)`, hence `PisotData`.

| Obligation | Available | Gap |
| --- | --- | --- |
| a definite `β` | `ParameterFamilyPisot.real_root`, `pisot` (existential) | choose it, or prove uniqueness of the real root above `2` from `other_root` |
| `ne_nil`, `ℓ_pos`, `1 < β` | `2 < β` | immediate |
| `eigen`: `Σ ℓ(σ a) = β ℓ a` | `positive_left_eigenvector` (`w ᵥ* M = β w`, source letters index columns) | unfold `vecMul` against image words |
| `mat S` is the cast of `inc (substitution k)` | `incidence_eq` | bind the two matrix presentations once |
| `SpectralPisot` | `irreducible`, `pisot`, `SpectralPisot.ofIrreducible` | transport `χ` along the cast |

Control: `zero_no_root_above_two` (`k = 0`). Exit: `PisotData (familySubst k hk)` with only
`k`, `1 ≤ k` as premises.

### F2. The legal hull and its properties

All statements are on `LocalHull (familySubst k hk)` unless stated.

1. **Nonempty.** `hull_nonempty_of_seed` needs a legal two-tile seed fixed by a power of
   inflation; exhibit one for `σ_k`.
2. **Finite local complexity.** For each `R`, finitely many patches on `(−R, R)` up to
   translation. Uses only `Fintype α` and `min ℓ > 0`; state it for every `LengthSubst`.
3. **Compact.** `S.Hull` with the exact metric is not compact, so go through the transversal
   `Ξ = {T | a tile starts at 0}`: `Ξ` is totally bounded by FLC and complete because `Legal`
   and `IsTiling` are patchwise; then `LocalHull = chart '' ([0, max ℓ] × Ξ)`.
4. **Hausdorff.** Separate distinct tilings by patch neighbourhoods;
   `small_translate_eq_zero_of_agree` supplies the local rigidity.
5. **Action laws.** Have `translate_translate`, `inflateH_translate`, joint continuity. Add
   `translate 0 = id` and package as a continuous `ℝ`-action with `inflate ∘ translate t =
   translate (β t) ∘ inflate`.
6. **Nonperiodic.** `translate t T = T → t = 0`. The written argument uses minimality and
   letter frequencies with `root_irrational`. Decide at stop/go between formalizing that and
   deriving it from recognizability.
7. **Recognizability**, only where F4's route needs it: `Injective inflateH` and
   `Surjective inflateH` as separate facts, then inverse inflation continuous (compact
   Hausdorff source makes a continuous bijection a homeomorphism, so item 3 pays for this).
   General Mossé/Solomyak† is large; a family-specific marker argument is the alternative.

Items 2–5 are substitution-generic and independent of F1. Controls: the existing
`a ↦ aa` boundary example (periodic, inflation not injective) should be formalized here as
the negative control for 6 and 7.

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
| (a) | `realizeLocal` is continuous, equivariant and onto the solenoid | F2.3, F2.7, `PisotData`, §0 (i)–(ii) |
| (b) | the solenoid flow `z ↦ z + [tβ⁻ⁿu]` is a minimal translation flow on a compact abelian group; its only invariant probability is Haar | irreducibility of `χ_M` |
| (c) | `FullFactorCriterion` at one unequal-letter seed ⇒ the set of solenoid points with more than one preimage is Haar-null | Barge–Štimac–Williams, Cor. 2 |
| (d) | an equivariant, measure-preserving, a.e.-injective map onto a compact abelian translation flow gives `PureDiscrete` | characters separate points; Stone–Weierstrass |

If (b) holds, every invariant `μ` pushes forward to Haar and the conclusion can quantify over
all invariant `μ`, which avoids proving unique ergodicity of the hull. That design choice is
unverified and is the first question for this stage's stop/go. (c) is the mathematical core
and the largest formalization; (d) is generic and can be developed in parallel with F1–F3.
Until (a)–(d) are all checked the status sentence at the top stands unchanged.

### F5. Symbolic and tiling conclusions, separately

Two theorems, never one:

- `family_tiling_pureDiscrete`: the `ℝ`-action on `LocalHull (familySubst k hk)`;
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
    ∀ μ, IsProbabilityMeasure μ → Invariant (translate (familySubst k _)) μ →
      PureDiscrete (translate (familySubst k _)) μ
```

No finiteness, coincidence, root, recognizability or spectral premise is supplied by the
caller. The request's quantifier symbol was lost in transit; it is read here as `k`. The Lean
termination proof needs `2 ≤ k` (`terminates_with_coincidence`), so `k = 1` is either a
separate finite certificate or stays external through the cubic trace-at-most-two theorem.

Dependencies: F1 → F2.1, F2.6; F2.2 → F2.3 → F2.7 → F4(a); F3 → F4(c); F4 → F5. F2.2–F2.5 and
F4(d) have no family dependency and can start immediately.

## 3. Non-claims

1. Nothing here is proved; the signatures are targets and may change at each stop/go.
2. No universal PIP3 statement: every stage is for `σ_k` or for a generic `LengthSubst`, and
   F4(c) is the family's criterion, not a strict-system exclusion.
3. Finite fibres, BDS periodicization and the BBK identification are not on this path unless
   F4(a) or (c) turns out to need them; if so that is recorded at the stage's stop/go.
4. Lean is the deductive layer here. No executable census or certificate is planned, so no
   Mojo module is owed; if a stage adds a finite computation it goes to `kernel/` first.
