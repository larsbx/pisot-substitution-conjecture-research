# The measured pure-discrete interface for the σₖ hull

**Status:** Lean now defines pure discrete spectrum of a measured real flow and proves three
implications that reduce the family's measured conclusion to one named input. For every
`k ≥ 1` and every translation-invariant finite Borel measure on the ordinary legal hull, the
image measure on the full solenoid is flow invariant and the solenoid flow has pure discrete
spectrum for it. The hull conclusion is **conditional** on a measurable almost everywhere
inverse of the realization. That input, the existence of an invariant measure and weak
regularity of its image are not proved. The family statement therefore remains: *family
criterion inputs proved in Lean; spectral conclusion obtained by a published theorem.* No
governed claim changes. Independent human review is pending.

Starting revision: `main@f5ba148d` (through #649).

## Source decision

Proceed, narrowed to the generic measure-theoretic transfer and its family specialization.

- The claim. If an equivariant measure-preserving map onto a system with pure discrete
  spectrum is invertible almost everywhere, the source has pure discrete spectrum. This is
  the standard direction of the Halmos–von Neumann picture and is not new. Only the
  formalization and its binding to the constructed realization are added.
- Prior art already recorded for this route.
  [Next obligations](c4-finite-fibre-obligations-2026-11-21.md) fixes Barge–Kellendonk
  (Lemma 2.12, Theorems 2.25 and 5.4), Baker–Barge–Kwapisz (Theorems 4.2, 5.1, Corollary 5.2)
  and Barge–Štimac–Williams (Theorem 3.1, Corollary 2) as the sources, and
  [the spectral interface](c4-zero-fibre-spectral-interface-2026-11-21.md), §4, states the
  one-way `L²` route used here. Those papers were not re-read in this session; this note
  relies on those two recorded decisions.
- Hypotheses that transfer: continuity, equivariance and surjectivity of the realization, and
  uniform density of the solenoid characters, all already in Lean.
- Hypotheses that do not transfer. Finite fibres and coincidence rank one do not give
  almost everywhere singleton fibres; the recorded decision says so explicitly. So the
  inverse stays a hypothesis.
- Known control. Thue–Morse has a finite-to-one factor onto its solenoid that is two-to-one
  almost everywhere and does not have pure discrete spectrum, so the inverse premise cannot
  be dropped. This is a written control, not formalized here.

## Work shown

### Assumptions and hypotheses

| Object or premise | Role | Status |
| --- | --- | --- |
| `MeasuredFlow μ` | maps `φ t`, each `μ`-preserving. No group law or continuity. | definition |
| `PureDiscrete F` | the complex span of `{f ∈ L²(μ; ℂ) \| ∃ ω : ℝ, ∀ t, f ∘ φ t = e^{2πiωt} f}` is dense | definition |
| `μ` on `LocalHull (geometry k hk)` | finite, Borel, translation invariant | hypothesis; existence not proved |
| `(μ.map solenoidRealize).WeaklyRegular` | lets continuous functions be dense in `L²` | hypothesis |
| `h` measurable, `h ∘ solenoidRealize =ᵐ[μ] id` | almost everywhere inverse | hypothesis; this is the open singleton-fibre input |

The Borel structures on the hull and the solenoid are instance arguments. No Lean axiom is
added.

### Derivation / reduction

1. **Continuous eigenfunctions** (`isEigen_toLp`, `pureDiscrete_of_continuous_eigen`). On a
   compact Hausdorff space with a finite weakly regular measure, `C(Y, ℂ) → L²` is continuous
   with dense range. A pointwise eigenfunction maps to an `L²` eigenfunction, so a set of
   them with uniformly dense span has dense span in `L²`.
2. **Target** (`solenoid_pureDiscrete`). The characters satisfy `character_flow` with
   frequency `frequency S P c`, and `span_character_closure_eq_top` is uniform density. Step 1
   applies for every `LengthSubst` with `PisotData`, and every invariant such measure.
3. **Intertwining** (`koopman_pullback`, `isEigen_pullback`). If `g ∘ φ t = ψ t ∘ g` almost
   everywhere, pullback by `g` commutes with the Koopman operators and preserves frequencies.
4. **Transfer** (`pureDiscrete_of_denseRange`). Pullback is a linear isometry; if its range
   is dense, the image of a dense span is dense and lies in the source eigenspan.
5. **Inverse** (`measurePreserving_of_ae_inverse`, `surjective_pullback_of_ae_inverse`). If
   `h ∘ g = id` almost everywhere then `h_* ν = μ`, and `f = (f ∘ h) ∘ g` almost everywhere,
   so pullback is onto.
6. **Family** (`image_flow_invariant`, `image_pureDiscrete`,
   `hull_pureDiscrete_of_ae_inverse`). `solenoidRealize_translate` and
   `measurePreserving_map_of_semiconj` give invariance of the image measure; steps 2 and 5
   then give the conditional hull conclusion for `k ≥ 1`.

### Evidence and replay

| Module | Checked scope |
| --- | --- |
| [`MeasuredPureDiscrete.lean`](../proof/PscVerif/PscVerif/MeasuredPureDiscrete.lean) | definitions, steps 1 and 3–5, the two stationary controls |
| [`PeriodicPartnerSolenoidPureDiscrete.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerSolenoidPureDiscrete.lean) | step 2 |
| [`C4FamilyMeasuredSpectrum.lean`](../proof/PscVerif/PscVerif/C4FamilyMeasuredSpectrum.lean) | step 6 |
| [`C4MeasuredSpectrumAudit.lean`](../proof/PscVerif/C4MeasuredSpectrumAudit.lean) | five literal endpoint types, standard axioms only over all three modules, twelve refusal controls |

```sh
(cd proof/PscVerif && lake build PscVerif.C4FamilyMeasuredSpectrum \
  && lake env lean -DautoImplicit=false -Dpp.unicode.fun=true C4MeasuredSpectrumAudit.lean)
python3 tools/make_proof_bank.py --check
./tools/check_c4_parameter_family.sh
```

Session receipt (Lean `v4.34.0-rc2`, cached build of the dependency closure):
`PSC_MEASURED_SPECTRUM_AUDIT_COMPLETE 60 38`, `PSC_MEASURED_SPECTRUM_REFUSAL_CONTROLS 12`.
The first two commands were run. The isolated family gate was extended with this audit and
passes a shell syntax check, but it was **not** run from fresh sources in this session, and
there is no hosted receipt yet.

### Negative controls

- `eq_zero_of_stationary_frequency_one`: under the stationary flow a function with frequency
  one is zero, so the frequency in `IsEigen` is a real constraint.
  `pureDiscrete_stationary` is the matching positive control.
- The audit refuses `HullUnconditionalType`, the family endpoint with the inverse premise
  removed, and `TransferNoInverseType`, the transfer with neither inverse nor density.
- These controls test the statements. They do not exhibit a system without pure discrete
  spectrum; the Thue–Morse control above is written only.

### Non-claims / remaining gaps

1. **No unconditional spectral theorem.** The almost everywhere inverse is not constructed.
   It needs Haar-almost-every fibre to be a singleton and a measurable choice of the inverse.
2. **No invariant measure is constructed**, on the hull or the solenoid, and uniqueness is
   not asserted. Haar measure on the solenoid is not defined.
3. **Weak regularity of the image measure is assumed.** It should follow from metrizability
   of the solenoid; that instance is not derived.
4. `PureDiscrete` is density of eigenfunctions. No converse and no classification of
   eigenvalues is stated.
5. The symbolic `ℤ`-shift is not addressed; the conclusion concerns the tiling `ℝ`-action
   only. `k = 1` is included in the conditional statement and gains nothing unconditional.
6. C4 and PSC remain open.
