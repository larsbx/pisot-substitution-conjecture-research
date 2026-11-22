# Unique ergodicity of the literal σₖ translation flow

**Status:** Lean proves that the invariant Borel probability measure of the family's
translation flow is unique, and hence that the measured pure-discrete conclusion holds for
*every* translation-invariant Borel probability on the ordinary legal hull, `k ≥ 2`. The
endpoint `C4FamilyUniqueErgodicity.pureDiscrete_of_invariant` has premises `k`, `1 ≤ k`,
`2 ≤ k`, the measure and its invariance, and nothing else. No governed claim changes.
Independent human review is pending. C4 and PSC remain open.

Starting revision: `main@968fabde` (through #650).

## Source decision

Proceed, narrowed to uniqueness of the invariant measure.

- **What was already proved.** [#650](c4-family-measured-spectrum-2026-11-21.md) constructs
  normalized Haar measure on the full solenoid, a conull set of singleton fibres, a measurable
  inverse, the lifted measure `hullMeasure` with its translation and inflation invariance,
  and `pureDiscrete_translation` for that one measure. It also proves
  `hullMeasure_eq_of_map`: a hull measure projecting to Haar is `hullMeasure`. The three
  hypotheses of the earlier conditional interface (an invariant measure, weak regularity of
  its image, an almost everywhere inverse) are therefore discharged there, not here.
- **The gap.** That theorem speaks about a measure the proof chose. The target of the
  [roadmap](c4-family-lean-dynamical-roadmap-2026-11-21.md) quantifies over invariant
  measures. The missing fact is that a flow-invariant probability on the solenoid is Haar.
- **Prior art.** A minimal translation flow on a compact abelian group is uniquely ergodic;
  this is classical (it is in the standard textbooks, for instance Walters, *An Introduction
  to Ergodic Theory*, chapter 6, cited from memory) and no novelty is claimed. The #650 note already observes that an
  invariant probability on the target must be Haar, as a written remark. The textbook
  statement was not re-read in this session; the proof below is self-contained in Lean.
- **Hypotheses that transfer.** Dense real flow orbit, explicit characters with real
  frequencies, uniformly dense character span: all in Lean for `k ≥ 1`.
- **Known boundary.** Without invariance the statement is false, and a flow with a
  non-dense orbit has many invariant measures. The proof uses density through
  `character_eq_one_of_frequency_eq_zero`.

## Work shown

### Assumptions and hypotheses

| Premise | Role |
| --- | --- |
| `k`, `1 ≤ k` | the literal family, its geometry and `PisotData` |
| `ν` a Borel probability on the solenoid, preserved by `flow P t` for all `t` | hypothesis of `flowInvariant_eq_haar` |
| `2 ≤ k` | only for the hull statements, through `hullMeasure` |
| `μ` a Borel probability on `LocalHull`, preserved by every translation | hypothesis of the hull statements |

The Borel structures are the scoped instances of #650. No regularity is assumed of `ν` or
`μ`. No Lean axiom is added.

### Derivation / reduction

1. **Character integrals** (`integral_character`). Let `χ` be a certificate character with
   frequency `ξ`, so `χ(flow t z) = e^{2πitξ} χ(z)`. If `ξ = 0` then `χ = 1` and `∫ χ dν = 1`.
   If `ξ ≠ 0`, take `t = 1/(2ξ)`: the phase is `−1`, and invariance gives
   `∫ χ dν = ∫ χ ∘ flow t dν = −∫ χ dν`, so the integral is `0`. The value depends only on `χ`.
2. **Haar is invariant** (`flow_haar`). `flow t` is addition of `flow t 0`.
3. **All continuous functions** (`integral_continuous_eq`). `f ↦ ∫ f dρ` is 1-Lipschitz on
   `C(G, ℂ)` for a probability `ρ`. The functions on which `ν` and Haar agree form a closed
   complex subspace containing the characters, hence their closed span, which is everything
   by `span_character_closure_eq_top`.
4. **Equality of measures** (`flowInvariant_eq_haar`). The solenoid embeds in a countable
   product of second-countable tori, so it is second countable, and compact Hausdorff, hence
   metrizable. Finite Borel measures on such a space with equal integrals of bounded
   continuous real functions are equal.
5. **The hull** (`translationInvariant_eq_hullMeasure`). The image of `μ` under the
   realization is a flow-invariant probability by `solenoidRealize_translate`, so it is Haar,
   and `hullMeasure_eq_of_map` gives `μ = hullMeasure`.
6. **Spectrum** (`pureDiscrete_of_invariant`). Substitute and apply
   `pureDiscrete_translation`.

### Evidence and replay

| Module | Checked scope |
| --- | --- |
| [`C4FamilyUniqueErgodicity.lean`](../proof/PscVerif/PscVerif/C4FamilyUniqueErgodicity.lean) | steps 1–6 |
| [`C4FamilyUniqueErgodicityAudit.lean`](../proof/PscVerif/C4FamilyUniqueErgodicityAudit.lean) | three literal endpoint types, standard axioms only for every declaration of the module, nine refusal controls |

```sh
(cd proof/PscVerif && lake build PscVerif.C4FamilyUniqueErgodicity \
  && lake env lean -DautoImplicit=false -Dpp.unicode.fun=true C4FamilyUniqueErgodicityAudit.lean)
python3 tools/make_proof_bank.py --check
./tools/check_c4_parameter_family.sh
```

Session receipt (Lean `v4.34.0-rc2`; the dependency closure through
`C4FamilyMeasuredSpectrum` was built locally, 3,181 jobs):
`PSC_UNIQUE_ERGODICITY_AUDIT_COMPLETE 23 8`, `PSC_UNIQUE_ERGODICITY_REFUSAL_CONTROLS 9`, and
`pureDiscrete_of_invariant` depends on `propext`, `Classical.choice`, `Quot.sound` only. The
first two commands were run. The isolated family gate was extended with this module and
audit and passes a shell syntax check; it was **not** run from fresh sources in this
session, and there is no hosted receipt.

### Negative controls

The audit refuses three altered contracts: both uniqueness statements with the invariance
premise removed, and the spectral statement with `2 ≤ k` removed. These are refusals of
statements. No Lean theorem here exhibits a second invariant measure for a non-minimal flow;
that boundary is written only.

### Non-claims / remaining gaps

1. The conclusion concerns the tiling `ℝ`-action. The symbolic `ℤ`-shift needs a separate
   transfer theorem.
2. `k = 1`: uniqueness on the solenoid holds, but there is no singleton-fibre theorem and no
   Lean spectral conclusion. It stays with the published trace-at-most-two result.
3. Pure discreteness here is density of eigenvectors. No converse and no description of the
   eigenvalue group beyond the certificate frequencies.
4. The criterion is not named in the final statement: the proof passes through the family's
   automaton witnesses, and no single `FullFactorCriterion` structure is consumed.
5. The family is one determinant-two example. Nothing is asserted for other substitutions,
   and C4 and PSC remain open.
