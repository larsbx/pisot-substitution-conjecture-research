# The census in Lean: source decision

**Status:** Source decision for non-claim 1 of the
[contraction note](c4-pisot-contraction-2026-11-19.md): bring the 4,554 census members into Lean
with the derived `PisotData`, instead of Tribonacci alone. Starting revision: `main@c0231e0`.
No governed claim changes.

## Exact target

For every substitution `σ` on `{0, 1, 2}` with images of length one to three
(`39³ = 59 319` specimens), Lean decides whether `σ` underlies a PIP3 `LengthSubst (Fin 3)`, and
for each that does, produces one with `PisotData`. The count must be the census count `4 554`.

## Sources

| Source | Input and boundary |
| --- | --- |
| [`PeriodicPartnerSpectral`](../proof/PscVerif/PscVerif/PeriodicPartnerSpectral.lean) (`SpectralPisot.toPisotData`, `ofIrreducible`) | The contraction from `χ_M = (X − β) Q`. Machine-checked in the previous round; used unchanged. |
| E. I. Jury, *Theory and Application of the z-Transform Method*, Wiley (1964), §3 (stability table) | For a monic real quadratic `Q`, both roots in the open unit disc ⟺ `Q(1) > 0`, `Q(−1) > 0`, `|Q(0)| < 1`. Bibliographic citation; **not re-opened**. Both directions are re-proved in Lean (`norm_lt_one_of_quadratic`, `jury_of_norm_lt_one`). |
| Mathlib at the pinned revision `4edb0db`: `Matrix.aeval_self_charpoly`, `Matrix.charpoly_map`, `Matrix.det_fin_three`, `intermediate_value_Icc`, `exists_integer_of_is_root_of_monic`, `irreducible_of_degree_le_three_of_not_isRoot`, `Polynomial.degree_eq_one_of_irreducible_of_root` | Cayley–Hamilton, base change of `χ`, the `3 × 3` determinant, the intermediate value theorem, the rational root theorem, and the degree-≤ 3 irreducibility test. Read in this session at the pinned checkout. |
| [`reference/psc_research/pip_screen.py`](../reference/psc_research/pip_screen.py), [`kernel/psc/pisot.mojo`](../kernel/psc/pisot.mojo) | The census definition (primitive, rational-root irreducibility, Sturm Pisot test) and its enumeration order. Used only as the external count to agree with; **not imported** into Lean. |

## Hypotheses that transfer, and those that do not

- **The cofactor.** If `p(β) = 0` then `χ_M = (X − β)(X² + (β − T)X + D/β)`; this is algebra,
  valid for any root `β ≠ 0`. With Jury's conditions on that quadratic, the Pisot condition
  becomes three sign conditions: `p(1) = (1 − β) Q(1) < 0`, `p(−1) = (−1 − β) Q(−1) < 0`, and
  `|D| < β`. The last is decided by bracketing `β` above `max(1, |D|)`.
- **The positive eigenvector without Perron–Frobenius.** `ℓ = 𝟙ᵀ Q(M)` is a left
  `β`-eigenvector by Cayley–Hamilton. Its positivity is a per-specimen fact: `β ℓⱼ` is an
  explicit integer quadratic in `β`, bounded below on a dyadic bracket of width `1/16`. A
  Python prototype (below) found the bracket of width `1/4` already sufficient on all 4,554.
- **Primitivity** enters PIP3 as `M⁵ > 0`. It is never needed to *reject* a specimen: the four
  cheap necessary conditions (`p(±1) < 0`, no integer root, `p(|D|) < 0` for `|D| ≥ 2`) already
  reject all 54,765 non-members. So completeness does not need Wielandt's exponent bound or
  Perron–Frobenius.
- **Kernel evaluation.** `decide +kernel` evaluates in the trusted kernel, with no
  `Lean.ofReduceBool` axiom, so the standard-axioms audit applies unchanged. A single
  evaluation of all 59,319 specimens exceeded 13 GB of memory; one declaration per first image
  stays within 4.4 GB.
- **Do not transfer.** Recognizability, BDS and finite fibres are unrelated to the spectral
  certificate and stay inputs of `publishedInputs`. Alphabets other than three and longer images
  are outside the enumeration.

## Prototype

A Python prototype in this session (not committed; the Lean modules are the record) checked
three facts on the census:

| Check | Result |
| --- | --- |
| `p(1) < 0 ∧ p(−1) < 0 ∧ (|D| ≤ 1 ∨ p(|D|) < 0)`, with `M⁵ > 0` and the rational root test, against `pip_corpus()` | 4,554 selected, identical list and order |
| bracket width `1`, `1/2`, `1/4`, …, `1/2¹⁶` for positivity of `ℓ` | 36 failures at width `1`, none from width `1/2` |
| every non-member refuted by one of the four necessary conditions | 27,963 / 13,142 / 10,228 / 3,432 (by first failing condition), none unrefuted |

## Decision

**Proceed** with a kernel-evaluated certificate `check` and its soundness proof, a rejection
certificate `refute` and its proof against PIP3, and the enumeration of all 59,319 specimens in
Lean. **Do not** import the Mojo census, `native_decide`, or any floating point. **Do not**
attempt recognizability, BDS or finite fibres.
