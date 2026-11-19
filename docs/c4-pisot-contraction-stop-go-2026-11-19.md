# The Pisot contraction from the characteristic polynomial: source decision

**Status:** Source decision for non-claim 2 of the
[geometric-realization note](c4-geometric-realization-2026-11-19.md): derive the `PisotData`
contraction from the characteristic polynomial instead of supplying it, and instantiate it on a
PIP3 member. Starting revision: `main@c1ce386`. No governed claim changes.

## Exact target

For `S : LengthSubst α` with substitution matrix `M`, positive left eigenvector `ℓ` (`ℓ M = β ℓ`)
and `α` nonempty, produce `PisotData S`, i.e. `u` with `M u = β u`, `ℓ ⬝ u = 1`, and
`C ≥ 0`, `0 ≤ ρ < 1` with `‖Mⁿ v‖ ≤ C ρⁿ ‖v‖` for all `v ∈ ker ℓ`, from

- **(F)** `χ_M = (X − β) Q` with `Q(β) ≠ 0` and every complex root of `Q` of modulus `< 1`;
  and, as a corollary, from
- **(PIP3)** `χ_M` the image of an irreducible polynomial over `ℚ`, and every complex root of
  `χ_M` other than `β` of modulus `< 1`.

Then instantiate (PIP3) and the contraction for Tribonacci `01/02/0`.

## Sources

| Source | Input and boundary |
| --- | --- |
| I. Gelfand, *Normierte Ringe*, Mat. Sb. 9 (51) (1941), 3–24 | Spectral radius formula `r(a) = lim ‖aⁿ‖^{1/n}` in a complex Banach algebra. Bibliographic citation; **not re-opened**. Used through Mathlib's `spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius`, whose proof is machine-checked, so the citation carries no proof load. |
| Mathlib, `Mathlib/LinearAlgebra/Eigenspace/Zero.lean` (`LinearMap.finrank_eigenspace_le`), at the pinned revision `4edb0db` | Geometric multiplicity `≤` root multiplicity of the characteristic polynomial. Read in this session at the pinned checkout. |
| Mathlib, `Mathlib/FieldTheory/Separable.lean` (`Irreducible.separable`), `Mathlib/RingTheory/Polynomial/RationalRoot.lean` (`exists_integer_of_is_root_of_monic`), same pin | Irreducible over a characteristic-zero field implies separable; rational roots of a monic integer polynomial are integer divisors of the constant term. Read in this session. |
| G. Rauzy, *Nombres algébriques et substitutions*, Bull. SMF 110 (1982), 147–178 | The Tribonacci substitution `1 ↦ 12, 2 ↦ 13, 3 ↦ 1`, its Pisot unit `τ` with `τ³ = τ² + τ + 1`, and the complex conjugate pair of modulus `τ^{-1/2}`. Bibliographic citation; **not re-opened**. Every fact used is re-proved in Lean here. |
| Baker–Barge–Kwapisz (2006), §3 | The role of the contraction on `Eˢ` in the realization; already recorded in the [realization source decision](c4-geometric-realization-stop-go-2026-11-19.md). Not re-opened. |

## Hypotheses that transfer, and those that do not

- **Transfer.** The stable space of BBK is `ker ℓ` here (it is `M`-invariant, and complementary
  to `u`). Gelfand's formula is applied to the deflated matrix `B = M − β u ℓᵀ` over `ℂ` with the
  `ℓ^∞` operator norm, not to the restriction of `M` to `ker ℓ`: this avoids a normed-algebra
  structure on a subspace. `Bⁿ v = Mⁿ v` on `ker ℓ`, and a nonzero eigenvalue of `B` has its
  eigenvector in `ker ℓ`.
- **Simplicity of `β`.** Needed twice: to normalise `u` (`ℓ ⬝ Q(M) ℓ = Q(β) ‖ℓ‖² ≠ 0`) and to
  exclude a `β`-eigenvector in `ker ℓ` (it would give a two-dimensional eigenspace against root
  multiplicity one). In (PIP3) it comes from separability; no Perron–Frobenius argument is used.
- **`β` a root.** Not assumed in (PIP3): `ℓ` is a nonzero left kernel vector of `β − M`.
- **Primitivity.** Not used by the derivation. It is proved for Tribonacci (`M³ > 0`) only to
  certify PIP3 membership.
- **Do not transfer.** Recognizability, BDS and finite fibres are unrelated to the spectral
  hypothesis and stay inputs of `publishedInputs`. The universal statement "every PIP3 member
  satisfies (PIP3)" needs, per member, the root condition, which is the census's Pisot screen;
  the census is not imported into Lean.

## Controls

- `doubled` (`0 ↦ 011, 1 ↦ 100`) has `χ_M = (X − 3)(X + 1)`: the root `−1` violates (F), and
  `doubled_not_pisot` already shows no `PisotData` exists. The derivation therefore cannot be
  strengthened to drop the root condition.
- Thue–Morse has `χ_M = X(X − 2)`, reducible over `ℚ` only through the factor `X`; (F) holds with
  `Q = X`, consistent with the existing `thueMorsePisot` (`ρ = 0`). It is not PIP3.

## Decision

**Proceed** with (F) ⇒ `PisotData` through Gelfand's formula, the corollary (PIP3) ⇒ (F), and the
Tribonacci instance with PIP3 membership proved in Lean. **Do not** import the census, and do not
attempt recognizability, BDS or finite fibres.
