# The Pisot contraction, derived; Tribonacci as a PIP3 instance

**Status:** Lean derives the `PisotData` contraction of the
[geometric realization](c4-geometric-realization-2026-11-19.md) from the characteristic
polynomial, closing its non-claim 2. The input is a factorization `χ_M = (X − β) Q` with
`Q(β) ≠ 0` and all roots of `Q` in the open unit disc (`SpectralPisot`), and that input is in turn
produced from the PIP3 conditions (irreducible `χ_M` over `ℚ`, Pisot root condition). Tribonacci
`01/02/0` is proved to be a PIP3 member and receives `PisotData` this way. Recognizability, BDS
and finite fibres remain inputs. Independent human review is pending. C4 and PSC remain open; no
governed claim changes.

Starting revision: `main@c1ce386`.
[Source decision](c4-pisot-contraction-stop-go-2026-11-19.md).

## Work shown

### Assumptions and hypotheses

| Input | Formal role | Status |
| --- | --- | --- |
| `LengthSubst α`, `[Fintype α]`, `[Nonempty α]` | As in the hull; `ℓ > 0`, `ℓ M = β ℓ`. | as before |
| `SpectralPisot S` | `Q : ℝ[X]`, `χ_M = (X − C β) Q`, `Q.eval β ≠ 0`, `∀ μ : ℂ`, root of `Q` ⇒ `‖μ‖ < 1`. | hypothesis of `toPisotData` |
| `ofIrreducible` | `p : ℚ[X]` irreducible, `χ_M = p.map ℚ→ℝ`, every complex root `μ ≠ β` of `χ_M` has `‖μ‖ < 1`. | hypotheses; all proved for Tribonacci |

No Lean axiom is added.

### Derivation

Write `M` for `mat S`.

1. **Left side** (`vecMul_mat`, `vecMul_aeval_eigen`, `dot_aeval`). `ℓ M = β ℓ`, so
   `ℓ ⬝ p(M) v = p(β) (ℓ ⬝ v)` for every polynomial `p`.
2. **The eigenvector** (`w_eigen`, `u`, `dot_u`). Cayley–Hamilton and (F) give
   `(M − β) Q(M) = 0`. With `w = Q(M) ℓ`, `M w = β w` and `ℓ ⬝ w = Q(β) ‖ℓ‖₂² ≠ 0`;
   `u = w / (ℓ ⬝ w)`.
3. **No `β`-eigenvector in `ker ℓ`** (`rootMultiplicity_β`, `eq_zero_of_eigen_β`). Over `ℂ` the
   root multiplicity of `β` in `χ_M = (X − β) Q` is `1`, so the `β`-eigenspace has dimension
   `≤ 1` (`LinearMap.finrank_eigenspace_le`). It contains `u`, with `ℓ ⬝ u = 1`, so any
   `β`-eigenvector `v` with `ℓ ⬝ v = 0` is `0`.
4. **Other eigenvalues** (`isRoot_of_eigen`). If `M v = μ v`, `v ≠ 0`, then
   `0 = χ_M(M) v = (μ − β) Q(μ) v`, so `μ ≠ β` forces `Q(μ) = 0` and `‖μ‖ < 1`.
5. **Deflation** (`B`, `dot_B`, `B_pow_mulVec`, `norm_lt_one_of_mem_spectrum`). Over `ℂ`,
   `B = M − β u ℓᵀ` satisfies `ℓ ⬝ B x = 0` for all `x` and `B x = M x` on `ker ℓ`; hence
   `Bⁿ x = Mⁿ x` there. If `μ ≠ 0` is in the spectrum of `B` (a root of `χ_B`, hence an
   eigenvalue), its eigenvector lies in `ker ℓ` and is an eigenvector of `M`; step 3 excludes
   `μ = β`, step 4 gives `‖μ‖ < 1`. So the spectral radius of `B` is `< 1`
   (`spectralRadius_B_lt_one`).
6. **Gelfand** (`exists_pow_norm_le`). In any complex Banach algebra, spectral radius `< 1`
   gives `‖aⁿ‖ ≤ C ρⁿ` with `0 < ρ < 1`: Gelfand's formula bounds `‖aⁿ‖ ≤ ρⁿ` for `n > N`, and
   `C = 1 + Σ_{k ≤ N} ‖aᵏ‖ / ρᵏ` covers the rest. Here the algebra is `Matrix α α ℂ` with the
   `ℓ^∞` operator norm.
7. **Back to `ℝ`** (`norm_ofReal_comp`, `exists_contract`, `toPisotData`). For real
   `v ∈ ker ℓ`, `‖Mⁿ v‖ = ‖Bⁿ v‖ ≤ ‖Bⁿ‖ ‖v‖ ≤ C ρⁿ ‖v‖` (sup norms agree under `ℝ → ℂ`).
8. **The PIP3 form** (`isRoot_charpoly_β`, `ofIrreducible`). `ℓ ≠ 0` and `ℓ (β − M) = 0` give
   `χ_M(β) = 0`. `Q := χ_M /ₘ (X − β)`. An irreducible polynomial over `ℚ` is separable, so
   `χ_M` is squarefree over `ℝ`, and `Q(β) = 0` would put `(X − β)²` in `χ_M`. A root of `Q` is a
   root of `χ_M` other than `β`, so the Pisot condition applies.

### Tribonacci

`0 ↦ 01`, `1 ↦ 02`, `2 ↦ 0`; `M = [[1,1,1],[1,0,0],[0,1,0]]`; `τ ∈ (1, 2)` the root of
`X³ − X² − X − 1` (intermediate value theorem on `[1, 2]`); `ℓ = (τ, τ² − τ, 1)`.

| Fact | Lean | Argument |
| --- | --- | --- |
| `χ_M = X³ − X² − X − 1` | `tribonacci_charpoly` | `det_fin_three` |
| primitive | `tribonacci_primitive` | `M³ = [[4,3,2],[2,2,1],[1,1,1]] > 0` |
| irreducible over `ℚ` | `tribPolyℚ_irreducible` | a rational root is an integer dividing `−1`; `±1` are not roots |
| Pisot | `norm_lt_one_of_root` | `Q = X² + (τ−1)X + (τ²−τ−1)`, `τ(τ²−τ−1) = 1`. A real root would need `(τ−1)² ≥ 4/τ`, false for `τ < 2`; a nonreal root has `Re μ = −(τ−1)/2` and `|μ|² = τ² − τ − 1 = 1/τ < 1`. |
| membership | `tribonacci_mem_PIP3` | the conjunction of the above with `ne_nil`, `1 < τ`, `χ_M(τ) = 0` |
| (F) by hand | `tribonacciSpectral` | `Q(τ) = (3τ + 1)(τ − 1) ≠ 0` |
| (F) from PIP3 | `tribonacciSpectralPIP3` | `ofIrreducible` |
| `PisotData` | `tribonacciPisot` | `tribonacciSpectralPIP3.toPisotData` |

### Evidence and replay

| Module | Checked scope |
| --- | --- |
| [`PeriodicPartnerSpectral.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerSpectral.lean) | Polynomial-in-matrix eigen lemmas, Gelfand bound, `SpectralPisot`, eigenvector, complexification, deflation, spectral radius, `toPisotData`, `ofIrreducible`. |
| [`PeriodicPartnerSpectralModels.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerSpectralModels.lean) | `τ`, Tribonacci `LengthSubst`, characteristic polynomial, primitivity, irreducibility, root bound, PIP3 membership, `tribonacciPisot`. |

```sh
(cd proof/PscVerif && lake build PscVerif.PeriodicPartnerSpectral PscVerif.PeriodicPartnerSpectralModels)
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
```

Both modules are in the periodic-partner audit closure (`PeriodicPartnerAudit.lean`), which
checks every compiled declaration for the standard axioms only. Session receipt (Lean
`v4.34.0-rc2`, source snapshot `27d4667c…5704` over 224 files):
`PSC_PERIODIC_PARTNER_AUDIT_VERIFIED 18 934 659 388`,
`PSC_PERIODIC_PARTNER_GATE_COMPLETE fresh-local-closure standard-axioms-only`. The hosted CI
receipt is separate.

### Negative controls

The existing `doubled_not_pisot` (root `−1` on `ker ℓ`) shows the root condition of (F) cannot be
dropped. `thueMorsePisot` (`Q = X`) is consistent with (F) but is not PIP3; it is not re-derived.

### Non-claims / remaining gaps

1. **No universal instance.** (PIP3) ⇒ `PisotData` is proved for every `LengthSubst` meeting its
   hypotheses; that the 4,554 census members meet them is the census's exact Pisot screen and is
   not imported into Lean. Only Tribonacci is instantiated.
   *Update:* the [census note](c4-pisot-census-2026-11-19.md) brings the census into Lean: a
   kernel-evaluated certificate and its refutation decide PIP3 on all 59,319 three-letter
   substitutions with images of length at most three, exactly 4,554 are members, and each
   receives `PisotData` through `SpectralPisot.toPisotData`.
2. **Recognizability, BDS and finite fibres** remain inputs for Tribonacci as for every
   `LengthSubst`; `tribonacciPisot` does not by itself produce `publishedInputs`.
3. Non-claims 1, 3–6 of the [realization note](c4-geometric-realization-2026-11-19.md)
   (finite fibres, recognizability, continuity, reducible case, selection and the global
   rank-two contradiction) are unchanged.
