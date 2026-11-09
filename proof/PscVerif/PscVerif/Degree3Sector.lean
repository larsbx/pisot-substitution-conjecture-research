import PscVerif.SectorBridge
import PscVerif.GaloisOrbit
import PscVerif.PerronExistence

/-!
# `thm:deg23` (iii): the degree-three sector lies in the `det M`-eigenspace

`manuscripts/PSC_balanced_pair_state_2026-09-13.tex`, `thm:deg23` (iii) (line 733) and
the (iii) part of its proof (line 737): "`Φ₃` has eigenvalues `βᵢ²βⱼ` (`i ≠ j`) and
`det M` with multiplicity two; `Φ₃` is semisimple since `χ_M` is. [...] A rational invariant
subspace of spectral radius `≤ β` therefore [...] lies in the `det M`-eigenspace; apply
Theorem `thm:defect-intertwiner`."  Inputs: `thm:defect-intertwiner` (line 721; `Q₃ S = Φ₃ Q₃`,
`Psc.SectorBridge.q3m_intertwine`) and `prop:cocycle` (line 705; `ρ(S) ≤ β`).  The census
`comp:defect` (line 1200) and its "Meaning" paragraph (line 1204) supply the content control.
`docs/c4-concentration-attack-2026-11-06.md` §8, rows `LieWeights`, `SectorBridge`
(whose "Not proved here" lists exactly this case analysis), `GaloisOrbit` and
`PerronExistence`; `docs/c4-defect-degree-census.md` §3 for the census state.

Setting and notation are those of `Psc.SectorBridge`: `S` a child system over `Fin 3`,
`P` a normalisation, `M = incQ S`, `χ_S` the characteristic polynomial of the cocycle matrix
`SsignQ P`, `Lie₃ = Lie3Q`, `Φ₃ = phi3Lie M`, `Q₃ = Q3m P hbal`, `q₃ = q3 P hbal`
`= χ(Φ₃|_{im Q₃})`; `β, α, γ` are pairwise distinct complex roots of `χ_M`.
`resCharpoly φ hW = χ(φ|_W)` for a `φ`-invariant `W`.

## Proved here, in full

* **The `(2,1,0)` orbit under the bound** (any rational `q`, `χ_M` irreducible):
  `orbit_210_root` (a root of `q` of shape `(2,1,0)` gives the root `β²δ`, `δ ∈ {α, γ}`, by
  `Psc.GaloisOrbit.orbit_exponent_on_beta`); `norm_lt_norm_sq_mul` (`‖β‖ < ‖β²δ‖` from
  `‖α‖, ‖γ‖ < 1 ≤ ‖βαγ‖`: `‖βδ‖ = ‖βαγ‖ / ‖other root‖ > 1`; no bound `1 < ‖β‖` is used);
  `shape3_root_eq`: if every root of `q` has modulus `≤ ‖β‖`, a root of `q` that is a
  degree-three weight `x^κ` (`Shape3 κ`) equals `βαγ`.
* **Helpers.**  From `Psc.SectorBridge` (shared with `Psc.Degree4Floor`):
  `det_eq_mul_roots` (`det M = βαγ`), `root_cases` (three pairwise distinct complex roots of
  `χ_M` are all of its roots), `one_le_norm_mul_roots`, `M0_det`,
  `ssign_root_bound_of_perron`.  Here: `norm_mul_lt_one`; `one_le_abs_det` (an
  integral `M` with irreducible `χ_M` has `|det M| ≥ 1`, via
  `Psc.Cyclicity.det_ne_zero_of_irreducible`); `eq_X_sub_C_pow_of_roots` (a monic rational
  polynomial whose complex roots all equal `d` is `(X - d)^{deg}`); `charpoly_smul_one`;
  `resCharpoly` with `resCharpoly_monic`, `resCharpoly_natDegree`, `resCharpoly_dvd`
  (`Psc.SectorBridge.charpoly_restrict_dvd`), `pow_sub_smul_apply_eq_zero` (Cayley–Hamilton
  on `W`), `resCharpoly_of_le_ker`, `invariant_of_le_ker`.
* **Semisimplicity of the rational `Φ₃`, kernel form**: `phi3Lie_sub_smul_of_pow`: if the
  rational `M` is `Q (diag x) Q⁻¹` over some field of characteristic zero, then on
  `Lie₃(ℚ³)`, `(Φ₃ - μ)^k v = 0 ⇒ (Φ₃ - μ) v = 0` for every rational `μ`.  Proof: base change
  of `v` along `map3` (`map3_pow_sub_smul`, from `Psc.Lie3.phi3_map`), the Lyndon eigenbasis
  of `Psc.LieWeights.exists_eigenbasis_phi3Lie`, the general `sub_smul_eq_zero_of_pow` (an
  endomorphism with an eigenbasis), and injectivity of `map3` (`map3_eq_zero`).
* **The multiplicity of `det M` in `χ(Φ₃)`** (three pairwise distinct complex roots,
  `det M ≠ 0`; no irreducibility, no moduli): `le_two_of_pow_dvd`
  (`(X - det M)^n ∣ χ(Φ₃)` over `ℚ` forces `n ≤ 2`, from the explicit `χ(Φ₃)` over `ℂ`,
  `Psc.LieWeights.charpoly_phi3Lie_explicit`, and `weights_ne_det`: no non-scalar weight
  equals `βαγ`); `finrank_ker_sub_det_le_two`: `dim_ℚ ker (Φ₃ - det M) ≤ 2`;
  **`finrank_ker_sub_det_eq_two`**: `= 2`, since `(X − det M)² ∣ χ(Φ₃)` over `ℚ` (from `ℂ`,
  `Polynomial.map_dvd_map`), the maximal generalized eigenspace has the root multiplicity
  as dimension (`LinearMap.finrank_maxGenEigenspace_eq`), and it is `ker (Φ₃ − det M)` by
  `phi3Lie_sub_smul_of_pow`.
* **The core, matrix form** (`M` rational, `χ_M` irreducible, `‖α‖, ‖γ‖ < 1`,
  `1 ≤ |det M|`, `W ⊆ Lie₃(ℚ³)` a `Φ₃`-invariant rational subspace whose `χ(Φ₃|_W)` has all
  complex roots of modulus `≤ ‖β‖`):
  (a) `root_restrict_eq_det`: every complex root of `χ(Φ₃|_W)` is `det M`
  (`Psc.SectorBridge.root_phi3Lie_of_roots` and `shape3_root_eq`);
  (b) `charpoly_restrict_eq_pow`: `χ(Φ₃|_W) = (X - det M)^{dim W}`;
  (c) `le_ker_sub_det`: `W ⊆ ker (Φ₃ - det M)` over `ℚ` (Cayley–Hamilton with (b), then
  `phi3Lie_sub_smul_of_pow` with the diagonalization `Psc.SectorBridge.exists_conj_diagonal`);
  (d) `finrank_le_two`: `dim W ≤ 2` over `ℚ`, from `(X - det M)^{dim W} ∣ χ(Φ₃)` (by (b))
  and `le_two_of_pow_dvd`; no transport of dimensions from `ℂ` to `ℚ` is needed.
  The converse `bound_of_le_ker` (no irreducibility, no `|det M| ≥ 1`) and
  `bound_iff_le_ker`: **`W` satisfies the bound iff `W ⊆ ker (Φ₃ - det M)`**.
* **On representatives** (`thm:deg23` (iii) itself; every state `Equiv2`, i.e.
  `K₁ = K₂ = 0`; `χ_M` irreducible; `‖α‖, ‖γ‖ < 1`; the bound `hbound`: every complex root of
  `χ_S` has modulus `≤ ‖β‖`):  `q3_eq_resCharpoly` (`q₃` is `resCharpoly` at `W = im Q₃`,
  by `rfl`); `one_le_abs_det_incQ` (`|det M| ≥ 1` is derived, not assumed); `bound_q3` (roots
  of `q₃` are roots of `χ_S`, `Psc.SectorBridge.q3_dvd_ssign`);
  (a) `root_q3_eq_det`; (b) `q3_eq_pow`: `q₃ = (X - det M)^{rank Q₃}`;
  (c) `range_q3m_le_ker`: `im Q₃ ⊆ ker (Φ₃ - det M)` over `ℚ`, and its column form
  `phi3_k3Vec_eq_det`: `M^{⊗3} K₃(T) = det M · K₃(T)` for every representative `T`
  (`phi3_k3Vec_of_le_ker`); (d) `rank_q3_le_two`; all four in `deg23_iii`.
  `deg23_iii_of_ne`: with a nonzero column (`r(C) = 3`), `1 ≤ rank Q₃ ≤ 2` and `det M` is a
  root of `χ_S`.
* **`hbound` discharged.**  `roots_ssign_le`: `ρ(S) ≤ b` as a bound on the **roots** of
  `χ_S`, from the eigenvector form `Psc.SignedCocycle.Normalisation.cocycle_spectral_bound_rep`
  (positive `ℓ`, `ℓ M = bℓ`, balanced states); `perron_eq_root`: in the setting above such a
  `b` **is** `β` (it is a root of `χ_M` of maximal modulus, and `b ∈ {α, γ}` would give
  `‖βαγ‖ < 1`); `deg23_iii_of_perron`: the four steps with `hbound` replaced by a positive
  left eigenvector (`b` not assumed to be a root, nor distinct from `α, γ`);
  **`deg23_iii_of_primitive`**: for a primitive `σ = S.s` the hypothesis `hbound` is dropped
  altogether (`Psc.PerronExistence.perron_inc`), and `β` is the Perron root.
* **Controls.**
  - Matrix level, every hypothesis of the core: `m0_control` (`Psc.M0Pisot.M0`,
    `χ = x³ − 32x² + 5x + 2` irreducible, real roots in `(-1,0)`, `(0,1)`, `(1,32)`,
    `det M0 = -2`, with `W₀ = ℚ·K₃(T13) ≠ 0`, `T13` the `∼₂` pair of
    `Psc.ConcentrationControls`; `m0_phi3_t13` is `t13_det_sector` cast to `ℚ`), and
    `m0_W0_charpoly`: there (b) reads `χ(Φ₃|_{W₀}) = X + 2`.
  - Negative, the bound is needed: `m0_bound_needed`: `W = Lie₃(ℚ³)` is invariant, `M0`
    meets every other hypothesis, `dim W = 8`, `W ⊄ ker (Φ₃ - det M0)`, and for every
    admissible `β, α, γ` some root of `χ(Φ₃(M0)|_W)` has modulus `> ‖β‖`.
  - Degenerate full control of the representative theorems: `census_empty_control` (the
    empty child system over `censusSubst = (0 ↦ 011, 1 ↦ 2, 2 ↦ 120)`, primitive with
    irreducible Pisot `χ_M = X³ − 2X² − 1`, `det M = 1`: every hypothesis of `deg23_iii`,
    `deg23_iii_of_perron`, `deg23_iii_of_primitive` holds, `χ_S = 1`, `im Q₃ = 0`).
  - **Content control from the census** (`comp:defect`): `census_not_mem`: the length-9
    census state `(011212001, 120011120)` (`census_state`: `∼₂`, `K₃ ≠ 0`, and
    `M^{⊗3} K₃ ≠ c K₃` for every `c`) lies in **no** child system over `censusSubst` that
    has a normalisation and only `∼₂` states.  It uses `deg23_iii_of_primitive` with every
    matrix hypothesis discharged (`census_irreducible`, `censusSubst_primitive`,
    `census_pisot`, via `census_other`: the complex pair has `‖z‖² = b² − 2b = 1/b`).
    `Psc.Degree3Catalogue.catalogue_spec` extends it to all 24 catalogue occurrences.
  - State level: `wT_conclusions` (`Psc.SignedIntertwiner.wT`, the identity substitution,
    `Equiv2` states, `K₃ ≠ 0`): the conclusions hold with `rank Q₃ = 1`; weak, since `M = 1`
    (`χ_M` reducible, `Psc.KernelCofactor.wT_not_irreducible`; `Φ₃ = 1`).
  - Negative, the Galois/Pisot hypotheses are needed: `cyc3_negative`
    (`Psc.SectorBridge.cyc3Norm`, the 3-cycle relabelling: `Equiv2` states, a nonzero
    column, three distinct roots `1, ζ, ζ²`, `|det M| = 1`, and the bound with `β = 1`,
    `cyc3_bound`) fails (c): `M^{⊗3} K₃(wTPair)` is `2` at `(2,0,2)` where
    `det M · K₃(wTPair) = -2`.  There `χ_M = X³ - 1` is reducible (`cycM_not_irreducible`)
    and `‖ζ‖ = ‖ζ²‖ = 1`; the control does not separate these two failures.

## Not proved here

* **No non-degenerate full control** of the representative theorems is known or expected:
  a normalised child system over three letters with `Equiv2` states, a nonzero `K₃` column,
  irreducible Pisot `χ_M` and `ρ(S) ≤ β` is what `thm:deg23` (iii) constrains, a
  hypothetical strict component with first defect degree three (manuscript, Open Problem
  `prob:concentration`, line 787).  `root_q3_eq_det`, `q3_eq_pow`, `range_q3m_le_ker`,
  `rank_q3_le_two`, `deg23_iii`, `deg23_iii_of_ne`, `deg23_iii_of_perron`,
  `deg23_iii_of_primitive` are **reductio lemmas**: necessary conditions on such a component.
  Their hypotheses are jointly satisfiable only degenerately (`census_empty_control`,
  `im Q₃ = 0`); the matrix-form core has the full control `m0_control`; the state
  hypotheses with `K₃ ≠ 0` are met by `wT` and `cyc3Norm`, whose `χ_M` are reducible.
  On a strict system they are restated with every structural hypothesis discharged as
  `Psc.StrictSystem.StrictSystem.deg23_iii` (`StrictComponent.deg23_iii`); the leave-one-out
  table of their hypotheses is `Psc.ReductioControls` (`degree3Sector_leave_one_out`).
* **The census beyond one state.**  `census_not_mem` covers the single state
  `(011212001, 120011120)` over the single substitution `censusSubst`.  The other 23 census
  states, their reachability and recurrence in `B_σ`, their leak pattern and the exact
  vertex sets of the twelve automata are `Psc.Degree3Catalogue` (`catalogue_spec`,
  `catalogue_exact`, `catalogue_card`, `no_closed_equiv2`; the length-21 inflation of the
  first length-9 class over `censusSubst` is `class9a_sigmaA_control`), which supersedes the
  scratch inflation checks this docstring used to cite.  That the 24 are all the degree-three
  states of the 4,554-member corpus remains the Mojo census `kernel/degree3_catalog.mojo`.
* `r(C) = 3` as the first-defect selection: the hypothesis is `Equiv2` on every state (as in
  `Psc.SectorBridge`), and a nonzero column is used only in `deg23_iii_of_ne`; strictness of
  the component (closure, reachability, recurrence) is not used.
* The bound `hbound` is derived only from a positive left eigenvector of `M`
  (`deg23_iii_of_perron`), in particular for primitive `σ` (`deg23_iii_of_primitive`); for a
  non-primitive `σ` without one it remains a hypothesis.
* The manuscript's route through the Galois-stable rational constituents of the non-scalar
  part ("one sextic factor or two cubic factors") is not formalized; it is replaced by the
  Galois-orbit step on the roots of `q₃` (`shape3_root_eq`).  Semisimplicity is proved in
  the kernel form `ker (Φ₃ - μ)^k = ker (Φ₃ - μ)`, not as `Module.End.IsSemisimple`.
* Degrees `r ≥ 4` (`thm:sieve`) and other alphabets.
-/

namespace Psc.Degree3Sector

open Matrix Polynomial Psc.LieWeights Psc.SectorBridge

/-! ### Modulus and Galois steps for the `(2,1,0)` orbit -/

section Weight

/-- `1 < ‖βα‖` from `‖γ‖ < 1 ≤ ‖βαγ‖` (no bound `1 < ‖β‖` is used). -/
theorem one_lt_norm_mul {β α γ : ℂ} (hγ1 : ‖γ‖ < 1) (hdet : 1 ≤ ‖β * α * γ‖) :
    1 < ‖β * α‖ := by
  rw [norm_mul (β * α) γ] at hdet
  by_contra h
  push Not at h
  nlinarith [mul_nonneg (sub_nonneg.2 h) (norm_nonneg γ), norm_nonneg (β * α)]

/-- **The `(2,1,0)` moduli.**  If `‖α‖, ‖γ‖ < 1 ≤ ‖βαγ‖`, then `‖β‖ < ‖β²δ‖` for
`δ ∈ {α, γ}`: `‖β²δ‖ = ‖β‖ ‖βδ‖` and `‖βδ‖ > 1` (`one_lt_norm_mul`). -/
theorem norm_lt_norm_sq_mul {β α γ δ : ℂ} (hα1 : ‖α‖ < 1) (hγ1 : ‖γ‖ < 1)
    (hdet : 1 ≤ ‖β * α * γ‖) (hδ : δ = α ∨ δ = γ) : ‖β‖ < ‖β ^ 2 * δ‖ := by
  have hβ0 : 0 < ‖β‖ := by
    refine norm_pos_iff.2 fun h0 => ?_
    rw [h0] at hdet
    simp at hdet
    linarith
  have hδ1 : 1 < ‖β * δ‖ := by
    rcases hδ with rfl | rfl
    · exact one_lt_norm_mul hγ1 hdet
    · exact one_lt_norm_mul hα1 (by rw [show β * δ * α = β * α * δ by ring]; exact hdet)
  have e : ‖β ^ 2 * δ‖ = ‖β‖ * ‖β * δ‖ := by
    rw [show β ^ 2 * δ = β * (β * δ) by ring, norm_mul]
  rw [e]
  exact lt_mul_of_one_lt_right hβ0 hδ1

section Orbit
variable {f : ℚ[X]} (hf : Irreducible f) (hdeg : f.natDegree = 3) {β α γ : ℂ}
    (hβ : aeval β f = 0) (hα : aeval α f = 0) (hγ : aeval γ f = 0)
    (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ)
include hf hdeg hβ hα hγ hβα hβγ hαγ

/-- **The `(2,1,0)` orbit reaches `β²δ`.**  If the rational `q` vanishes at a weight of
shape `(2,1,0)` (any of the six permutations), it vanishes at `β²δ` for some
`δ ∈ {α, γ}` (`Psc.GaloisOrbit.orbit_exponent_on_beta`). -/
theorem orbit_210_root (q : ℚ[X]) (a b c : ℕ)
    (habc : (a, b, c) = (2, 1, 0) ∨ (a, b, c) = (2, 0, 1) ∨ (a, b, c) = (1, 2, 0) ∨
      (a, b, c) = (0, 2, 1) ∨ (a, b, c) = (1, 0, 2) ∨ (a, b, c) = (0, 1, 2))
    (hq : aeval (β ^ a * α ^ b * γ ^ c) q = 0) :
    ∃ δ : ℂ, (δ = α ∨ δ = γ) ∧ aeval (β ^ 2 * δ) q = 0 := by
  have h1 := Psc.GaloisOrbit.orbit_exponent_on_beta hf hdeg hβ hα hγ hβα hβγ hαγ q a b c hq
  rcases habc with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl, rfl⟩ := h
  · exact ⟨α, Or.inl rfl, Psc.GaloisOrbit.of_eq (by ring1) hq⟩
  · exact ⟨γ, Or.inr rfl, Psc.GaloisOrbit.of_eq (by ring1) hq⟩
  · obtain ⟨x, y, hxy, hm⟩ := h1.1
    exact ⟨x, hxy.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1), Psc.GaloisOrbit.of_eq (by ring1) hm⟩
  · obtain ⟨x, y, hxy, hm⟩ := h1.1
    exact ⟨y, hxy.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2), Psc.GaloisOrbit.of_eq (by ring1) hm⟩
  · obtain ⟨x, y, hxy, hm⟩ := h1.2
    exact ⟨x, hxy.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1), Psc.GaloisOrbit.of_eq (by ring1) hm⟩
  · obtain ⟨x, y, hxy, hm⟩ := h1.2
    exact ⟨y, hxy.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2), Psc.GaloisOrbit.of_eq (by ring1) hm⟩

/-- **A degree-three weight root under the spectral bound is `βαγ`.**  If the rational
`q` vanishes at `x^κ` (`x = (β, α, γ)`, `κ` of shape `(2,1,0)` or `(1,1,1)`) and every
complex root of `q` has modulus `≤ ‖β‖`, then `x^κ = βαγ`: a `(2,1,0)` weight would give
the root `β²δ` of modulus `> ‖β‖` (`orbit_210_root`, `norm_lt_norm_sq_mul`). -/
theorem shape3_root_eq (hα1 : ‖α‖ < 1) (hγ1 : ‖γ‖ < 1) (hdet : 1 ≤ ‖β * α * γ‖) (q : ℚ[X])
    (hbound : ∀ z : ℂ, aeval z q = 0 → ‖z‖ ≤ ‖β‖) {κ : Fin 3 → ℕ} (hκ : Shape3 κ)
    (hq : aeval (mono ![β, α, γ] κ) q = 0) : mono ![β, α, γ] κ = β * α * γ := by
  rw [mono_fin_three] at hq ⊢
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hq ⊢
  rcases hκ.triple with h | h
  · obtain ⟨δ, hδ, hz⟩ := orbit_210_root hf hdeg hβ hα hγ hβα hβγ hαγ q _ _ _ h hq
    exact absurd (hbound _ hz) (not_le.2 (norm_lt_norm_sq_mul hα1 hγ1 hdet hδ))
  · simp only [Prod.mk.injEq] at h
    rw [h.1, h.2.1, h.2.2]
    ring

end Orbit

end Weight

/-! ### Algebraic helpers: roots, determinant, scalar polynomials -/

section Helpers

/-- Three moduli `< 1` give `‖βαγ‖ < 1`. -/
theorem norm_mul_lt_one {β α γ : ℂ} (hβ1 : ‖β‖ < 1) (hα1 : ‖α‖ < 1) (hγ1 : ‖γ‖ < 1) :
    ‖β * α * γ‖ < 1 := by
  rw [norm_mul, norm_mul]
  have h : ‖β‖ * ‖α‖ < 1 := by nlinarith [norm_nonneg β, norm_nonneg α]
  nlinarith [mul_nonneg (norm_nonneg β) (norm_nonneg α), norm_nonneg γ]

/-- **An integral `M` with irreducible `χ_M` has `|det M| ≥ 1`**: the determinant is a
nonzero integer (`Psc.Cyclicity.det_ne_zero_of_irreducible`). -/
theorem one_le_abs_det (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hM : Irreducible (A.map (Int.cast : ℤ → ℚ)).charpoly) :
    1 ≤ |(A.map (Int.cast : ℤ → ℚ)).det| := by
  have h := RingHom.map_det (Int.castRingHom ℚ) A
  have hA : (Int.castRingHom ℚ).mapMatrix A = A.map (Int.cast : ℤ → ℚ) := rfl
  rw [hA] at h
  have h0 := Psc.Cyclicity.det_ne_zero_of_irreducible _ hM
  rw [← h] at h0 ⊢
  have hz : A.det ≠ 0 := fun hz => h0 (by rw [hz, map_zero])
  rw [eq_intCast, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs hz

/-- **A rational polynomial whose complex roots all equal `d` is a power of `X - d`**
(it splits over `ℂ`; the map `ℚ[X] → ℂ[X]` is injective). -/
theorem eq_X_sub_C_pow_of_roots {p : ℚ[X]} (hp : p.Monic) (d : ℚ)
    (h : ∀ z : ℂ, aeval z p = 0 → z = (d : ℂ)) : p = (X - C d) ^ p.natDegree := by
  set p' := p.map (algebraMap ℚ ℂ) with hp'
  have hm : p'.Monic := hp.map _
  have hs : p'.Splits := IsAlgClosed.splits p'
  have hroots : p'.roots = Multiset.replicate p'.natDegree (d : ℂ) := by
    rw [Multiset.eq_replicate]
    refine ⟨IsAlgClosed.card_roots_eq_natDegree, fun z hz => h z ?_⟩
    rw [mem_roots hm.ne_zero, IsRoot.def, hp', eval_map_algebraMap] at hz
    exact hz
  have key : p' = ((X - C d) ^ p.natDegree).map (algebraMap ℚ ℂ) := by
    rw [hs.eq_prod_roots_of_monic hm, hroots, Multiset.map_replicate, Multiset.prod_replicate,
      Polynomial.map_pow, Polynomial.map_sub, map_X, map_C, hp', natDegree_map, eq_ratCast]
  exact map_injective _ (algebraMap ℚ ℂ).injective key

/-- The characteristic polynomial of a scalar endomorphism: `χ(c • 1) = (X - c)^{dim}`. -/
theorem charpoly_smul_one {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (c : K) :
    (c • (1 : Module.End K V)).charpoly = (X - C c) ^ Module.finrank K V := by
  set b := Module.finBasis K V
  rw [← LinearMap.charpoly_toMatrix _ b, map_smul, LinearMap.toMatrix_one,
    Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

end Helpers

/-! ### Semisimplicity of the rational `Φ₃`: `ker (Φ₃ - μ)^k = ker (Φ₃ - μ)` -/

section Semisimple

/-- **An endomorphism with an eigenbasis is semisimple, kernel form**:
`(T - μ)^k v = 0 ⇒ (T - μ) v = 0`.  In the eigenbasis the coordinates of `(T - μ)^m v`
are `(wᵢ - μ)^m vᵢ`. -/
theorem sub_smul_eq_zero_of_pow {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] (b : Module.Basis ι F V) {T : Module.End F V} {w : ι → F}
    (hT : ∀ i, T (b i) = w i • b i) (μ : F) (k : ℕ) {v : V}
    (hv : ((T - μ • 1) ^ k) v = 0) : (T - μ • 1) v = 0 := by
  have hD : ∀ m : ℕ, ∀ i, ((T - μ • 1) ^ m) (b i) = (w i - μ) ^ m • b i := by
    intro m i
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, hT,
        LinearMap.smul_apply, Module.End.one_apply, ← sub_smul, smul_smul, pow_succ]
  have hexp : ∀ m : ℕ, ((T - μ • 1) ^ m) v = ∑ i, ((w i - μ) ^ m * b.repr v i) • b i := by
    intro m
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hD, smul_smul, mul_comm]
  have hc : ∀ i, (w i - μ) ^ k * b.repr v i = 0 := by
    intro i
    have h := congrArg (fun u => b.repr u i) ((hexp k).symm.trans hv)
    simp only [Module.Basis.repr_sum_self, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h
    exact h
  have h1 := hexp 1
  rw [pow_one] at h1
  rw [h1]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases eq_or_ne (w i - μ) 0 with h | h
  · simp [h]
  · have : b.repr v i = 0 := (mul_eq_zero.1 (hc i)).resolve_left (pow_ne_zero _ h)
    simp [this]

/-- The powers of `T|_p - μ` are the restrictions of the powers of `T - μ`. -/
theorem coe_pow_restrict_sub_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) {p : Submodule K V} (hp : ∀ v ∈ p, T v ∈ p) (μ : K) (m : ℕ) (w : p) :
    (((T.restrict hp - μ • 1) ^ m) w : V) = ((T - μ • 1) ^ m) (w : V) := by
  induction m generalizing w with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
    congr 1

theorem coe_pow_phi3Lie_sub {F : Type*} [Field F] [CharZero F] (M : Matrix (Fin 3) (Fin 3) F)
    (μ : F) (m : ℕ) (w : Submodule.span F (Set.range (Lie3.lyndon (R := F)))) :
    (((phi3Lie M - μ • 1) ^ m) w : Lie3.Vec3 F) = ((Phi3 M - μ • 1) ^ m) (w : Lie3.Vec3 F) :=
  coe_pow_restrict_sub_smul (Phi3 M) _ μ m w

theorem map3_smul {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (c : R)
    (f : Lie3.Vec3 R) : Lie3.map3 φ (c • f) = φ c • Lie3.map3 φ f := by
  funext a b e; simp [Lie3.map3]

theorem map3_eq_zero {R S : Type*} [CommRing R] [CommRing S] {φ : R →+* S}
    (hφ : Function.Injective φ) {f : Lie3.Vec3 R} (h : Lie3.map3 φ f = 0) : f = 0 := by
  funext a b e
  exact (map_eq_zero_iff φ hφ).1 (congrFun (congrFun (congrFun h a) b) e)

/-- Base change of `(M^{⊗3} - μ)^m` along a ring homomorphism (`Psc.Lie3.phi3_map`). -/
theorem map3_pow_sub_smul {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (M : Matrix (Fin 3) (Fin 3) R) (μ : R) (m : ℕ) (f : Lie3.Vec3 R) :
    Lie3.map3 φ (((Phi3 M - μ • 1) ^ m) f) = ((Phi3 (M.map φ) - φ μ • 1) ^ m) (Lie3.map3 φ f) := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
    congr 1
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Phi3_apply,
      Lie3.map3_sub, map3_smul, Lie3.phi3_map]

/-- **Semisimplicity of the rational `Φ₃`, kernel form.**  If the rational `M` is
`Q (diag x) Q⁻¹` over some field `L` of characteristic zero, then on `Lie₃(ℚ³)`
`(Φ₃ - μ)^k v = 0 ⇒ (Φ₃ - μ) v = 0` for every rational `μ`: base-change `v` to `L`, where
`Φ₃` has the Lyndon eigenbasis (`Psc.LieWeights.exists_eigenbasis_phi3Lie`), apply
`sub_smul_eq_zero_of_pow`, and come back (`map3` is injective). -/
theorem phi3Lie_sub_smul_of_pow (M : Matrix (Fin 3) (Fin 3) ℚ) {L : Type*} [Field L] [CharZero L]
    (Q : Matrix (Fin 3) (Fin 3) L) (x : Fin 3 → L) (hQ : IsUnit Q.det)
    (hMQ : M.map (algebraMap ℚ L) = Q * Matrix.diagonal x * Q⁻¹) (μ : ℚ) (k : ℕ) {v : Lie3Q}
    (hv : ((phi3Lie M - μ • 1) ^ k) v = 0) : (phi3Lie M - μ • 1) v = 0 := by
  set φ := algebraMap ℚ L
  obtain ⟨b, hb⟩ := exists_eigenbasis_phi3Lie (M.map φ) Q x hQ hMQ
  have hmem : Lie3.map3 φ (v : Lie3.Vec3 ℚ) ∈ Submodule.span L (Set.range (Lie3.lyndon (R := L))) :=
    (Lie3.shuffleAnnih_iff_mem_span _).1 (((Lie3.shuffleAnnih_iff_mem_span _).2 v.2).map φ)
  set v' : Submodule.span L (Set.range (Lie3.lyndon (R := L))) := ⟨_, hmem⟩ with hv'def
  have hv0 : (((Phi3 M - μ • 1) ^ k) (v : Lie3.Vec3 ℚ)) = 0 := by
    rw [← coe_pow_phi3Lie_sub, hv, Submodule.coe_zero]
  have hv' : ((phi3Lie (M.map φ) - φ μ • 1) ^ k) v' = 0 := by
    apply Subtype.ext
    rw [coe_pow_phi3Lie_sub, hv'def, ← map3_pow_sub_smul, hv0, Submodule.coe_zero]
    funext a b e; simp [Lie3.map3]
  have h1 := congrArg Subtype.val (sub_smul_eq_zero_of_pow b hb (φ μ) k hv')
  have h1' := coe_pow_phi3Lie_sub (M.map φ) (φ μ) 1 v'
  rw [pow_one] at h1'
  rw [h1', Submodule.coe_zero, hv'def] at h1
  have h2 := map3_pow_sub_smul φ M μ 1 (v : Lie3.Vec3 ℚ)
  rw [pow_one, pow_one] at h2
  apply Subtype.ext
  have h3 := coe_pow_phi3Lie_sub M μ 1 v
  rw [pow_one] at h3
  rw [h3, Submodule.coe_zero]
  exact map3_eq_zero φ.injective (h2.trans h1)

end Semisimple

/-! ### The core: a rational `Φ₃`-invariant subspace under the spectral bound -/

section Core

/-- The characteristic polynomial of `φ|_W` for a `φ`-invariant `W` (defined over an
arbitrary field, so that its instances are the generic ones; `Psc.SectorBridge.q3` is
`resCharpoly` of `Φ₃` at `W = im Q₃`, `q3_eq_resCharpoly`). -/
noncomputable def resCharpoly {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (φ : Module.End K V) {W : Submodule K V}
    (hW : ∀ v ∈ W, φ v ∈ W) : K[X] :=
  (φ.restrict hW).charpoly

section Restrict

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (φ : Module.End K V) {W : Submodule K V} (hW : ∀ v ∈ W, φ v ∈ W)

theorem resCharpoly_monic : (resCharpoly φ hW).Monic := LinearMap.charpoly_monic _

theorem resCharpoly_natDegree : (resCharpoly φ hW).natDegree = Module.finrank K W :=
  LinearMap.charpoly_natDegree _

theorem resCharpoly_dvd : resCharpoly φ hW ∣ φ.charpoly := charpoly_restrict_dvd φ W hW

/-- **Cayley–Hamilton on `W`, power form**: if `χ(φ|_W) = (X - c)^n`, then
`(φ - c)^n` vanishes on `W`. -/
theorem pow_sub_smul_apply_eq_zero (c : K) (n : ℕ) (h : resCharpoly φ hW = (X - C c) ^ n)
    {v : V} (hv : v ∈ W) : ((φ - c • 1) ^ n) v = 0 := by
  have hCH := LinearMap.aeval_self_charpoly (φ.restrict hW)
  rw [show (φ.restrict hW).charpoly = resCharpoly φ hW from rfl, h, map_pow, map_sub, aeval_X,
    aeval_C, Algebra.algebraMap_eq_smul_one] at hCH
  have h1 := coe_pow_restrict_sub_smul φ hW c n ⟨v, hv⟩
  rw [hCH] at h1
  simpa using h1.symm

/-- **No hypothesis on `φ`**: if `φ = c` on the invariant subspace `W`, then
`χ(φ|_W) = (X - c)^{dim W}`. -/
theorem resCharpoly_of_le_ker (c : K) (hle : W ≤ LinearMap.ker (φ - c • 1)) :
    resCharpoly φ hW = (X - C c) ^ Module.finrank K W := by
  have h : φ.restrict hW = c • 1 := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    have hw := LinearMap.mem_ker.1 (hle w.2)
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hw
    rw [LinearMap.coe_restrict_apply, hw]
    rfl
  rw [resCharpoly, h, charpoly_smul_one]

omit [FiniteDimensional K V] in
/-- A subspace of `ker (φ - c)` is `φ`-invariant. -/
theorem invariant_of_le_ker {W : Submodule K V} (c : K) (hle : W ≤ LinearMap.ker (φ - c • 1)) :
    ∀ v ∈ W, φ v ∈ W := by
  intro v hv
  have h := LinearMap.mem_ker.1 (hle hv)
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
  rw [h]
  exact W.smul_mem c hv

end Restrict

/-- The six non-scalar weights of `Φ₃` differ from `βαγ`: `βαγ - β²α = βα(γ - β)`, etc. -/
theorem weights_ne_det {β α γ : ℂ} (h0 : β * α * γ ≠ 0) (hβα : β ≠ α) (hβγ : β ≠ γ)
    (hαγ : α ≠ γ) :
    (β * α * γ - β ^ 2 * α) * (β * α * γ - β ^ 2 * γ) * (β * α * γ - β * α ^ 2) *
      (β * α * γ - β * γ ^ 2) * (β * α * γ - α ^ 2 * γ) * (β * α * γ - α * γ ^ 2) ≠ 0 := by
  have hβ : β ≠ 0 := fun h => h0 (by rw [h]; ring)
  have hα : α ≠ 0 := fun h => h0 (by rw [h]; ring)
  have hγ : γ ≠ 0 := fun h => h0 (by rw [h]; ring)
  have e : (β * α * γ - β ^ 2 * α) * (β * α * γ - β ^ 2 * γ) * (β * α * γ - β * α ^ 2) *
      (β * α * γ - β * γ ^ 2) * (β * α * γ - α ^ 2 * γ) * (β * α * γ - α * γ ^ 2) =
      (β * α * (γ - β)) * (β * γ * (α - β)) * (β * α * (γ - α)) * (β * γ * (α - γ)) *
        (α * γ * (β - α)) * (α * γ * (β - γ)) := by ring
  rw [e]
  have s1 := sub_ne_zero.2 hβα
  have s2 := sub_ne_zero.2 hβγ
  have s3 := sub_ne_zero.2 hαγ
  have s4 := sub_ne_zero.2 hβα.symm
  have s5 := sub_ne_zero.2 hβγ.symm
  have s6 := sub_ne_zero.2 hαγ.symm
  repeat' apply mul_ne_zero
  all_goals assumption

/-- **The multiplicity of `det M` as a root of `χ(Φ₃)` is at most two.**  If
`(X - det M)^n ∣ χ(Φ₃)` over `ℚ`, for three pairwise distinct complex roots `β, α, γ` of
`χ_M` and `det M ≠ 0`, then `n ≤ 2`: over `ℂ`,
`χ(Φ₃) = (six non-scalar factors) · (X - det M)²`
(`Psc.LieWeights.charpoly_phi3Lie_explicit`, `charpoly_phi3Lie_map`), and no non-scalar
factor vanishes at `det M = βαγ` (`weights_ne_det`). -/
theorem le_two_of_pow_dvd {M : Matrix (Fin 3) (Fin 3) ℚ} {β α γ : ℂ}
    (hβ : aeval β M.charpoly = 0) (hα : aeval α M.charpoly = 0) (hγ : aeval γ M.charpoly = 0)
    (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ) (hdet0 : M.det ≠ 0) {n : ℕ}
    (hdvd : (X - C M.det) ^ n ∣ (phi3Lie M).charpoly) : n ≤ 2 := by
  obtain ⟨Q, hQ, hMQ⟩ :=
    exists_conj_diagonal M ![β, α, γ] (vec3_injective hβα hβγ hαγ) (vec3_roots hβ hα hγ)
  have hd : algebraMap ℚ ℂ M.det = β * α * γ := by
    rw [eq_ratCast]; exact det_eq_mul_roots M hβ hα hγ hβα hβγ hαγ
  have hdM : (M.map (algebraMap ℚ ℂ)).det = β * α * γ := by
    rw [← hd, RingHom.map_det, RingHom.mapMatrix_apply]
  have hdvd' := Polynomial.map_dvd (algebraMap ℚ ℂ) hdvd
  rw [Polynomial.map_pow, Polynomial.map_sub, map_X, map_C, hd, ← charpoly_phi3Lie_map,
    charpoly_phi3Lie_explicit _ Q _ hQ hMQ, hdM] at hdvd'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hdvd'
  by_contra hn
  push Not at hn
  have h3 := (pow_dvd_pow (X - C (β * α * γ)) hn).trans hdvd'
  rw [pow_succ, mul_comm _ ((X - C (β * α * γ)) ^ 2)] at h3
  have h4 := (mul_dvd_mul_iff_left (pow_ne_zero 2 (X_sub_C_ne_zero (β * α * γ)))).1 h3
  rw [dvd_iff_isRoot, IsRoot.def] at h4
  simp only [eval_mul, eval_sub, eval_X, eval_C] at h4
  have h0 : β * α * γ ≠ 0 := by
    rw [← det_eq_mul_roots M hβ hα hγ hβα hβγ hαγ]; exact_mod_cast hdet0
  exact weights_ne_det h0 hβα hβγ hαγ h4

/-- **The rational `det M`-eigenspace of `Φ₃` has dimension at most two**, for any rational
`M` with three pairwise distinct complex eigenvalues and `det M ≠ 0` (no irreducibility, no
modulus hypothesis): on `E = ker (Φ₃ - det M)`, `χ(Φ₃|_E) = (X - det M)^{dim E}`
(`resCharpoly_of_le_ker`) divides `χ(Φ₃)`, and `le_two_of_pow_dvd`.  The rational upper
half of `Psc.LieWeights.finrank_ker_phi3Lie_sub_det` (which is over a field containing the
eigenvalues). -/
theorem finrank_ker_sub_det_le_two {M : Matrix (Fin 3) (Fin 3) ℚ} {β α γ : ℂ}
    (hβ : aeval β M.charpoly = 0) (hα : aeval α M.charpoly = 0) (hγ : aeval γ M.charpoly = 0)
    (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ) (hdet0 : M.det ≠ 0) :
    Module.finrank ℚ (LinearMap.ker (phi3Lie M - M.det • 1)) ≤ 2 := by
  have hE := invariant_of_le_ker (phi3Lie M) M.det le_rfl
  refine le_two_of_pow_dvd hβ hα hγ hβα hβγ hαγ hdet0 ?_
  rw [← resCharpoly_of_le_ker _ hE _ le_rfl]
  exact resCharpoly_dvd _ hE

/-- **The rational `det M`-eigenspace of `Φ₃` has dimension exactly two**, for a rational `M`
with three pairwise distinct complex eigenvalues and `det M ≠ 0` (no irreducibility, no
moduli): the multiplicity of `det M` as a root of the rational `χ(Φ₃)` is two (at most two by
`le_two_of_pow_dvd`; at least two since `(X − det M)² ∣ χ(Φ₃)` over `ℂ`,
`Psc.LieWeights.charpoly_phi3Lie_explicit`, hence over `ℚ` by `Polynomial.map_dvd_map`), the
maximal generalized `det M`-eigenspace has that dimension
(`LinearMap.finrank_maxGenEigenspace_eq`), and it equals `ker (Φ₃ − det M)` by the kernel form
of semisimplicity `phi3Lie_sub_smul_of_pow`.  The rational form of
`Psc.LieWeights.finrank_ker_phi3Lie_sub_det`. -/
theorem finrank_ker_sub_det_eq_two {M : Matrix (Fin 3) (Fin 3) ℚ} {β α γ : ℂ}
    (hβ : aeval β M.charpoly = 0) (hα : aeval α M.charpoly = 0) (hγ : aeval γ M.charpoly = 0)
    (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ) (hdet0 : M.det ≠ 0) :
    Module.finrank ℚ (LinearMap.ker (phi3Lie M - M.det • 1)) = 2 := by
  obtain ⟨Q, hQ, hMQ⟩ :=
    exists_conj_diagonal M ![β, α, γ] (vec3_injective hβα hβγ hαγ) (vec3_roots hβ hα hγ)
  have hd : algebraMap ℚ ℂ M.det = β * α * γ := by
    rw [eq_ratCast]; exact det_eq_mul_roots M hβ hα hγ hβα hβγ hαγ
  have hdM : (M.map (algebraMap ℚ ℂ)).det = β * α * γ := by
    rw [← hd, RingHom.map_det, RingHom.mapMatrix_apply]
  have hdvd2 : (X - C M.det) ^ 2 ∣ (phi3Lie M).charpoly := by
    have hmon : ((X - C M.det) ^ 2 : ℚ[X]).Monic := (monic_X_sub_C _).pow 2
    rw [← Polynomial.map_dvd_map (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective hmon,
      Polynomial.map_pow, Polynomial.map_sub, map_X, map_C, hd, ← charpoly_phi3Lie_map,
      charpoly_phi3Lie_explicit _ Q _ hQ hMQ, hdM]
    exact dvd_mul_left _ _
  have hmult : (phi3Lie M).charpoly.rootMultiplicity M.det = 2 :=
    le_antisymm (le_two_of_pow_dvd hβ hα hγ hβα hβγ hαγ hdet0 (pow_rootMultiplicity_dvd _ _))
      ((le_rootMultiplicity_iff (LinearMap.charpoly_monic _).ne_zero).2 hdvd2)
  have hmax : (phi3Lie M).maxGenEigenspace M.det = LinearMap.ker (phi3Lie M - M.det • 1) := by
    apply le_antisymm
    · intro v hv
      obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
      exact LinearMap.mem_ker.2 (phi3Lie_sub_smul_of_pow M Q _ hQ hMQ M.det k hk)
    · intro v hv
      exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by simpa using hv⟩
  rw [← hmax, LinearMap.finrank_maxGenEigenspace_eq, hmult]

variable {M : Matrix (Fin 3) (Fin 3) ℚ} (hM : Irreducible M.charpoly) {β α γ : ℂ}
  (hβ : aeval β M.charpoly = 0) (hα : aeval α M.charpoly = 0) (hγ : aeval γ M.charpoly = 0)
  (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ) (hα1 : ‖α‖ < 1) (hγ1 : ‖γ‖ < 1)
  (hdet : 1 ≤ |M.det|) {W : Submodule ℚ Lie3Q} (hW : ∀ v ∈ W, phi3Lie M v ∈ W)

include hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 hdet

/-- **(a), matrix form.**  Every complex root of `χ(Φ₃|_W)`, for a rational
`Φ₃`-invariant `W ⊆ Lie₃(ℚ³)` whose roots have modulus `≤ ‖β‖`, equals `det M`: it is a
root of `χ(Φ₃)`, hence a weight of shape `(2,1,0)` or `(1,1,1)`
(`Psc.SectorBridge.root_phi3Lie_of_roots`), and `shape3_root_eq` excludes `(2,1,0)`. -/
theorem root_restrict_eq_det
    (hbound : ∀ z : ℂ, aeval z (resCharpoly (phi3Lie M) hW) = 0 → ‖z‖ ≤ ‖β‖) {z : ℂ}
    (hz : aeval z (resCharpoly (phi3Lie M) hW) = 0) : z = (M.det : ℂ) := by
  have hΦ : aeval z (phi3Lie M).charpoly = 0 :=
    aeval_eq_zero_of_dvd_aeval_eq_zero (resCharpoly_dvd _ hW) hz
  obtain ⟨κ, -, hκ, rfl⟩ := root_phi3Lie_of_roots M ![β, α, γ] (vec3_injective hβα hβγ hαγ)
    (vec3_roots hβ hα hγ) hΦ
  rw [det_eq_mul_roots M hβ hα hγ hβα hβγ hαγ]
  exact shape3_root_eq hM ((Matrix.charpoly_natDegree_eq_dim M).trans (Fintype.card_fin 3))
    hβ hα hγ hβα hβγ hαγ hα1 hγ1 (one_le_norm_mul_roots hβ hα hγ hβα hβγ hαγ hdet) _ hbound
    hκ hz

/-- **(b), matrix form.**  `χ(Φ₃|_W) = (X - det M)^{dim W}`. -/
theorem charpoly_restrict_eq_pow
    (hbound : ∀ z : ℂ, aeval z (resCharpoly (phi3Lie M) hW) = 0 → ‖z‖ ≤ ‖β‖) :
    resCharpoly (phi3Lie M) hW = (X - C M.det) ^ Module.finrank ℚ W := by
  have h := eq_X_sub_C_pow_of_roots (resCharpoly_monic _ hW) M.det fun z hz =>
    root_restrict_eq_det hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 hdet hW hbound hz
  rwa [resCharpoly_natDegree] at h

/-- **(c), matrix form: `W ⊆ ker (Φ₃ - det M)`.**  By (b) and Cayley–Hamilton,
`(Φ₃ - det M)^{dim W}` vanishes on `W`; `Φ₃` is semisimple (`phi3Lie_sub_smul_of_pow`,
with the diagonalization of `M` over `ℂ`), so `Φ₃ - det M` vanishes on `W`. -/
theorem le_ker_sub_det
    (hbound : ∀ z : ℂ, aeval z (resCharpoly (phi3Lie M) hW) = 0 → ‖z‖ ≤ ‖β‖) :
    W ≤ LinearMap.ker (phi3Lie M - M.det • 1) := by
  intro v hv
  obtain ⟨Q, hQ, hMQ⟩ :=
    exists_conj_diagonal M ![β, α, γ] (vec3_injective hβα hβγ hαγ) (vec3_roots hβ hα hγ)
  have h1 := pow_sub_smul_apply_eq_zero (phi3Lie M) hW M.det _
    (charpoly_restrict_eq_pow hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 hdet hW hbound) hv
  exact LinearMap.mem_ker.2 (phi3Lie_sub_smul_of_pow M Q ![β, α, γ] hQ hMQ M.det _ h1)

/-- **(d), matrix form: `dim W ≤ 2`.**  By (b), `(X - det M)^{dim W} ∣ χ(Φ₃)`, and the
multiplicity of `det M` in `χ(Φ₃)` is at most two (`le_two_of_pow_dvd`). -/
theorem finrank_le_two
    (hbound : ∀ z : ℂ, aeval z (resCharpoly (phi3Lie M) hW) = 0 → ‖z‖ ≤ ‖β‖) :
    Module.finrank ℚ W ≤ 2 := by
  refine le_two_of_pow_dvd hβ hα hγ hβα hβγ hαγ (fun h0 => ?_) ?_
  · rw [h0, abs_zero] at hdet
    linarith
  · rw [← charpoly_restrict_eq_pow hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 hdet hW hbound]
    exact resCharpoly_dvd _ hW

omit hM hdet in
/-- **The converse (no irreducibility, no `|det M| ≥ 1`)**: a `Φ₃`-invariant `W` inside
`ker (Φ₃ - det M)` satisfies the spectral bound, since its only eigenvalue is
`det M = βαγ` and `‖βαγ‖ ≤ ‖β‖`. -/
theorem bound_of_le_ker (hle : W ≤ LinearMap.ker (phi3Lie M - M.det • 1)) :
    ∀ z : ℂ, aeval z (resCharpoly (phi3Lie M) hW) = 0 → ‖z‖ ≤ ‖β‖ := by
  intro z hz
  rw [resCharpoly_of_le_ker _ hW _ hle, map_pow, map_sub, aeval_X, aeval_C] at hz
  rw [sub_eq_zero.1 (pow_eq_zero_iff'.1 hz).1, eq_ratCast,
    det_eq_mul_roots M hβ hα hγ hβα hβγ hαγ, norm_mul, norm_mul, mul_assoc]
  exact mul_le_of_le_one_right (norm_nonneg β)
    (by nlinarith [mul_nonneg (sub_nonneg.2 hα1.le) (norm_nonneg γ), norm_nonneg α])

/-- **`thm:deg23` (iii), matrix form, as an equivalence**: a rational `Φ₃`-invariant
`W ⊆ Lie₃(ℚ³)` has all its eigenvalues of modulus `≤ ‖β‖` iff `W ⊆ ker (Φ₃ - det M)`. -/
theorem bound_iff_le_ker :
    (∀ z : ℂ, aeval z (resCharpoly (phi3Lie M) hW) = 0 → ‖z‖ ≤ ‖β‖) ↔
      W ≤ LinearMap.ker (phi3Lie M - M.det • 1) :=
  ⟨le_ker_sub_det hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 hdet hW,
    bound_of_le_ker hβ hα hγ hβα hβγ hαγ hα1 hγ1 hW⟩

end Core

/-! ### `thm:deg23` (iii) on normalised representatives -/

section Rep

open Psc.Binomial Psc.SignedCocycle Psc.ParikhRank Psc.Degree2Sector Psc.Incidence

variable {S : ChildSystem (Fin 3)} (P : Normalisation S) (hbal : ∀ T ∈ S.C, Equiv2 T.1 T.2)

/-- `q₃ = χ(Φ₃|_{im Q₃})` is `resCharpoly` of `Φ₃` at `W = im Q₃`. -/
theorem q3_eq_resCharpoly :
    q3 P hbal = resCharpoly (phi3Lie (incQ S)) (range_invariant (q3m_intertwine P hbal)) :=
  rfl

omit P in
/-- **`|det M| ≥ 1` is automatic** for a child system with irreducible `χ_M`: `M` is
integral (`one_le_abs_det`). -/
theorem one_le_abs_det_incQ (hM : Irreducible (incQ S).charpoly) : 1 ≤ |(incQ S).det| := by
  have h : incQ S = ((inc S.s).map (Nat.cast : ℕ → ℤ)).map (Int.cast : ℤ → ℚ) := by
    ext i j; simp
  have h' := one_le_abs_det ((inc S.s).map (Nat.cast : ℕ → ℤ)) (by rw [← h]; exact hM)
  rwa [← h] at h'

/-- **`ρ(S) ≤ b` as a bound on the roots of `χ_S`** (`prop:cocycle`), for a positive left
eigenvector `ℓ M = b ℓ` (`b = β` in the setting of `deg23_iii`, `perron_eq_root`): from the
eigenvector form `Psc.SignedCocycle.Normalisation.cocycle_spectral_bound_rep`, since every
complex root of `χ_S` has a complex eigenvector
(`Psc.ConcentrationAlgebra.exists_eigenvector_of_isRoot`). -/
theorem roots_ssign_le (ℓ : Fin 3 → ℝ) (hℓ : ∀ a, 0 < ℓ a) (b : ℝ)
    (hℓN : ℓ ᵥ* (inc S.s).map (Nat.cast : ℕ → ℝ) = b • ℓ)
    (hbal1 : ∀ T ∈ S.C, Equiv1 T.1 T.2) :
    ∀ μ : ℂ, aeval μ (SsignQ P).charpoly = 0 → ‖μ‖ ≤ b :=
  ssign_root_bound_of_perron P _ (P.lrep_pos ℓ hℓ (P.top_ne_nil hbal1)) (P.rep_eigen ℓ b hℓN hbal1)

/-- If `im Q₃ ⊆ ker (Φ₃ - c)`, every column `K₃(T)`, `T ∈ R`, satisfies
`M^{⊗3} K₃(T) = c K₃(T)`. -/
theorem phi3_k3Vec_of_le_ker (c : ℚ)
    (hle : LinearMap.range (Q3m P hbal) ≤ LinearMap.ker (phi3Lie (incQ S) - c • 1))
    (j : P.Rep) : Lie3.phi3 (incQ S) (Lie3.k3Vec j.1.1 j.1.2) = c • Lie3.k3Vec j.1.1 j.1.2 := by
  have hj : k3Lie P hbal j ∈ LinearMap.range (Q3m P hbal) :=
    ⟨Pi.single j 1, by simp [Q3m]⟩
  have h := LinearMap.mem_ker.1 (hle hj)
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
  exact congrArg Subtype.val h

section Main

variable (hM : Irreducible (incQ S).charpoly) {β α γ : ℂ}
  (hβ : aeval β (incQ S).charpoly = 0) (hα : aeval α (incQ S).charpoly = 0)
  (hγ : aeval γ (incQ S).charpoly = 0) (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ)
  (hα1 : ‖α‖ < 1) (hγ1 : ‖γ‖ < 1)
  (hbound : ∀ μ : ℂ, aeval μ (SsignQ P).charpoly = 0 → ‖μ‖ ≤ ‖β‖)

include hbound in
/-- The roots of `q₃` are roots of `χ_S` (`Psc.SectorBridge.q3_dvd_ssign`), so they obey
the spectral bound. -/
theorem bound_q3 :
    ∀ z : ℂ, aeval z (resCharpoly (phi3Lie (incQ S)) (range_invariant (q3m_intertwine P hbal)))
      = 0 → ‖z‖ ≤ ‖β‖ :=
  fun z hz => hbound z (aeval_eq_zero_of_dvd_aeval_eq_zero (q3_dvd_ssign P hbal) hz)

include hbal hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 hbound

/-- **`thm:deg23` (iii), step (a)**: every complex root of `q₃` equals `det M`. -/
theorem root_q3_eq_det {z : ℂ} (hz : aeval z (q3 P hbal) = 0) : z = ((incQ S).det : ℂ) :=
  root_restrict_eq_det hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 (one_le_abs_det_incQ hM) _
    (bound_q3 P hbal hbound) hz

/-- **`thm:deg23` (iii), step (b)**: `q₃ = (X - det M)^k`, `k = dim im Q₃ = rank Q₃`. -/
theorem q3_eq_pow :
    q3 P hbal = (X - C (incQ S).det) ^ Module.finrank ℚ (LinearMap.range (Q3m P hbal)) :=
  charpoly_restrict_eq_pow hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 (one_le_abs_det_incQ hM) _
    (bound_q3 P hbal hbound)

/-- **`thm:deg23` (iii), step (c)**: `im Q₃ ⊆ ker (Φ₃ - det M)`, over `ℚ`. -/
theorem range_q3m_le_ker :
    LinearMap.range (Q3m P hbal) ≤ LinearMap.ker (phi3Lie (incQ S) - (incQ S).det • 1) :=
  le_ker_sub_det hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 (one_le_abs_det_incQ hM) _
    (bound_q3 P hbal hbound)

/-- **Step (c), column form**: every `K₃(T)`, `T ∈ R`, satisfies
`M^{⊗3} K₃(T) = det M · K₃(T)`, in the coordinates of `Psc.Lie3.phi3` (a `det M`-eigenvector
when `K₃(T) ≠ 0`). -/
theorem phi3_k3Vec_eq_det (j : P.Rep) :
    Lie3.phi3 (incQ S) (Lie3.k3Vec j.1.1 j.1.2) = (incQ S).det • Lie3.k3Vec j.1.1 j.1.2 :=
  phi3_k3Vec_of_le_ker P hbal _
    (range_q3m_le_ker P hbal hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 hbound) j

/-- **`thm:deg23` (iii), step (d)**: `rank Q₃ ≤ 2`. -/
theorem rank_q3_le_two : Module.finrank ℚ (LinearMap.range (Q3m P hbal)) ≤ 2 :=
  finrank_le_two hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 (one_le_abs_det_incQ hM) _
    (bound_q3 P hbal hbound)

/-- **`thm:deg23` (iii) for normalised representatives**, all four steps. -/
theorem deg23_iii :
    (∀ z : ℂ, aeval z (q3 P hbal) = 0 → z = ((incQ S).det : ℂ)) ∧
      q3 P hbal = (X - C (incQ S).det) ^ Module.finrank ℚ (LinearMap.range (Q3m P hbal)) ∧
      LinearMap.range (Q3m P hbal) ≤ LinearMap.ker (phi3Lie (incQ S) - (incQ S).det • 1) ∧
      Module.finrank ℚ (LinearMap.range (Q3m P hbal)) ≤ 2 :=
  ⟨fun _ => root_q3_eq_det P hbal hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 hbound,
    q3_eq_pow P hbal hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 hbound,
    range_q3m_le_ker P hbal hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 hbound,
    rank_q3_le_two P hbal hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 hbound⟩

/-- **With a nonzero column** (`r(C) = 3`): `1 ≤ rank Q₃ ≤ 2`, and `det M` is a root of
`χ_S` (an eigenvalue of the signed cocycle matrix), since `X - det M ∣ q₃ ∣ χ_S`. -/
theorem deg23_iii_of_ne (hK : ∃ j : P.Rep, Lie3.k3Vec j.1.1 j.1.2 ≠ 0) :
    1 ≤ Module.finrank ℚ (LinearMap.range (Q3m P hbal)) ∧
      Module.finrank ℚ (LinearMap.range (Q3m P hbal)) ≤ 2 ∧
      (SsignQ P).charpoly.IsRoot (incQ S).det := by
  have hpos : 1 ≤ Module.finrank ℚ (LinearMap.range (Q3m P hbal)) := by
    rw [← natDegree_q3]; exact natDegree_q3_pos P hbal hK
  refine ⟨hpos, rank_q3_le_two P hbal hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 hbound, ?_⟩
  rw [← dvd_iff_isRoot]
  refine dvd_trans ?_ (q3_dvd_ssign P hbal)
  rw [q3_eq_pow P hbal hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 hbound]
  exact dvd_pow_self _ (by omega)

end Main

/-- **The eigenvalue of a positive left eigenvector of `M` is `β`.**  In the setting of
`deg23_iii` (`χ_M` irreducible; `β, α, γ` pairwise distinct complex roots,
`‖α‖, ‖γ‖ < 1`), if `ℓ > 0` and `ℓ M = b ℓ`, then `b = β`: `b` is a root of `χ_M`
(`Psc.PerronSimple.isRoot_of_real_left_eigen`), every root has modulus `≤ b`
(`Psc.PerronExistence.norm_le_of_pos_left_eigen`), `b ∈ {β, α, γ}` (`root_cases`), and
`b = α` or `b = γ` would give `‖βαγ‖ < 1 ≤ |det M|` (`norm_mul_lt_one`,
`one_le_abs_det_incQ`).  No bound `1 < ‖β‖` is assumed. -/
theorem perron_eq_root (hM : Irreducible (incQ S).charpoly) {β α γ : ℂ}
    (hβ : aeval β (incQ S).charpoly = 0) (hα : aeval α (incQ S).charpoly = 0)
    (hγ : aeval γ (incQ S).charpoly = 0) (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ)
    (hα1 : ‖α‖ < 1) (hγ1 : ‖γ‖ < 1) (ℓ : Fin 3 → ℝ) (hℓ : ∀ a, 0 < ℓ a) (b : ℝ)
    (hℓN : ℓ ᵥ* (inc S.s).map (Nat.cast : ℕ → ℝ) = b • ℓ) : (b : ℂ) = β := by
  have hℓ0 : ℓ ≠ 0 := fun h => by simpa [h] using hℓ 0
  have hR : (incQ S).map ((↑) : ℚ → ℝ) = (inc S.s).map (Nat.cast : ℕ → ℝ) := by
    ext; simp
  have hbR : aeval b (incQ S).charpoly = 0 :=
    Psc.PerronSimple.isRoot_of_real_left_eigen (incQ S) ℓ b hℓ0 (by rw [hR]; exact hℓN)
  have hbC : aeval (b : ℂ) (incQ S).charpoly = 0 := by
    have h := aeval_algebraMap_apply ℂ b (incQ S).charpoly
    rw [hbR, map_zero] at h
    simpa using h
  have hC : ((inc S.s).map (Nat.cast : ℕ → ℝ)).map ((↑) : ℝ → ℂ) =
      (incQ S).map (algebraMap ℚ ℂ) := by
    ext; simp
  have hle : ‖β‖ ≤ b :=
    Psc.PerronExistence.norm_le_of_pos_left_eigen _ (fun i j => by simp) ℓ hℓ b hℓN β
      (by rw [hC, Matrix.charpoly_map, eval_map_algebraMap]; exact hβ)
  have hdet := one_le_norm_mul_roots hβ hα hγ hβα hβγ hαγ (one_le_abs_det_incQ hM)
  have hβb : ‖β‖ ≤ ‖(b : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hle.trans (le_abs_self b)
  rcases root_cases (incQ S) hβ hα hγ hβα hβγ hαγ hbC with h | h | h
  · exact h
  · rw [h] at hβb
    exact absurd hdet (not_le.2 (norm_mul_lt_one (hβb.trans_lt hα1) hα1 hγ1))
  · rw [h] at hβb
    exact absurd hdet (not_le.2 (norm_mul_lt_one (hβb.trans_lt hγ1) hα1 hγ1))

/-- **`thm:deg23` (iii) from Perron data instead of the root bound.**  In the setting of
`deg23_iii`, with a positive left eigenvector `ℓ M = b ℓ` in place of `hbound`: `b = β`
(`perron_eq_root`), so `hbound` is `roots_ssign_le` (`prop:cocycle`), and the four steps
hold.  `b` is not assumed to be a root of `χ_M`, nor distinct from `α, γ`. -/
theorem deg23_iii_of_perron (hM : Irreducible (incQ S).charpoly) {β α γ : ℂ}
    (hβ : aeval β (incQ S).charpoly = 0) (hα : aeval α (incQ S).charpoly = 0)
    (hγ : aeval γ (incQ S).charpoly = 0) (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ)
    (hα1 : ‖α‖ < 1) (hγ1 : ‖γ‖ < 1) (ℓ : Fin 3 → ℝ) (hℓ : ∀ a, 0 < ℓ a) (b : ℝ)
    (hℓN : ℓ ᵥ* (inc S.s).map (Nat.cast : ℕ → ℝ) = b • ℓ) :
    (b : ℂ) = β ∧ (∀ z : ℂ, aeval z (q3 P hbal) = 0 → z = ((incQ S).det : ℂ)) ∧
      q3 P hbal = (X - C (incQ S).det) ^ Module.finrank ℚ (LinearMap.range (Q3m P hbal)) ∧
      LinearMap.range (Q3m P hbal) ≤ LinearMap.ker (phi3Lie (incQ S) - (incQ S).det • 1) ∧
      Module.finrank ℚ (LinearMap.range (Q3m P hbal)) ≤ 2 := by
  have hbβ := perron_eq_root hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 ℓ hℓ b hℓN
  refine ⟨hbβ, deg23_iii P hbal hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 fun μ hμ => ?_⟩
  rw [← hbβ, Complex.norm_real, Real.norm_eq_abs]
  exact (roots_ssign_le P ℓ hℓ b hℓN (fun T hT => (hbal T hT).1) μ hμ).trans (le_abs_self b)

/-- **`thm:deg23` (iii) for a primitive substitution** (`hbound` discharged).  Let
`σ = S.s` be primitive (`M^k > 0`), `χ_M` irreducible with pairwise distinct complex roots
`β, α, γ`, `‖α‖, ‖γ‖ < 1`, and `P` a normalisation with `∼₂` states.  Then `β` is the
Perron root `r` of `M` (`PerronData` from `Psc.PerronExistence.perron_inc`, and
`perron_eq_root`), and the four steps of `thm:deg23` (iii) hold. -/
theorem deg23_iii_of_primitive (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc S.s ^ k) a c)
    (hM : Irreducible (incQ S).charpoly) {β α γ : ℂ}
    (hβ : aeval β (incQ S).charpoly = 0) (hα : aeval α (incQ S).charpoly = 0)
    (hγ : aeval γ (incQ S).charpoly = 0) (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ)
    (hα1 : ‖α‖ < 1) (hγ1 : ‖γ‖ < 1) :
    (∃ (r : ℝ) (ℓ u : Fin 3 → ℝ),
        Psc.PerronExistence.PerronData ((inc S.s).map (Nat.cast : ℕ → ℝ)) r ℓ u ∧
          (r : ℂ) = β) ∧
      (∀ z : ℂ, aeval z (q3 P hbal) = 0 → z = ((incQ S).det : ℂ)) ∧
      q3 P hbal = (X - C (incQ S).det) ^ Module.finrank ℚ (LinearMap.range (Q3m P hbal)) ∧
      LinearMap.range (Q3m P hbal) ≤ LinearMap.ker (phi3Lie (incQ S) - (incQ S).det • 1) ∧
      Module.finrank ℚ (LinearMap.range (Q3m P hbal)) ≤ 2 := by
  obtain ⟨r, ℓ, u, h, -, -⟩ := Psc.PerronExistence.perron_inc S.s hprim
  obtain ⟨hr, h4⟩ :=
    deg23_iii_of_perron P hbal hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 ℓ h.left_pos r h.left
  exact ⟨⟨r, ℓ, u, h, hr⟩, h4⟩

end Rep

/-! ### Controls -/

section Controls

open Psc.Binomial Psc.SignedCocycle Psc.ParikhRank Psc.Degree2Sector Psc.Incidence
  Psc.SignedIntertwiner Psc.ConcentrationControls Psc.M0Pisot

/-! #### Matrix level: `M0` and the `∼₂` pair `T13` (every hypothesis of the core) -/

/-- `M0` meets the matrix hypotheses: irreducible `χ` (`Psc.KernelCofactor.ctrl_irreducible`),
three distinct roots, two of modulus `< 1` (the real roots in `(-1,0)`, `(0,1)` of
`Psc.M0Pisot`), and `|det M0| = 2 ≥ 1`. -/
theorem m0_hyps : Irreducible M0.charpoly ∧ ∃ β α γ : ℂ,
    aeval β M0.charpoly = 0 ∧ aeval α M0.charpoly = 0 ∧ aeval γ M0.charpoly = 0 ∧
      β ≠ α ∧ β ≠ γ ∧ α ≠ γ ∧ ‖α‖ < 1 ∧ ‖γ‖ < 1 ∧ 1 ≤ |M0.det| := by
  obtain ⟨r1, ⟨h1l, h1u⟩, h1⟩ := exists_root_neg
  obtain ⟨r2, ⟨h2l, h2u⟩, h2⟩ := exists_root_small
  obtain ⟨r3, ⟨h3l, -⟩, h3⟩ := exists_root_big
  refine ⟨Psc.KernelCofactor.ctrl_irreducible, r3, r1, r2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f_is_charpoly]; exact aeval_ofReal_f r3 h3
  · rw [f_is_charpoly]; exact aeval_ofReal_f r1 h1
  · rw [f_is_charpoly]; exact aeval_ofReal_f r2 h2
  · exact_mod_cast (show r3 ≠ r1 by linarith)
  · exact_mod_cast (show r3 ≠ r2 by linarith)
  · exact_mod_cast (show r1 ≠ r2 by linarith)
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  · rw [M0_det]; norm_num

/-- `M0^{⊗3} K₃(T13) = det(M0) K₃(T13)` in the coordinates of `Psc.Lie3.phi3`
(`Psc.ConcentrationControls.t13_det_sector`, cast to `ℚ`). -/
theorem m0_phi3_t13 :
    Lie3.phi3 M0 (Lie3.k3Vec u13 v13) = M0.det • Lie3.k3Vec u13 v13 := by
  funext a b c
  have h := congrArg (Int.cast : ℤ → ℚ) (t13_det_sector a b c)
  rw [ConcentrationControls.m0_det] at h
  simp only [sum3, Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_ofNat] at h
  simp only [Lie3.phi3, Lie3.k3Vec, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul, M0_det,
    M0_eq_m0]
  rw [← Psc.CountBridge.controls_k3_eq]
  simp only [← Psc.CountBridge.controls_k3_eq]
  linear_combination h

/-- `K₃(T13)` as an element of `Lie₃(ℚ³)`. -/
def t13Lie : Lie3Q := ⟨Lie3.k3Vec u13 v13, Lie3.k3Vec_mem_span_lyndon t13_equiv2⟩

theorem t13Lie_ne : t13Lie ≠ 0 := by
  intro h
  obtain ⟨a, b, c, hne⟩ := t13_k3_ne_zero
  have := congrFun (congrFun (congrFun (congrArg Subtype.val h) a) b) c
  simp only [t13Lie, Lie3.k3Vec, Submodule.coe_zero, Pi.zero_apply, Int.cast_eq_zero] at this
  exact hne (by rw [Psc.CountBridge.controls_k3_eq]; exact this)

/-- The line `W₀ = ℚ K₃(T13) ⊆ Lie₃(ℚ³)`. -/
def W0 : Submodule ℚ Lie3Q := Submodule.span ℚ {t13Lie}

theorem W0_le_ker : W0 ≤ LinearMap.ker (phi3Lie M0 - M0.det • 1) := by
  refine Submodule.span_le.2 (Set.singleton_subset_iff.2 ?_)
  show (phi3Lie M0 - M0.det • 1) t13Lie = 0
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
  exact Subtype.ext m0_phi3_t13

theorem W0_invariant : ∀ v ∈ W0, phi3Lie M0 v ∈ W0 :=
  invariant_of_le_ker _ _ W0_le_ker

theorem W0_ne_bot : W0 ≠ ⊥ := by
  rw [W0, Ne, Submodule.span_singleton_eq_bot]; exact t13Lie_ne

/-- **Full control of the matrix-level theorems** (`root_restrict_eq_det`,
`charpoly_restrict_eq_pow`, `le_ker_sub_det`, `finrank_le_two`): `M0` with the
`Φ₃`-invariant line `W₀ = ℚ K₃(T13) ≠ 0` meets every hypothesis, the spectral bound
included (by the converse `bound_of_le_ker`). -/
theorem m0_control : Irreducible M0.charpoly ∧ ∃ β α γ : ℂ,
    (aeval β M0.charpoly = 0 ∧ aeval α M0.charpoly = 0 ∧ aeval γ M0.charpoly = 0 ∧
      β ≠ α ∧ β ≠ γ ∧ α ≠ γ ∧ ‖α‖ < 1 ∧ ‖γ‖ < 1 ∧ 1 ≤ |M0.det|) ∧
      W0 ≠ ⊥ ∧ ∀ z : ℂ, aeval z (resCharpoly (phi3Lie M0) W0_invariant) = 0 → ‖z‖ ≤ ‖β‖ := by
  obtain ⟨hM, β, α, γ, hβ, hα, hγ, hβα, hβγ, hαγ, hα1, hγ1, hdet⟩ := m0_hyps
  exact ⟨hM, β, α, γ, ⟨hβ, hα, hγ, hβα, hβγ, hαγ, hα1, hγ1, hdet⟩, W0_ne_bot,
    bound_of_le_ker hβ hα hγ hβα hβγ hαγ hα1 hγ1 W0_invariant W0_le_ker⟩

/-- On the control, conclusion (b) reads `χ(Φ₃|_{W₀}) = X - det M0 = X + 2`. -/
theorem m0_W0_charpoly : resCharpoly (phi3Lie M0) W0_invariant = X - C M0.det := by
  rw [resCharpoly_of_le_ker _ _ _ W0_le_ker, W0, finrank_span_singleton t13Lie_ne, pow_one]

/-- `W = Lie₃(ℚ³)` is `Φ₃`-invariant. -/
theorem top_invariant (M : Matrix (Fin 3) (Fin 3) ℚ) :
    ∀ v ∈ (⊤ : Submodule ℚ Lie3Q), phi3Lie M v ∈ (⊤ : Submodule ℚ Lie3Q) :=
  fun _ _ => Submodule.mem_top

/-- **Negative control: the spectral bound cannot be dropped.**  `W = Lie₃(ℚ³)` is
`Φ₃(M0)`-invariant and `M0` meets every other hypothesis of the matrix-form core
(`m0_hyps`), but `dim W = 8 > 2` and `W ⊄ ker (Φ₃ - det M0)` (whose dimension is `≤ 2`,
`finrank_ker_sub_det_le_two`); so, for **every** admissible choice of `β, α, γ`, some root of
`χ(Φ₃(M0)|_W) = χ(Φ₃(M0))` has modulus `> ‖β‖` (by `bound_iff_le_ker`). -/
theorem m0_bound_needed :
    Module.finrank ℚ (⊤ : Submodule ℚ Lie3Q) = 8 ∧
      ¬ ((⊤ : Submodule ℚ Lie3Q) ≤ LinearMap.ker (phi3Lie M0 - M0.det • 1)) ∧
      ∀ β α γ : ℂ, aeval β M0.charpoly = 0 → aeval α M0.charpoly = 0 →
        aeval γ M0.charpoly = 0 → β ≠ α → β ≠ γ → α ≠ γ → ‖α‖ < 1 → ‖γ‖ < 1 →
        ∃ z : ℂ, aeval z (resCharpoly (phi3Lie M0) (top_invariant M0)) = 0 ∧ ‖β‖ < ‖z‖ := by
  have h8 : Module.finrank ℚ (⊤ : Submodule ℚ Lie3Q) = 8 := by
    rw [finrank_top, finrank_span_eq_card Lie3.linearIndependent_lyndon, Fintype.card_fin]
  have hnot : ¬ ((⊤ : Submodule ℚ Lie3Q) ≤ LinearMap.ker (phi3Lie M0 - M0.det • 1)) := by
    intro hle
    obtain ⟨-, β, α, γ, hβ, hα, hγ, hβα, hβγ, hαγ, -, -, -⟩ := m0_hyps
    have h2 := finrank_ker_sub_det_le_two hβ hα hγ hβα hβγ hαγ (by rw [M0_det]; norm_num)
    have h3 : 8 ≤ 2 := h8 ▸ (Submodule.finrank_mono hle).trans h2
    omega
  refine ⟨h8, hnot, fun β α γ hβ hα hγ hβα hβγ hαγ hα1 hγ1 => ?_⟩
  by_contra hcon
  push Not at hcon
  exact hnot ((bound_iff_le_ker m0_hyps.1 hβ hα hγ hβα hβγ hαγ hα1 hγ1
    (by rw [M0_det]; norm_num) (top_invariant M0)).1 hcon)

/-! #### State level: `wT` (the identity substitution, `χ_M = (X - 1)³`) -/

theorem incQ_wT : incQ wT = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wT, Psc.Reduction.redSystem, idSubst]

/-- **The conclusions on an actual child system with `im Q₃ ≠ 0`** (`wT`, `Equiv2` states,
`K₃ ≠ 0`): `q₃ = (X - det M)^{rank Q₃}`, `im Q₃ ⊆ ker (Φ₃ - det M)`, `1 ≤ rank Q₃ ≤ 2`.
Weak: `M = 1`, so `Φ₃ = 1` and (c) is automatic; `χ_M = (X - 1)³` is reducible
(`Psc.KernelCofactor.wT_not_irreducible`) and the Pisot moduli fail. -/
theorem wT_conclusions :
    ¬ Irreducible (incQ wT).charpoly ∧
    q3 wTNorm wT_equiv2 =
        (X - C (incQ wT).det) ^ Module.finrank ℚ (LinearMap.range (Q3m wTNorm wT_equiv2)) ∧
      LinearMap.range (Q3m wTNorm wT_equiv2) ≤
        LinearMap.ker (phi3Lie (incQ wT) - (incQ wT).det • 1) ∧
      1 ≤ Module.finrank ℚ (LinearMap.range (Q3m wTNorm wT_equiv2)) ∧
      Module.finrank ℚ (LinearMap.range (Q3m wTNorm wT_equiv2)) ≤ 2 := by
  have hle : LinearMap.range (Q3m wTNorm wT_equiv2) ≤
      LinearMap.ker (phi3Lie (incQ wT) - (incQ wT).det • 1) := by
    intro v _
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero, incQ_wT, Matrix.det_one, one_smul]
    exact Subtype.ext (LieWeights.phi3_one (v : Lie3.Vec3 ℚ))
  have hcard : Module.finrank ℚ (wTNorm.Rep → ℚ) = 1 := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_eq_one_iff.2 ⟨wTRep, wTNorm_rep⟩
  refine ⟨Psc.KernelCofactor.wT_not_irreducible, resCharpoly_of_le_ker _ _ _ hle, hle, ?_, ?_⟩
  · rw [← natDegree_q3]; exact wT_q3_pos
  · have := LinearMap.finrank_range_le (Q3m wTNorm wT_equiv2)
    omega

/-! #### Negative control: the 3-cycle relabelling (`χ_M = X³ - 1`) -/

theorem incQ_cyc3 : incQ cyc3Sys = cycM := rfl

theorem cycM_det : cycM.det = 1 := by
  simp [Matrix.det_fin_three, cycSubst]

/-- `χ_M = X³ - 1 = (X - 1)(X² + X + 1)` is reducible. -/
theorem cycM_not_irreducible : ¬ Irreducible cycM.charpoly := by
  rw [cycM_charpoly]
  intro h
  obtain ⟨g, hg⟩ : (X - C 1 : ℚ[X]) ∣ X ^ 3 - 1 := by rw [dvd_iff_isRoot]; simp
  rcases h.isUnit_or_isUnit hg with hu | hu
  · exact not_isUnit_X_sub_C 1 hu
  · have h3 : (X ^ 3 - 1 : ℚ[X]).natDegree = 3 := by compute_degree!
    rw [hg, natDegree_mul (X_sub_C_ne_zero 1) hu.ne_zero, natDegree_X_sub_C,
      natDegree_eq_zero_of_isUnit hu] at h3
    omega

theorem cycX_norm (i : Fin 3) : ‖cycX i‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (cycX_cube i) (by norm_num)

/-- `ρ(S) ≤ 1` on `cyc3Norm` (`roots_ssign_le` with `ℓ = (1,1,1)`, `ℓ M = ℓ`). -/
theorem cyc3_bound : ∀ μ : ℂ, aeval μ (SsignQ cyc3Norm).charpoly = 0 → ‖μ‖ ≤ ‖cycX 0‖ := by
  intro μ hμ
  rw [cycX_norm]
  refine roots_ssign_le cyc3Norm (fun _ => 1) (fun _ => one_pos) 1 ?_
    (fun T hT => (cyc3_equiv2 T hT).1) μ hμ
  funext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, cyc3Sys,
    Psc.Reduction.redSystem, cycSubst]

/-- **Negative control: the Galois/Pisot hypotheses cannot be dropped.**  `cyc3Norm`
(`Psc.SectorBridge`: `Equiv2` states, a nonzero column, three distinct roots
`cycX = (1, ζ, ζ²)` of `χ_M = X³ - 1`, `|det M| = 1`) meets the spectral bound with
`β = 1` (`cyc3_bound`), but `‖ζ‖ = ‖ζ²‖ = 1` and `χ_M` is reducible, and the conclusion (c)
fails: `M^{⊗3} K₃(wTPair)` is `K₃` shifted by the relabelling, `2` at `(2,0,2)`, where
`det M · K₃ = -2`. -/
theorem cyc3_negative :
    (∀ μ : ℂ, aeval μ (SsignQ cyc3Norm).charpoly = 0 → ‖μ‖ ≤ ‖cycX 0‖) ∧
      1 ≤ |cycM.det| ∧ ¬ Irreducible cycM.charpoly ∧ ‖cycX 1‖ = 1 ∧ ‖cycX 2‖ = 1 ∧
      ¬ (LinearMap.range (Q3m cyc3Norm cyc3_equiv2) ≤
        LinearMap.ker (phi3Lie (incQ cyc3Sys) - (incQ cyc3Sys).det • 1)) := by
  refine ⟨cyc3_bound, by rw [cycM_det]; norm_num, cycM_not_irreducible, cycX_norm 1, cycX_norm 2,
    fun hle => ?_⟩
  have h := congrFun (congrFun (congrFun
    (phi3_k3Vec_of_le_ker cyc3Norm cyc3_equiv2 _ hle ⟨wTPair, by decide⟩) 2) 0) 2
  have k1 : Psc.Intertwiner3.K3 wTPair.1 wTPair.2 1 2 1 = 2 := by decide
  have k2 : Psc.Intertwiner3.K3 wTPair.1 wTPair.2 2 0 2 = -2 := by decide
  rw [incQ_cyc3, cycM_det] at h
  simp [Lie3.phi3, Lie3.k3Vec, Fin.sum_univ_three, cycSubst] at h
  rw [k1, k2] at h
  norm_num at h

/-! #### The census substitution `0 ↦ 011, 1 ↦ 2, 2 ↦ 120` and its length-9 `∼₂` state -/

/-- The substitution class `011 / 2 / 120` of `comp:defect` (manuscript line 1200;
`docs/c4-defect-degree-census.md` §3): `0 ↦ 011`, `1 ↦ 2`, `2 ↦ 120`. -/
def censusSubst : Fin 3 → List (Fin 3) := ![[0, 1, 1], [2], [1, 2, 0]]

/-- Its rational incidence matrix `[[1,0,1],[2,0,1],[0,1,1]]`. -/
abbrev censusQ : Matrix (Fin 3) (Fin 3) ℚ := (inc censusSubst).map (Nat.cast : ℕ → ℚ)

/-- The length-9 state `(011212001, 120011120)` (the second length-9 state class of
`docs/c4-defect-degree-census.md` §3).  Over `censusSubst` its inflation is a single
irreducible `∼₂` pair of length 19 with five children, one a coincidence, and the pair is a
reachable, recurrent vertex of `B_σ`: `Psc.Degree3Catalogue.catalogue_spec` (fields
`reachable`, `recurrent`, `leak`).  The first class `(011202001, 120001120)` inflates over
`censusSubst` to a `∼₂` pair of length 21 and is not a vertex of `B_σ`
(`Psc.Degree3Catalogue.class9a_sigmaA_control`, `class9a_not_mem_sigmaA`); it occurs only
over a relabelled or reversed substitution.  Nothing in this module uses reachability. -/
def censusPair : List (Fin 3) × List (Fin 3) :=
  ([0, 1, 1, 2, 1, 2, 0, 0, 1], [1, 2, 0, 0, 1, 1, 1, 2, 0])

theorem inc_censusSubst :
    inc censusSubst = Matrix.of ![![1, 0, 1], ![2, 0, 1], ![0, 1, 1]] := by
  decide

/-- `censusSubst` is primitive: `M² > 0`. -/
theorem censusSubst_primitive : ∃ k ≥ 1, ∀ a c, 0 < (inc censusSubst ^ k) a c :=
  ⟨2, by norm_num, fun a c => by fin_cases a <;> fin_cases c <;> decide +kernel⟩

/-- `χ_M = X³ - 2X² - 1`. -/
theorem census_charpoly : censusQ.charpoly = X ^ 3 - C 2 * X ^ 2 - 1 := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp [censusQ, inc_censusSubst]
  simp only [map_ofNat]
  ring

theorem census_det : censusQ.det = 1 := by
  rw [Matrix.det_fin_three]; simp [censusQ, inc_censusSubst]; norm_num

/-- The same cubic over `ℤ`, for the rational root theorem. -/
noncomputable def censusZ : ℤ[X] := X ^ 3 - C 2 * X ^ 2 - 1

/-- **`χ_M = X³ - 2X² - 1` is irreducible over `ℚ`**: a cubic, and a rational root of the
monic integer cubic would be an integer dividing `-1` (`exists_integer_of_is_root_of_monic`,
as in `Psc.M0Pisot.f_irreducible`), while `χ(±1) = -2, -4`. -/
theorem census_irreducible : Irreducible censusQ.charpoly := by
  rw [census_charpoly]
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [show (X ^ 3 - C 2 * X ^ 2 - 1 : ℚ[X]).natDegree = 3 by compute_degree!]; decide
  · intro x hx
    have hm : censusZ.Monic := by unfold censusZ; monicity!
    have hx' : aeval x censusZ = 0 := by
      have h0 : eval x (X ^ 3 - C 2 * X ^ 2 - 1 : ℚ[X]) = 0 := hx
      simp [censusZ] at h0 ⊢
      simpa [map_ofNat] using h0
    obtain ⟨n, rfl, hn⟩ := exists_integer_of_is_root_of_monic hm hx'
    have hc : censusZ.coeff 0 = -1 := by simp [censusZ]
    rw [hc] at hn
    have hroot : n ^ 3 - 2 * n ^ 2 - 1 = 0 := by
      have := hx'
      simp [censusZ, map_ofNat] at this
      exact_mod_cast this
    have hb : n.natAbs ≤ 1 := Nat.le_of_dvd (by norm_num) (Int.natAbs_dvd_natAbs.mpr hn)
    have h1 : -1 ≤ n := by omega
    have h2 : n ≤ 1 := by omega
    interval_cases n <;> norm_num at hroot

theorem census_aeval (z : ℂ) : aeval z censusQ.charpoly = z ^ 3 - 2 * z ^ 2 - 1 := by
  rw [census_charpoly]; simp [map_ofNat]

/-- A real root `b ∈ (2, 12/5)` of `x³ - 2x² - 1` (intermediate value theorem). -/
theorem census_real_root : ∃ b : ℝ, 2 < b ∧ b < 12 / 5 ∧ b ^ 3 - 2 * b ^ 2 - 1 = 0 := by
  have hc : Continuous fun x : ℝ => x ^ 3 - 2 * x ^ 2 - 1 := by fun_prop
  obtain ⟨b, ⟨h1, h2⟩, hb⟩ := intermediate_value_Ioo (show (2 : ℝ) ≤ 12 / 5 by norm_num)
    hc.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo ((fun x : ℝ => x ^ 3 - 2 * x ^ 2 - 1) 2)
      ((fun x : ℝ => x ^ 3 - 2 * x ^ 2 - 1) (12 / 5)) by norm_num)
  exact ⟨b, h1, h2, hb⟩

/-- **The other two roots.**  Every complex root `z ≠ b` of `x³ - 2x² - 1` solves
`z² + (b - 2) z + (b² - 2b) = 0`, whose discriminant `-(3b + 2)(b - 2)` is negative; so `z`
is non-real, `Re z = (2 - b)/2`, and `‖z‖² = b² - 2b = 1/b < 1` (as `b < 12/5`). -/
theorem census_other {b : ℝ} (hb2 : 2 < b) (hb3 : b < 12 / 5) (hb : b ^ 3 - 2 * b ^ 2 - 1 = 0)
    {z : ℂ} (hz : z ^ 3 - 2 * z ^ 2 - 1 = 0) (hzb : z ≠ b) :
    ‖z‖ ^ 2 = b ^ 2 - 2 * b ∧ z.im ≠ 0 ∧ ‖z‖ < 1 := by
  have hq : z ^ 2 + (b - 2) * z + (b ^ 2 - 2 * b) = 0 := by
    have hbC : (b : ℂ) ^ 3 - 2 * b ^ 2 - 1 = 0 := by exact_mod_cast hb
    have h : (z - b) * (z ^ 2 + (b - 2) * z + (b ^ 2 - 2 * b)) = 0 := by
      linear_combination hz - hbC
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hzb)
  have hre := congrArg Complex.re hq
  have him := congrArg Complex.im hq
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.zero_re, Complex.add_im, Complex.mul_im,
    Complex.sub_im, Complex.zero_im, Complex.re_ofNat, Complex.im_ofNat] at hre him
  set x := z.re
  set y := z.im
  have hd : 0 < (3 * b + 2) * (b - 2) := by nlinarith
  have hy : y ≠ 0 := by
    intro hy0
    rw [hy0] at hre
    nlinarith [sq_nonneg (2 * x + b - 2)]
  have hx : 2 * x + (b - 2) = 0 := by
    have : y * (2 * x + (b - 2)) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hy
  have hn : ‖z‖ ^ 2 = b ^ 2 - 2 * b := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    linear_combination (-1 : ℝ) * hre + x * hx
  refine ⟨hn, hy, ?_⟩
  nlinarith [norm_nonneg z]

/-- **`censusSubst` meets the matrix hypotheses of `deg23_iii`**: a real root `b > 2` of
`χ_M` and two further roots `α ≠ γ`, all three pairwise distinct (`exists_distinct_roots`),
with `‖α‖, ‖γ‖ < 1` (`census_other`). -/
theorem census_pisot : ∃ b : ℝ, 2 < b ∧ ∃ α γ : ℂ, aeval (b : ℂ) censusQ.charpoly = 0 ∧
    aeval α censusQ.charpoly = 0 ∧ aeval γ censusQ.charpoly = 0 ∧ (b : ℂ) ≠ α ∧
      (b : ℂ) ≠ γ ∧ α ≠ γ ∧ ‖α‖ < 1 ∧ ‖γ‖ < 1 := by
  obtain ⟨b, hb2, hb3, hb⟩ := census_real_root
  have hbC : aeval (b : ℂ) censusQ.charpoly = 0 := by rw [census_aeval]; exact_mod_cast hb
  obtain ⟨x, hx, hroot, hall⟩ := exists_distinct_roots (L := ℂ) censusQ census_irreducible
  obtain ⟨i, hi⟩ := hall _ hbC
  obtain ⟨j, k, hij, hik, hjk⟩ : ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    fin_cases i
    · exact ⟨1, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 1, by decide, by decide, by decide⟩
  have hbj : (b : ℂ) ≠ x j := by rw [hi]; exact hx.ne hij
  have hbk : (b : ℂ) ≠ x k := by rw [hi]; exact hx.ne hik
  have hn : ∀ z : ℂ, aeval z censusQ.charpoly = 0 → z ≠ b → ‖z‖ < 1 := fun z hz hzb =>
    (census_other hb2 hb3 hb (by rw [← census_aeval]; exact hz) hzb).2.2
  exact ⟨b, hb2, x j, x k, hbC, hroot j, hroot k, hbj, hbk, hx.ne hjk,
    hn _ (hroot j) hbj.symm, hn _ (hroot k) hbk.symm⟩

/-- The census state is `∼₂` (`K₁ = K₂ = 0`). -/
theorem census_equiv2 : Equiv2 censusPair.1 censusPair.2 := by unfold Equiv2 Equiv1; decide

theorem census_k3_001 : Psc.Intertwiner3.K3 censusPair.1 censusPair.2 0 0 1 = 0 := by decide

theorem census_k3_001_swap : Psc.Intertwiner3.K3 censusPair.2 censusPair.1 0 0 1 = 0 := by
  decide

/-- `(M^{⊗3} K₃)(0,0,1) = 2` for the census state (an integer computation). -/
theorem census_phi3_001 : (∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3,
    ((inc censusSubst 0 x : ℤ) * inc censusSubst 0 y * inc censusSubst 1 z) *
      Psc.Intertwiner3.K3 censusPair.1 censusPair.2 x y z) = 2 := by
  decide +kernel

theorem census_phi3_001_swap : (∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3,
    ((inc censusSubst 0 x : ℤ) * inc censusSubst 0 y * inc censusSubst 1 z) *
      Psc.Intertwiner3.K3 censusPair.2 censusPair.1 x y z) = -2 := by
  decide +kernel

/-- `K₃` of the census state is nonzero (`K₃(0,2,1) = 3`). -/
theorem census_k3_ne : Lie3.k3Vec censusPair.1 censusPair.2 ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun (congrFun h 0) 2) 1
  have k : Psc.Intertwiner3.K3 censusPair.1 censusPair.2 0 2 1 = 3 := by decide
  simp only [Lie3.k3Vec, k, Pi.zero_apply] at h1
  norm_num at h1

/-- Over `censusSubst`, a pair with `K₃(0,0,1) = 0` and `(M^{⊗3} K₃)(0,0,1) ≠ 0` has
`M^{⊗3} K₃ ≠ c K₃` for every `c`. -/
theorem phi3_ne_smul_of_coord {S : ChildSystem (Fin 3)} (hs : S.s = censusSubst)
    {u v : List (Fin 3)} (h0 : Psc.Intertwiner3.K3 u v 0 0 1 = 0)
    (hsum : (∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3,
      ((inc censusSubst 0 x : ℤ) * inc censusSubst 0 y * inc censusSubst 1 z) *
        Psc.Intertwiner3.K3 u v x y z) ≠ 0) (c : ℚ) :
    Lie3.phi3 (incQ S) (Lie3.k3Vec u v) ≠ c • Lie3.k3Vec u v := by
  intro h
  have hq : incQ S = censusQ := by
    show (inc S.s).map (Nat.cast : ℕ → ℚ) = _
    rw [hs]
  have h1 := congrFun (congrFun (congrFun h 0) 0) 1
  rw [hq] at h1
  simp only [Lie3.phi3, Lie3.k3Vec, Pi.smul_apply, smul_eq_mul, h0, Int.cast_zero, mul_zero,
    Matrix.map_apply] at h1
  apply hsum
  exact_mod_cast h1

/-- **Content control: the census state violates (c), so it lies in no `∼₂` child system
over `censusSubst`.**  `censusSubst` is primitive with irreducible Pisot `χ_M = X³ - 2X² - 1`
(`census_pisot`), the census state is `∼₂` with `K₃ ≠ 0` (`census_equiv2`, `census_k3_ne`),
and `M^{⊗3} K₃ ≠ det M · K₃` in either orientation (`census_phi3_001`,
`census_phi3_001_swap`).  So, by `deg23_iii_of_primitive` (step (c)) applied to the
representative `T` or `T.swap` (`Normalisation.cover`): **no child system over
`censusSubst` whose states are all `∼₂` and which has a normalisation contains this state.**
This formalizes, for this one state, the manuscript's reading of `comp:defect` ("none of
which satisfies the necessary condition `im Q₃ ⊆ ker (Φ₃ - det M)`"), line 1204; all 24
catalogue occurrences over the 12 catalogue substitutions are
`Psc.Degree3Catalogue.catalogue_spec` (field `not_mem`), and the exact vertex sets of their
automata are `Psc.Degree3Catalogue.catalogue_exact`. -/
theorem census_not_mem (S : ChildSystem (Fin 3)) (hs : S.s = censusSubst) (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Equiv2 T.1 T.2) : censusPair ∉ S.C := by
  intro hT
  have hq : incQ S = censusQ := by
    show (inc S.s).map (Nat.cast : ℕ → ℚ) = _
    rw [hs]
  have hM : Irreducible (incQ S).charpoly := hq ▸ census_irreducible
  obtain ⟨b, -, α, γ, hb, hα, hγ, hbα, hbγ, hαγ, hα1, hγ1⟩ := census_pisot
  rw [← hq] at hb hα hγ
  have hle := (deg23_iii_of_primitive P hbal (hs ▸ censusSubst_primitive) hM hb hα hγ hbα hbγ
    hαγ hα1 hγ1).2.2.2.1
  rcases P.cover _ hT with hR | hR
  · exact phi3_ne_smul_of_coord hs census_k3_001 (by rw [census_phi3_001]; norm_num) _
      (phi3_k3Vec_of_le_ker P hbal _ hle ⟨_, hR⟩)
  · exact phi3_ne_smul_of_coord hs census_k3_001_swap (by rw [census_phi3_001_swap]; norm_num) _
      (phi3_k3Vec_of_le_ker P hbal _ hle ⟨_, hR⟩)

/-- The census state meets the state-level hypotheses that `census_not_mem` does not
refute: `∼₂`, `K₃ ≠ 0`, and (c) fails for every eigenvalue `c`, over every child system
with `S.s = censusSubst`. -/
theorem census_state : Equiv2 censusPair.1 censusPair.2 ∧
    Lie3.k3Vec censusPair.1 censusPair.2 ≠ 0 ∧
    ∀ S : ChildSystem (Fin 3), S.s = censusSubst → ∀ c : ℚ,
      Lie3.phi3 (incQ S) (Lie3.k3Vec censusPair.1 censusPair.2) ≠
        c • Lie3.k3Vec censusPair.1 censusPair.2 :=
  ⟨census_equiv2, census_k3_ne, fun _ hs c =>
    phi3_ne_smul_of_coord hs census_k3_001 (by rw [census_phi3_001]; norm_num) c⟩

/-- The empty child system over `censusSubst`: no states. -/
def censusEmpty : ChildSystem (Fin 3) where
  s := censusSubst
  C := ∅
  children := fun _ => []
  top := by simp
  bot := by simp
  closed := by simp
  nonempty := by simp

/-- The (empty) normalisation of `censusEmpty`. -/
def censusEmptyNorm : Normalisation censusEmpty where
  R := ∅
  swap_mem := by simp [censusEmpty]
  children_swap := by simp [censusEmpty]
  sub := by simp
  cover := by simp [censusEmpty]
  not_both := by simp

theorem censusEmpty_equiv2 : ∀ T ∈ censusEmpty.C, Equiv2 T.1 T.2 := by simp [censusEmpty]

/-- **Degenerate full control of `deg23_iii`, `deg23_iii_of_perron`,
`deg23_iii_of_primitive`.**  The empty child system over `censusSubst` meets every
hypothesis: primitivity, `∼₂` states (vacuously), irreducible `χ_M`, a real root `b` and
two further roots of modulus `< 1`, and the bound `hbound` (vacuously: `χ_S = 1` has no
root).  The conclusion holds and is degenerate: `im Q₃ = 0`.  A non-degenerate full control
would be a normalised child system over a primitive irreducible Pisot substitution with
`∼₂` states and a nonzero `K₃` column; none is known (`census_not_mem` excludes the census
state). -/
theorem census_empty_control :
    (∃ k ≥ 1, ∀ a c, 0 < (inc censusEmpty.s ^ k) a c) ∧ Irreducible (incQ censusEmpty).charpoly ∧
      (∃ b : ℝ, 2 < b ∧ ∃ α γ : ℂ, aeval (b : ℂ) (incQ censusEmpty).charpoly = 0 ∧
        aeval α (incQ censusEmpty).charpoly = 0 ∧ aeval γ (incQ censusEmpty).charpoly = 0 ∧
        (b : ℂ) ≠ α ∧ (b : ℂ) ≠ γ ∧ α ≠ γ ∧ ‖α‖ < 1 ∧ ‖γ‖ < 1 ∧
        ∀ μ : ℂ, aeval μ (SsignQ censusEmptyNorm).charpoly = 0 → ‖μ‖ ≤ ‖(b : ℂ)‖) ∧
      (SsignQ censusEmptyNorm).charpoly = 1 ∧
      Module.finrank ℚ (LinearMap.range (Q3m censusEmptyNorm censusEmpty_equiv2)) = 0 := by
  have : IsEmpty censusEmptyNorm.Rep := ⟨fun j => by simpa [censusEmptyNorm] using j.2⟩
  have h1 : (SsignQ censusEmptyNorm).charpoly = 1 := Matrix.charpoly_isEmpty
  obtain ⟨b, hb2, α, γ, hb, hα, hγ, hbα, hbγ, hαγ, hα1, hγ1⟩ := census_pisot
  refine ⟨censusSubst_primitive, census_irreducible,
    ⟨b, hb2, α, γ, hb, hα, hγ, hbα, hbγ, hαγ, hα1, hγ1, fun μ hμ => ?_⟩, h1,
    Nat.eq_zero_of_le_zero ((LinearMap.finrank_range_le _).trans (by simp))⟩
  rw [h1, map_one] at hμ
  exact absurd hμ one_ne_zero

end Controls

end Psc.Degree3Sector
