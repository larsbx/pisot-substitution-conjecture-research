import PscVerif.SectorBridge
import PscVerif.GaloisOrbit
import PscVerif.Wielandt
import PscVerif.PerronExistence
import PscVerif.CocycleSpectrum

/-!
# `thm:sieve` at `r = 4`: the degree-four first-defect floor

`manuscripts/PSC_balanced_pair_state_2026-09-13.tex`, `thm:sieve` (the clause "In
particular, if `r = 4` then `|det M| = 1` and `ρ(S) = β`") and its proof sketch ("For
`r = 4` the shapes are `(2,1,1)` … and, only for complex stable roots with `|det M| = 1`,
`(2,2,0)`; both have spectral radius `≥ β`, forcing `ρ(S) = β` and `|det M| = 1` through
Theorem `thm:defect-intertwiner`"), with `prop:cocycle` (`ρ(S) ≤ β`) as input.  Ledger claim
`Degree4Floor` ("the degree-4 first-defect reduction", `docs/c4-degree4-free-lie.md`).
`docs/c4-concentration-attack-2026-11-06.md` §2, Theorem A (i), (ii) and (iii), and §8,
rows `SectorBridge`, `GaloisOrbit`, `WeightModulus`, `Wielandt`, `PerronExistence`: this
module is the composition that §8 lists as "the case analysis of `thm:sieve` … not
formalized".

## Setting

`S : ChildSystem (Fin 3)`, `P : Normalisation S`, every state `∼₃` (`Psc.Defect4.Equiv3`:
`K₁ = K₂ = K₃ = 0`) and some representative column `K₄(j) ≠ 0` — together exactly
`r(C) = 4`.  `M = incQ S`, `S = SsignQ P` (the manuscript's cocycle matrix `A − B`),
`q₄ = Psc.SectorBridge.q4 P hbal = χ(Φ₄|_{im Q₄})`, which divides `χ_S`
(`q4_dvd_ssign`).  `χ_M` is irreducible, with complex roots `β, α, γ`, `α ≠ γ`,
`1 < ‖β‖`, `‖α‖ < 1`, `‖γ‖ < 1` (Pisot); `β ≠ α, γ` follows from the moduli, and the Pisot
form `sieve4_pisot` needs no distinctness at all (`exists_other_roots`).  `1 ≤ |det M|` is
**derived**, not assumed: `det M` is an integer (`det_incQ`), nonzero because `χ_M` is
irreducible (`Psc.Cyclicity.det_ne_zero_of_irreducible`), and `det M = βαγ`
(`Psc.SectorBridge.det_eq_mul_roots`).  The spectral bound of `prop:cocycle` enters `sieve4`, `sieve4_roots`,
`sieve4_pisot` as `hρ : ∀ μ, χ_S(μ) = 0 → ‖μ‖ ≤ ‖β‖`; it is discharged from any positive
left `β`-eigenvector `L` of `N_C` by `Psc.SectorBridge.ssign_root_bound_of_perron` (so the Wielandt-layer
theorems, which take `L`, do not assume it), and for primitive `σ` by
`ssign_root_bound_of_primitive`.

## Proved here, in full

* **Roots** (`3 × 3` rational `M`): `natDegree_charpoly`; `det_eq_mul_roots`
  (`det M = βαγ` for three distinct complex roots, via
  `Matrix.det_eq_prod_roots_charpoly`); `exists_other_roots` (irreducible `χ_M`: any root
  `β` has two further roots `α ≠ γ`, and these three are all the roots); `injective_vec3`.
* **The sieve for an arbitrary rational `q`** (composition of `Psc.GaloisOrbit`; `f`
  irreducible cubic with roots `β, α, γ`, Pisot moduli, `1 ≤ ‖βαγ‖`, every root of `q` of
  modulus `≤ ‖β‖`, and `q` vanishing at a weight `β^a α^b γ^c` of a listed shape):
  `Psc.GaloisOrbit.orbit_211_root` (shape `(2,1,1)` gives the root `dβ`, `d = βαγ`;
  `orbit_211_root` here is a deprecated alias); `weight_211`
  (`‖d‖ = 1`, `‖dβ‖ = ‖β‖`, the weight is `dβ`, `dα` or `dγ`); `weight_220` (`‖d‖ = 1`,
  `‖α‖ = ‖γ‖`, `α, γ` non-real, `β²α²` a root of modulus `‖β‖`, the weight is `β²α²`,
  `β²γ²` or `α²γ²`); **`weight_root_cases`** (`(3,1,0)` impossible, else one of the two);
  **`sieve4_weight`** (`‖d‖ = 1` and `q` has a root of modulus `‖β‖`).
* **The determinant**: `det_incQ`, `incZ_det_ne_zero`, `norm_det_cast`, `pisot_setup`
  (distinctness, `det M = βαγ`, `1 ≤ ‖βαγ‖`).
* **`thm:sieve` at `r = 4` on representatives**: `q4_root_bound`; **`sieve4`**
  (`|det M| = 1`, `det M = βαγ`, and a common root of `q₄` and `χ_S` of modulus `‖β‖`, so
  `ρ(S) = ‖β‖` given `hρ`); **`sieve4_roots`** (every root of `q₄` is `dβ, dα, dγ`, with
  `dβ` a root of `q₄`, or — only in the complex unit case — `β²α², β²γ², α²γ²`, with `β²α²`
  a root of `q₄`; never `(3,1,0)`); **`sieve4_pisot`** (Pisot-root form).
* **`prop:cocycle` as a bound on the roots of `χ_S`**: `exists_eigen_of_root_ssign`;
  **`ssign_root_bound_of_perron`** (`hρ` from a positive left `β`-eigenvector `L` of `N_C`:
  `Psc.ParikhIntertwiner.spectral_bound` with `|S| ≤ N_C`; neither strong connectivity nor
  primitivity is used); `perron_eq_pisot` (the Perron root of a primitive `M` is the Pisot
  root, hence real and positive); **`ssign_root_bound_of_primitive`** (`hρ` for primitive
  `σ`, with `L = Lrep ℓ` from `Psc.PerronExistence.perron_inc` and
  `Psc.SignedCocycle.Normalisation.rep_eigen`); **`sieve4_of_primitive`** (for primitive
  `σ`: `β = r` with `PerronData` for `M` at `r > 1`, `|det M| = 1`, `ρ(S) = β`).
* **Theorem A(ii), (iii) with the Wielandt step** (`N_C` strongly connected, a positive left
  `β`-eigenvector `L` of `N_C`, `β` real; `hρ` is derived from `L`, not assumed):
  `Psc.GaloisOrbit.aeval_conj_eq_zero` (`aeval_conj_eq_zero` here is a deprecated alias),
  `det_sq_eq_one`, `exists_real_eigen_of_root_ssign`;
  **`no_220_root`** (`β²α²` is not a root of `χ_S`: `Psc.Wielandt.no_220_eigenvalue`, with
  `γ = ᾱ` and `βαᾱ = det M = ±1` derived); **`sieve4_211`** (only `(2,1,1)` survives: `dβ`
  is a root of `q₄` and `χ_S`, and every root of `q₄` is `dβ`, `dα` or `dγ`);
  **`gauge_of_sieve4`** (Theorem A(iii): `S = d · D N_C D`, `D` an integer sign vector, via
  `Psc.Wielandt.gauge_of_real`); **`gauge_or_antiGauge_of_sieve4`** (the same in the
  vocabulary of `Psc.CocycleSpectrum`: `det M = 1` and a gauge, or `det M = −1` and an
  anti-gauge); **`theoremA_of_primitive`** (all of it for primitive `σ`, with `PerronData`
  for `M` at `r = β`, the Perron data `L = Lrep ℓ` supplied by `perron_inc` and
  `rep_eigen`; only `hSC` remains a hypothesis).
* **Controls** (see below): `w4_controls`; `m0Subst`, `inc_m0Subst`, `incQ_m0Subst`,
  `m0Subst_primitive`, `m0_det`, `m0_perron_control`, **`m0_no_degree4`**; `plasticQ`,
  `plastic_real_root`, `plastic_other`, `plastic_pisot`, `plastic_det`,
  `plastic_matrix_controls`, `plastic_perron_control`, `plasticEmpty`, `plasticEmptyNorm`,
  `plastic_empty_control`, **`plastic_weight_control`**; `q220`, `q220_natDegree`,
  `aeval_q220`, `q220_root`, `plastic_sum_roots`, **`plastic_220_control`**.

## Controls, and why no full control exists

The representative theorems (`sieve4`, `sieve4_roots`, `sieve4_pisot`, `sieve4_of_primitive`,
`no_220_root`, `sieve4_211`, `gauge_of_sieve4`, `gauge_or_antiGauge_of_sieve4`,
`theoremA_of_primitive`) are **reductio lemmas**: their hypotheses describe a hypothetical
strict component with first defect degree four over a Pisot substitution with irreducible
`χ_M`, and none is known (by Theorem A and the attack note's configuration (R), one would be
a unimodular gauge-trivial component whose existence is open).  No control meets their full
hypothesis set, and none is expected.  On a strict system or component every structural hypothesis is
discharged and they are restated as `Psc.StrictSystem.StrictSystem.sieve4`,
`Psc.StrictSystem.StrictComponent.theoremA` and `StrictComponent.gauge_or_antiGauge`; the
leave-one-out table of their hypotheses is `Psc.ReductioControls`
(`degree4Floor_leave_one_out`, and the literal three-root form of `sieve4`).  The strongest honest controls:
* state level: `w4_controls` (`Psc.Defect4.w4Norm`: `∼₃` states, a nonzero `K₄` column and
  `hρ` at `β = 1` (from `ssign_root_bound_of_perron` with `L = Lrep 1`), jointly, over the
  identity substitution; it fails only `hM` (`χ_M = (X − 1)³` is reducible) and the Pisot
  moduli); with `Psc.SectorBridge.cyc4_galoisOrbit_input` (states, a nonzero column
  and three distinct roots of `χ_M = X³ − 1`) jointly satisfiable up to irreducibility and
  the Pisot moduli;
* matrix level: `plastic_matrix_controls` (`plasticSubst`: irreducible, primitive with
  `M⁵ > 0`, Pisot, `det M = 1`, consistent with the conclusion);
* `perron_eq_pisot` has full controls on `plasticSubst` (`plastic_perron_control`) and on
  `m0Subst` (`m0_perron_control`); `ssign_root_bound_of_primitive` has only the degenerate
  full control `plastic_empty_control` (the empty child system over `plasticSubst`, where
  `χ_S = 1` has no roots).  A non-empty one would be a normalised (coincidence-free) child
  system with balanced states over a primitive Pisot substitution; none is formalized;
* the conclusion has content: `m0_no_degree4` applies `sieve4_of_primitive` to `m0Subst`
  (incidence `Psc.M0Pisot.M0`, irreducible, primitive, Pisot, `det = −2`) and proves that
  **no** normalised child system over it with `∼₃` states has a nonzero `K₄` column;
* the abstract layer has full controls: `plastic_weight_control` meets every hypothesis of
  `sieve4_weight`, `weight_root_cases` and `weight_211` (`q = χ_M`, root `β = β²αγ`);
  `plastic_220_control` meets every hypothesis of `weight_220` (`q = X³ − X² + 2X − 1`,
  roots `β²α², β²γ², α²γ²` of moduli `β, β, (β² − 1)²`).  The latter is a **negative
  control for the root-level sieve**: the modulus and Galois constraints on the roots of
  a rational `q` do not exclude `(2,2,0)`; `sieve4_211` excludes it only through the
  Wielandt step, which uses `N_C`, `|S| ≤ N_C` and `L`.

## Not proved here

* The first-defect selection in general: `r(C) = 4` is encoded directly as `∼₃` states
  and a nonzero `K₄` column; nothing about `r ≥ 5`, the general shapes
  `(m, m, m)`, `(m+1, m, m)`, `(m+1, m+1, m−1)`, `(m+1, m+1, m)` of `thm:sieve`, or its
  `|C| = 3` clauses.
* Strictness of `C` is not used: the theorems hold for every normalised child system with
  the stated hypotheses (no BPA reachability, closure or productivity hypothesis).
  Conversely, strong connectivity of `N_C` (`hSC` of `no_220_root`, `sieve4_211`,
  `gauge_of_sieve4`, `gauge_or_antiGauge_of_sieve4`, `theoremA_of_primitive`) is a
  hypothesis, not derived.
* `prop:cocycle`'s bound without Perron data: `hρ` is a hypothesis of `sieve4`,
  `sieve4_roots`, `sieve4_pisot`, discharged when a positive left `β`-eigenvector of `N_C`
  is given (`ssign_root_bound_of_perron`, in particular for primitive `σ`); for a
  non-primitive `σ` with no such eigenvector it is not derived.
* Theorem A(ii) as a statement about subspaces: `im Q₄ ⊆ ker χ_{dM}(Φ₄)` needs the
  semisimplicity of `Φ₄|_{im Q₄}`, which is not formalized; only the eigenvalue form (every
  root of `q₄` is a root of `χ_{dM}`, `sieve4_211`) is proved.  That `q₄` is then a power of
  the irreducible `χ_{dM}` is not stated.
* Theorem A(iv) (`Q₄ D = L ∘ P`, `K₄ ≠ 0` on every state) is not composed with this module
  (its parts are the `KernelCofactor`, `PerronSimple`, `ConcentrationAlgebra` rows).
* `orbit_211_root` and `aeval_conj_eq_zero` moved to `Psc.GaloisOrbit` (2026-11-09; the
  old names remain as deprecated aliases), where `orbit_211_forces_unit` and
  `im_ne_zero_of_norm_eq` now use them instead of re-deriving them.  The root and
  spectral-bound helpers shared with `Psc.Degree3Sector` (`det_eq_mul_roots`,
  `vec3_injective`, `M0_det`, `exists_eigen_of_root_ssign`, `ssign_root_bound_of_perron`)
  live in `Psc.SectorBridge`.
-/

namespace Psc.Degree4Floor

open Polynomial Matrix

/-! ### The roots of a rational `3 × 3` matrix with irreducible `χ_M` -/

section Roots

/-- `χ_M` of a `3 × 3` matrix has degree three. -/
theorem natDegree_charpoly (M : Matrix (Fin 3) (Fin 3) ℚ) : M.charpoly.natDegree = 3 := by
  rw [charpoly_natDegree_eq_dim, Fintype.card_fin]

/-- **The other two roots.**  If `χ_M` is irreducible and `β` is one of its complex roots,
there are complex roots `α, γ` with `β, α, γ` pairwise distinct, and every complex root
of `χ_M` is one of them (`Psc.SectorBridge.exists_distinct_roots`). -/
theorem exists_other_roots (M : Matrix (Fin 3) (Fin 3) ℚ) (hM : Irreducible M.charpoly)
    {β : ℂ} (hβ : aeval β M.charpoly = 0) :
    ∃ α γ : ℂ, aeval α M.charpoly = 0 ∧ aeval γ M.charpoly = 0 ∧ β ≠ α ∧ β ≠ γ ∧ α ≠ γ ∧
      ∀ z : ℂ, aeval z M.charpoly = 0 → z = β ∨ z = α ∨ z = γ := by
  obtain ⟨x, hx, hroot, hall⟩ := Psc.SectorBridge.exists_distinct_roots (L := ℂ) M hM
  have h01 : x 0 ≠ x 1 := hx.ne (by decide)
  have h02 : x 0 ≠ x 2 := hx.ne (by decide)
  have h12 : x 1 ≠ x 2 := hx.ne (by decide)
  have hall' : ∀ z : ℂ, aeval z M.charpoly = 0 → z = x 0 ∨ z = x 1 ∨ z = x 2 := by
    intro z hz
    obtain ⟨j, rfl⟩ := hall z hz
    fin_cases j <;> simp
  obtain ⟨i, rfl⟩ := hall β hβ
  fin_cases i
  · refine ⟨x 1, x 2, hroot 1, hroot 2, h01, h02, h12, fun z hz => ?_⟩
    exact hall' z hz
  · refine ⟨x 0, x 2, hroot 0, hroot 2, h01.symm, h12, h02, fun z hz => ?_⟩
    rcases hall' z hz with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · refine ⟨x 0, x 1, hroot 0, hroot 1, h02.symm, h12.symm, h01, fun z hz => ?_⟩
    rcases hall' z hz with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h

end Roots

/-! ### The sieve at `r = 4` for an arbitrary rational `q` (composition of `GaloisOrbit`) -/

section Abstract

variable {f : ℚ[X]} (hf : Irreducible f) (hdeg : f.natDegree = 3) {β α γ : ℂ}
    (hβ : aeval β f = 0) (hα : aeval α f = 0) (hγ : aeval γ f = 0)
    (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ)
include hf hdeg hβ hα hγ hβα hβγ hαγ

/-- **The `(2,1,1)` orbit contains `d β`**: moved to `Psc.GaloisOrbit.orbit_211_root`
(2026-11-09); this alias keeps the old name. -/
@[deprecated Psc.GaloisOrbit.orbit_211_root (since := "2026-11-09")]
alias orbit_211_root := Psc.GaloisOrbit.orbit_211_root

/-- **A root of shape `(2,1,1)`**: with `1 ≤ ‖d‖` and every root of `q` of modulus at most
`‖β‖`, `‖d‖ = 1`, `d β` is a root of `q` of modulus `‖β‖`, and the given root is one of
`d β`, `d α`, `d γ`. -/
theorem weight_211 (hdet : 1 ≤ ‖β * α * γ‖) (q : ℚ[X])
    (hbound : ∀ z : ℂ, aeval z q = 0 → ‖z‖ ≤ ‖β‖) (a b c : ℕ)
    (habc : (a, b, c) = (2, 1, 1) ∨ (a, b, c) = (1, 2, 1) ∨ (a, b, c) = (1, 1, 2))
    (hq : aeval (β ^ a * α ^ b * γ ^ c) q = 0) :
    ‖β * α * γ‖ = 1 ∧ aeval (β * (β * α * γ)) q = 0 ∧ ‖β * (β * α * γ)‖ = ‖β‖ ∧
      (β ^ a * α ^ b * γ ^ c = β * (β * α * γ) ∨ β ^ a * α ^ b * γ ^ c = α * (β * α * γ) ∨
        β ^ a * α ^ b * γ ^ c = γ * (β * α * γ)) := by
  have hunit := Psc.GaloisOrbit.orbit_211_forces_unit hf hdeg hβ hα hγ hβα hβγ hαγ hdet q a b c
    habc hq hbound
  refine ⟨hunit, Psc.GaloisOrbit.orbit_211_root hf hdeg hβ hα hγ hβα hβγ hαγ q a b c habc hq,
    by rw [norm_mul, hunit, mul_one], ?_⟩
  rcases habc with h | h | h <;> simp only [Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl, rfl⟩ := h
  · exact Or.inl (by ring)
  · exact Or.inr (Or.inl (by ring))
  · exact Or.inr (Or.inr (by ring))

/-- **A root of shape `(2,2,0)`**: with `1 < ‖β‖`, `1 ≤ ‖d‖` and the modulus bound,
`‖d‖ = 1`, `‖α‖ = ‖γ‖`, `α` and `γ` are non-real
(`Psc.GaloisOrbit.orbit_220_forces_complex_unit`), `β² α²` and `β² γ²` are roots of `q`
(`Psc.GaloisOrbit.orbit_220_both`) of modulus `‖β‖`, and the given root is one of
`β² α²`, `β² γ²`, `α² γ²`. -/
theorem weight_220 (hβ1 : 1 < ‖β‖) (hdet : 1 ≤ ‖β * α * γ‖) (q : ℚ[X])
    (hbound : ∀ z : ℂ, aeval z q = 0 → ‖z‖ ≤ ‖β‖) (a b c : ℕ)
    (habc : (a, b, c) = (2, 2, 0) ∨ (a, b, c) = (2, 0, 2) ∨ (a, b, c) = (0, 2, 2))
    (hq : aeval (β ^ a * α ^ b * γ ^ c) q = 0) :
    ‖β * α * γ‖ = 1 ∧ ‖α‖ = ‖γ‖ ∧ α.im ≠ 0 ∧ γ.im ≠ 0 ∧
      aeval (β ^ 2 * α ^ 2) q = 0 ∧ aeval (β ^ 2 * γ ^ 2) q = 0 ∧ ‖β ^ 2 * α ^ 2‖ = ‖β‖ ∧
      (β ^ a * α ^ b * γ ^ c = β ^ 2 * α ^ 2 ∨ β ^ a * α ^ b * γ ^ c = β ^ 2 * γ ^ 2 ∨
        β ^ a * α ^ b * γ ^ c = α ^ 2 * γ ^ 2) := by
  obtain ⟨hunit, hαγn, hαr, hγr⟩ := Psc.GaloisOrbit.orbit_220_forces_complex_unit hf hdeg hβ hα
    hγ hβα hβγ hαγ hβ1 hdet q a b c habc hq hbound
  obtain ⟨hA, hG⟩ := Psc.GaloisOrbit.orbit_220_both hf hdeg hβ hα hγ hβα hβγ hαγ q a b c habc hq
  have hmod : ‖β ^ 2 * α ^ 2‖ = ‖β‖ := by
    have h1 : ‖β‖ * ‖α‖ * ‖γ‖ = 1 := by rw [← norm_mul, ← norm_mul]; exact hunit
    rw [norm_mul, norm_pow, norm_pow]
    calc ‖β‖ ^ 2 * ‖α‖ ^ 2 = ‖β‖ * (‖β‖ * ‖α‖ * ‖α‖) := by ring
      _ = ‖β‖ := by rw [← hαγn] at h1; rw [h1, mul_one]
  refine ⟨hunit, hαγn, hαr, hγr, hA, hG, hmod, ?_⟩
  rcases habc with h | h | h <;> simp only [Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl, rfl⟩ := h
  · exact Or.inl (by ring)
  · exact Or.inr (Or.inl (by ring))
  · exact Or.inr (Or.inr (by ring))

/-- **The sieve at `r = 4`, one weight root.**  Let `β, α, γ` be the roots of the
irreducible rational cubic `f`, with `1 < ‖β‖`, `‖α‖ < 1`, `‖γ‖ < 1` and `1 ≤ ‖βαγ‖`;
let `q : ℚ[X]` have every complex root of modulus at most `‖β‖`.  If `q` vanishes at a
weight `β^a α^b γ^c` with `(a, b, c)` a permutation of `(3,1,0)`, `(2,2,0)` or `(2,1,1)`,
then that weight is not of shape `(3,1,0)` (`Psc.GaloisOrbit.orbit_310_excluded`), and
either it is one of `d β, d α, d γ` (shape `(2,1,1)`, `d = β α γ`, `‖d‖ = 1`, and `d β`
is a root of `q`), or the complex unit case holds (`‖d‖ = 1`, `‖α‖ = ‖γ‖`, `α`, `γ`
non-real) and it is one of `β²α², β²γ², α²γ²` (shape `(2,2,0)`, and `β²α²` is a root of
`q` of modulus `‖β‖`). -/
theorem weight_root_cases (hβ1 : 1 < ‖β‖) (hα1 : ‖α‖ < 1) (hγ1 : ‖γ‖ < 1)
    (hdet : 1 ≤ ‖β * α * γ‖) (q : ℚ[X]) (hbound : ∀ z : ℂ, aeval z q = 0 → ‖z‖ ≤ ‖β‖)
    (a b c : ℕ)
    (habc : ((a, b, c) = (3, 1, 0) ∨ (a, b, c) = (3, 0, 1) ∨ (a, b, c) = (1, 3, 0) ∨
          (a, b, c) = (0, 3, 1) ∨ (a, b, c) = (1, 0, 3) ∨ (a, b, c) = (0, 1, 3)) ∨
        ((a, b, c) = (2, 2, 0) ∨ (a, b, c) = (2, 0, 2) ∨ (a, b, c) = (0, 2, 2)) ∨
        ((a, b, c) = (2, 1, 1) ∨ (a, b, c) = (1, 2, 1) ∨ (a, b, c) = (1, 1, 2)))
    (hq : aeval (β ^ a * α ^ b * γ ^ c) q = 0) :
    ‖β * α * γ‖ = 1 ∧
      ((aeval (β * (β * α * γ)) q = 0 ∧
          (β ^ a * α ^ b * γ ^ c = β * (β * α * γ) ∨ β ^ a * α ^ b * γ ^ c = α * (β * α * γ) ∨
            β ^ a * α ^ b * γ ^ c = γ * (β * α * γ))) ∨
        (‖α‖ = ‖γ‖ ∧ α.im ≠ 0 ∧ γ.im ≠ 0 ∧ aeval (β ^ 2 * α ^ 2) q = 0 ∧
          (β ^ a * α ^ b * γ ^ c = β ^ 2 * α ^ 2 ∨ β ^ a * α ^ b * γ ^ c = β ^ 2 * γ ^ 2 ∨
            β ^ a * α ^ b * γ ^ c = α ^ 2 * γ ^ 2))) := by
  rcases habc with h310 | h220 | h211
  · exfalso
    obtain ⟨z, hz, hlt, -⟩ := Psc.GaloisOrbit.orbit_310_excluded hf hdeg hβ hα hγ hβα hβγ hαγ
      hβ1 hα1 hγ1 hdet q a b c h310 hq
    exact absurd (hbound z hz) (not_le.2 hlt)
  · obtain ⟨hunit, hαγn, hαr, hγr, hA, -, -, hv⟩ :=
      weight_220 hf hdeg hβ hα hγ hβα hβγ hαγ hβ1 hdet q hbound a b c h220 hq
    exact ⟨hunit, Or.inr ⟨hαγn, hαr, hγr, hA, hv⟩⟩
  · obtain ⟨hunit, hB, -, hv⟩ := weight_211 hf hdeg hβ hα hγ hβα hβγ hαγ hdet q hbound a b c h211 hq
    exact ⟨hunit, Or.inl ⟨hB, hv⟩⟩

/-- **`thm:sieve` at `r = 4` for an arbitrary rational `q`**: under the hypotheses of
`weight_root_cases`, `‖β α γ‖ = 1` and `q` has a complex root of modulus exactly `‖β‖`
(`d β` in shape `(2,1,1)`, `β² α²` in shape `(2,2,0)`). -/
theorem sieve4_weight (hβ1 : 1 < ‖β‖) (hα1 : ‖α‖ < 1) (hγ1 : ‖γ‖ < 1)
    (hdet : 1 ≤ ‖β * α * γ‖) (q : ℚ[X]) (hbound : ∀ z : ℂ, aeval z q = 0 → ‖z‖ ≤ ‖β‖)
    (a b c : ℕ)
    (habc : ((a, b, c) = (3, 1, 0) ∨ (a, b, c) = (3, 0, 1) ∨ (a, b, c) = (1, 3, 0) ∨
          (a, b, c) = (0, 3, 1) ∨ (a, b, c) = (1, 0, 3) ∨ (a, b, c) = (0, 1, 3)) ∨
        ((a, b, c) = (2, 2, 0) ∨ (a, b, c) = (2, 0, 2) ∨ (a, b, c) = (0, 2, 2)) ∨
        ((a, b, c) = (2, 1, 1) ∨ (a, b, c) = (1, 2, 1) ∨ (a, b, c) = (1, 1, 2)))
    (hq : aeval (β ^ a * α ^ b * γ ^ c) q = 0) :
    ‖β * α * γ‖ = 1 ∧ ∃ z : ℂ, aeval z q = 0 ∧ ‖z‖ = ‖β‖ := by
  rcases habc with h310 | h220 | h211
  · exfalso
    obtain ⟨z, hz, hlt, -⟩ := Psc.GaloisOrbit.orbit_310_excluded hf hdeg hβ hα hγ hβα hβγ hαγ
      hβ1 hα1 hγ1 hdet q a b c h310 hq
    exact absurd (hbound z hz) (not_le.2 hlt)
  · obtain ⟨hunit, -, -, -, hA, -, hmod, -⟩ :=
      weight_220 hf hdeg hβ hα hγ hβα hβγ hαγ hβ1 hdet q hbound a b c h220 hq
    exact ⟨hunit, _, hA, hmod⟩
  · obtain ⟨hunit, hB, hmod, -⟩ :=
      weight_211 hf hdeg hβ hα hγ hβα hβγ hαγ hdet q hbound a b c h211 hq
    exact ⟨hunit, _, hB, hmod⟩

end Abstract

/-! ### The determinant of the incidence matrix -/

section Det

open Psc.Binomial Psc.ParikhRank Psc.Degree2Sector

/-- `det M` over `ℚ` is the cast of the integer determinant `det (incZ S)`. -/
theorem det_incQ (S : ChildSystem (Fin 3)) : (incQ S).det = ((incZ S).det : ℚ) := by
  rw [← incZ_map_rat S]
  exact ((Int.castRingHom ℚ).map_det (incZ S)).symm

/-- An irreducible `χ_M` has a nonzero integer determinant
(`Psc.Cyclicity.det_ne_zero_of_irreducible`). -/
theorem incZ_det_ne_zero {S : ChildSystem (Fin 3)} (hM : Irreducible (incQ S).charpoly) :
    (incZ S).det ≠ 0 := by
  have h := Psc.Cyclicity.det_ne_zero_of_irreducible (incQ S) hM
  rw [det_incQ] at h
  exact_mod_cast h

/-- `‖det M‖ = |det M|` for the complex cast of the integer determinant. -/
theorem norm_det_cast (S : ChildSystem (Fin 3)) :
    ‖(((incQ S).det : ℚ) : ℂ)‖ = |((incZ S).det : ℝ)| := by
  rw [det_incQ, Rat.cast_intCast, Complex.norm_intCast]

/-- **The setting of `Psc.GaloisOrbit` from the Pisot moduli.**  For complex roots `β, α, γ`
of `χ_M` with `α ≠ γ`, `1 < ‖β‖`, `‖α‖ < 1`, `‖γ‖ < 1`: the three are pairwise distinct,
`det M = β α γ`, and `1 ≤ ‖β α γ‖` because `det M` is a nonzero integer (`χ_M`
irreducible). -/
theorem pisot_setup {S : ChildSystem (Fin 3)} (hM : Irreducible (incQ S).charpoly) {β α γ : ℂ}
    (hβ : aeval β (incQ S).charpoly = 0) (hα : aeval α (incQ S).charpoly = 0)
    (hγ : aeval γ (incQ S).charpoly = 0) (hαγ : α ≠ γ) (hβ1 : 1 < ‖β‖) (hα1 : ‖α‖ < 1)
    (hγ1 : ‖γ‖ < 1) :
    β ≠ α ∧ β ≠ γ ∧ (((incQ S).det : ℚ) : ℂ) = β * α * γ ∧ 1 ≤ ‖β * α * γ‖ := by
  have hβα : β ≠ α := fun h => by rw [h] at hβ1; linarith
  have hβγ : β ≠ γ := fun h => by rw [h] at hβ1; linarith
  have hd := SectorBridge.det_eq_mul_roots (incQ S) hβ hα hγ hβα hβγ hαγ
  refine ⟨hβα, hβγ, hd, ?_⟩
  rw [← hd, norm_det_cast]
  have := Int.one_le_abs (incZ_det_ne_zero hM)
  exact_mod_cast this

end Det

/-! ### `thm:sieve` at `r = 4` on normalised representatives -/

section Rep

open Psc.Binomial Psc.SignedCocycle Psc.ParikhRank Psc.Degree2Sector Psc.SectorBridge

variable {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Psc.Defect4.Equiv3 T.1 T.2)

/-- A bound on the roots of `χ_S` bounds the roots of `q₄ ∣ χ_S` (`q4_dvd_ssign`). -/
theorem q4_root_bound {B : ℝ} (hρ : ∀ μ : ℂ, aeval μ (SsignQ P).charpoly = 0 → ‖μ‖ ≤ B) :
    ∀ z : ℂ, aeval z (q4 P hbal) = 0 → ‖z‖ ≤ B := fun z hz =>
  hρ z (aeval_eq_zero_of_dvd_aeval_eq_zero (q4_dvd_ssign P hbal) hz)

/-- **`thm:sieve` at `r = 4`** (`docs/c4-concentration-attack-2026-11-06.md`, Theorem A(i)).
Let `P` normalise a child system over `Fin 3` whose states are all `∼₃` (`K₁ = K₂ = K₃ = 0`)
with some `K₄` column nonzero (`r(C) = 4`), let `χ_M` be irreducible with complex roots
`β, α, γ`, `α ≠ γ`, `1 < ‖β‖`, `‖α‖ < 1`, `‖γ‖ < 1`, and assume the bound of
`prop:cocycle` on the roots of `χ_S`: every one has modulus at most `‖β‖`.  Then
`|det M| = 1`, `det M = β α γ`, and `q₄ = χ(Φ₄|_{im Q₄})` (hence `χ_S`) has a root of
modulus exactly `‖β‖`: `ρ(S) = ‖β‖`.  A reductio lemma (no known child system meets every
hypothesis); controls of each hypothesis group are listed in the module docstring, and
`m0_no_degree4` applies it to a non-unimodular Pisot substitution. -/
theorem sieve4 (hM : Irreducible (incQ S).charpoly)
    (hK : ∃ j : P.Rep, Psc.Defect4Lie.k4Vec j.1.1 j.1.2 ≠ 0) {β α γ : ℂ}
    (hβ : aeval β (incQ S).charpoly = 0) (hα : aeval α (incQ S).charpoly = 0)
    (hγ : aeval γ (incQ S).charpoly = 0) (hαγ : α ≠ γ) (hβ1 : 1 < ‖β‖) (hα1 : ‖α‖ < 1)
    (hγ1 : ‖γ‖ < 1) (hρ : ∀ μ : ℂ, aeval μ (SsignQ P).charpoly = 0 → ‖μ‖ ≤ ‖β‖) :
    |(incZ S).det| = 1 ∧ (((incQ S).det : ℚ) : ℂ) = β * α * γ ∧
      ∃ μ : ℂ, aeval μ (q4 P hbal) = 0 ∧ aeval μ (SsignQ P).charpoly = 0 ∧ ‖μ‖ = ‖β‖ := by
  obtain ⟨hβα, hβγ, hd, hdet⟩ := pisot_setup hM hβ hα hγ hαγ hβ1 hα1 hγ1
  obtain ⟨a, b, c, habc, hq⟩ := galoisOrbit_input_q4 P hbal hβ hα hγ hβα hβγ hαγ hK
  obtain ⟨hunit, z, hz, hzn⟩ := sieve4_weight hM (natDegree_charpoly _) hβ hα hγ hβα hβγ hαγ
    hβ1 hα1 hγ1 hdet (q4 P hbal) (q4_root_bound P hbal hρ) a b c habc hq
  refine ⟨?_, hd, z, hz, aeval_eq_zero_of_dvd_aeval_eq_zero (q4_dvd_ssign P hbal) hz, hzn⟩
  rw [← hd, norm_det_cast] at hunit
  exact_mod_cast hunit

/-- **Every eigenvalue of `Φ₄` on `im Q₄`**, under the hypotheses of `sieve4`: each root
`z` of `q₄` is `d β`, `d α` or `d γ` (`d = β α γ = det M`; shape `(2,1,1)`, and then `d β`
is a root of `q₄`), or the complex unit case holds (`‖α‖ = ‖γ‖`, `α`, `γ` non-real) and
`z` is `β²α²`, `β²γ²` or `α²γ²` (shape `(2,2,0)`, and then `β²α²` is a root of `q₄`).
The shape `(3,1,0)` never occurs. -/
theorem sieve4_roots (hM : Irreducible (incQ S).charpoly) {β α γ : ℂ}
    (hβ : aeval β (incQ S).charpoly = 0) (hα : aeval α (incQ S).charpoly = 0)
    (hγ : aeval γ (incQ S).charpoly = 0) (hαγ : α ≠ γ) (hβ1 : 1 < ‖β‖) (hα1 : ‖α‖ < 1)
    (hγ1 : ‖γ‖ < 1) (hρ : ∀ μ : ℂ, aeval μ (SsignQ P).charpoly = 0 → ‖μ‖ ≤ ‖β‖) {z : ℂ}
    (hz : aeval z (q4 P hbal) = 0) :
    (aeval (β * (β * α * γ)) (q4 P hbal) = 0 ∧
        (z = β * (β * α * γ) ∨ z = α * (β * α * γ) ∨ z = γ * (β * α * γ))) ∨
      (‖α‖ = ‖γ‖ ∧ α.im ≠ 0 ∧ γ.im ≠ 0 ∧ aeval (β ^ 2 * α ^ 2) (q4 P hbal) = 0 ∧
        (z = β ^ 2 * α ^ 2 ∨ z = β ^ 2 * γ ^ 2 ∨ z = α ^ 2 * γ ^ 2)) := by
  obtain ⟨hβα, hβγ, -, hdet⟩ := pisot_setup hM hβ hα hγ hαγ hβ1 hα1 hγ1
  have hroot : ∀ i, aeval (![β, α, γ] i) (incQ S).charpoly = 0 := by
    intro i; fin_cases i <;> simpa
  obtain ⟨-, κ, -, hsh, rfl⟩ := root_q4 P hbal ![β, α, γ] (SectorBridge.vec3_injective hβα hβγ hαγ) hroot hz
  have hm : Psc.LieWeights.mono ![β, α, γ] κ = β ^ κ 0 * α ^ κ 1 * γ ^ κ 2 := by
    rw [mono_fin_three]; rfl
  rw [hm] at hz ⊢
  exact (weight_root_cases hM (natDegree_charpoly _) hβ hα hγ hβα hβγ hαγ hβ1 hα1 hγ1 hdet
    (q4 P hbal) (q4_root_bound P hbal hρ) (κ 0) (κ 1) (κ 2) hsh.triple hz).2

/-- **`sieve4` for a Pisot root.**  The same conclusion when `β` is a complex root of the
irreducible `χ_M` with `1 < ‖β‖` and every other complex root of modulus `< 1` (the other
two roots are produced by `exists_other_roots`; no distinctness hypothesis). -/
theorem sieve4_pisot (hM : Irreducible (incQ S).charpoly)
    (hK : ∃ j : P.Rep, Psc.Defect4Lie.k4Vec j.1.1 j.1.2 ≠ 0) {β : ℂ}
    (hβ : aeval β (incQ S).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z (incQ S).charpoly = 0 → z ≠ β → ‖z‖ < 1)
    (hρ : ∀ μ : ℂ, aeval μ (SsignQ P).charpoly = 0 → ‖μ‖ ≤ ‖β‖) :
    |(incZ S).det| = 1 ∧
      ∃ μ : ℂ, aeval μ (q4 P hbal) = 0 ∧ aeval μ (SsignQ P).charpoly = 0 ∧ ‖μ‖ = ‖β‖ := by
  obtain ⟨α, γ, hα, hγ, hβα, hβγ, hαγ, -⟩ := exists_other_roots _ hM hβ
  obtain ⟨h1, -, h2⟩ := sieve4 P hbal hM hK hβ hα hγ hαγ hβ1 (hpisot α hα (Ne.symm hβα))
    (hpisot γ hγ (Ne.symm hβγ)) hρ
  exact ⟨h1, h2⟩

end Rep

/-! ### Discharging the spectral bound from primitivity -/

section Primitive

open Psc.Binomial Psc.Incidence Psc.SignedCocycle Psc.ParikhRank Psc.Degree2Sector
  Psc.SectorBridge Psc.PerronExistence

/-- **The Perron root is the Pisot root.**  If `r` is the Perron root of the incidence
matrix of `s` (`PerronData`) and `β` is a complex root of `χ_M` with `1 < ‖β‖` and every
other root of modulus `< 1`, then `β = r`; in particular `β` is real, positive, and
`‖β‖ = r`. -/
theorem perron_eq_pisot {s : Fin 3 → List (Fin 3)} {r : ℝ} {ℓ u : Fin 3 → ℝ}
    (h : PerronData ((inc s).map (Nat.cast : ℕ → ℝ)) r ℓ u) {β : ℂ}
    (hβ : aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 → z ≠ β →
      ‖z‖ < 1) : (r : ℂ) = β := by
  set Mq := (inc s).map (Nat.cast : ℕ → ℚ)
  have hcR : Mq.map (algebraMap ℚ ℝ) = (inc s).map (Nat.cast : ℕ → ℝ) := by ext; simp [Mq]
  have hcC : Mq.map (algebraMap ℚ ℂ) = ((inc s).map (Nat.cast : ℕ → ℝ)).map ((↑) : ℝ → ℂ) := by
    ext; simp [Mq]
  have hrR : aeval r Mq.charpoly = 0 := by
    rw [← eval_map_algebraMap, ← Matrix.charpoly_map, hcR]; exact h.isRoot
  have hrC : aeval (r : ℂ) Mq.charpoly = 0 := by
    have := aeval_algebraMap_apply ℂ r Mq.charpoly
    rw [hrR, map_zero] at this
    simpa using this
  have hle : ‖β‖ ≤ r :=
    h.norm_le β (by rw [← hcC, Matrix.charpoly_map, eval_map_algebraMap]; exact hβ)
  by_contra hne
  have := hpisot _ hrC hne
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h.pos] at this
  linarith

variable {S : ChildSystem (Fin 3)} (P : Normalisation S)

/-- **`prop:cocycle`'s `ρ(S) ≤ β` for a primitive substitution** with a Pisot root `β` and
balanced states: the hypothesis `hρ` of `sieve4`.  The Perron root `r` of `M` is `β`
(`perron_eq_pisot`), and `L = Lrep ℓ` for the left Perron vector `ℓ` of
`Psc.PerronExistence.perron_inc` is a positive left `r`-eigenvector of `N_C`
(`Psc.SignedCocycle.Normalisation.rep_eigen`, `lrep_pos`), so `ssign_root_bound_of_perron`
applies. -/
theorem ssign_root_bound_of_primitive (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc S.s ^ k) a c)
    (hbal : ∀ T ∈ S.C, Equiv1 T.1 T.2) {β : ℂ} (hβ : aeval β (incQ S).charpoly = 0)
    (hβ1 : 1 < ‖β‖) (hpisot : ∀ z : ℂ, aeval z (incQ S).charpoly = 0 → z ≠ β → ‖z‖ < 1) :
    ∀ μ : ℂ, aeval μ (SsignQ P).charpoly = 0 → ‖μ‖ ≤ ‖β‖ := by
  obtain ⟨r, ℓ, u, h, -, -⟩ := perron_inc S.s hprim
  have hr := perron_eq_pisot h hβ hβ1 hpisot
  rw [← hr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h.pos]
  exact SectorBridge.ssign_root_bound_of_perron P _ (P.lrep_pos ℓ h.left_pos (P.top_ne_nil hbal))
    (P.rep_eigen ℓ r h.left hbal)

/-- **`thm:sieve` at `r = 4` for a primitive substitution** (the corollary of `sieve4`
with `prop:cocycle` discharged).  Let `σ = S.s` be primitive, `χ_M` irreducible with a
Pisot root `β` (`1 < ‖β‖`, every other root of modulus `< 1`), `P` a normalisation with
`∼₃` states and a nonzero `K₄` column.  Then `β = r` for a real `r > 1` that is the Perron
root of `M` (`PerronData` for `M` at `r`, from `Psc.PerronExistence.perron_inc`, and
`perron_eq_pisot`), `|det M| = 1`, every root of `χ_S` has modulus at most `‖β‖ = r`, and
`q₄` (hence `χ_S`) has a root of modulus `‖β‖`: `ρ(S) = β`. -/
theorem sieve4_of_primitive (hbal : ∀ T ∈ S.C, Psc.Defect4.Equiv3 T.1 T.2)
    (hM : Irreducible (incQ S).charpoly)
    (hK : ∃ j : P.Rep, Psc.Defect4Lie.k4Vec j.1.1 j.1.2 ≠ 0)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc S.s ^ k) a c) {β : ℂ}
    (hβ : aeval β (incQ S).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z (incQ S).charpoly = 0 → z ≠ β → ‖z‖ < 1) :
    (∃ (r : ℝ) (ℓ u : Fin 3 → ℝ), PerronData ((inc S.s).map (Nat.cast : ℕ → ℝ)) r ℓ u ∧
        1 < r ∧ (r : ℂ) = β) ∧ |(incZ S).det| = 1 ∧
      (∀ μ : ℂ, aeval μ (SsignQ P).charpoly = 0 → ‖μ‖ ≤ ‖β‖) ∧
      ∃ μ : ℂ, aeval μ (q4 P hbal) = 0 ∧ aeval μ (SsignQ P).charpoly = 0 ∧ ‖μ‖ = ‖β‖ := by
  have hρ := ssign_root_bound_of_primitive P hprim (fun T hT => (hbal T hT).1.1) hβ hβ1 hpisot
  obtain ⟨r, ℓ, u, h, -, -⟩ := perron_inc S.s hprim
  have hr := perron_eq_pisot h hβ hβ1 hpisot
  have hr1 : 1 < r := by
    rw [← hr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h.pos] at hβ1; exact hβ1
  obtain ⟨hunit, hμ⟩ := sieve4_pisot P hbal hM hK hβ hβ1 hpisot hρ
  exact ⟨⟨r, ℓ, u, h, hr1, hr⟩, hunit, hρ, hμ⟩

end Primitive

/-! ### Theorem A(ii), (iii): Wielandt excludes `(2,2,0)`; the gauge -/

section Wielandt

open Psc.Binomial Psc.Incidence Psc.SignedCocycle Psc.ParikhRank Psc.Degree2Sector
  Psc.SectorBridge Psc.PerronExistence Psc.PerronCore

/-- Complex conjugation permutes the roots of a rational polynomial: moved to
`Psc.GaloisOrbit.aeval_conj_eq_zero` (2026-11-09); this alias keeps the old name. -/
@[deprecated Psc.GaloisOrbit.aeval_conj_eq_zero (since := "2026-11-09")]
alias aeval_conj_eq_zero := Psc.GaloisOrbit.aeval_conj_eq_zero

/-- `det M = ±1` as a complex number when `|det M| = 1`, so `(det M)² = 1`. -/
theorem det_sq_eq_one {S : ChildSystem (Fin 3)} (hunit : |(incZ S).det| = 1) :
    ((((incQ S).det : ℚ) : ℂ)) ^ 2 = 1 := by
  rw [det_incQ, Rat.cast_intCast]
  rcases (abs_eq zero_le_one).1 hunit with h | h <;> rw [h] <;> norm_num

variable {S : ChildSystem (Fin 3)} (P : Normalisation S)

/-- A complex root of `χ_S` is an eigenvalue of the real cast of `S`, in the form
`Psc.Wielandt` takes it. -/
theorem exists_real_eigen_of_root_ssign {μ : ℂ} (hμ : aeval μ (SsignQ P).charpoly = 0) :
    ∃ x : P.Rep → ℂ, x ≠ 0 ∧ (P.Ssign.map (Int.cast : ℤ → ℝ)).map ((↑) : ℝ → ℂ) *ᵥ x = μ • x := by
  obtain ⟨x, hx0, hx⟩ := SectorBridge.exists_eigen_of_root_ssign P hμ
  exact ⟨x, hx0, by rw [Psc.CocycleSpectrum.ssign_map_real]; exact hx⟩

/-- **Theorem A(ii), the `(2,2,0)` eigenvalue is impossible** (`Psc.Wielandt.no_220_eigenvalue`
on `N = N_C`, the cocycle `S` and `|S| ≤ N_C`).  Let `χ_M` be irreducible with complex roots
`β, α, γ`, `β` real `> 1`, `‖α‖, ‖γ‖ < 1`, `α ≠ γ`, `α` non-real, and `|det M| = 1`; let
`N_C` be strongly connected with a positive left eigenvector `L` for `β`.  Then `β² α²` is
not a root of `χ_S`.  (`γ = ᾱ` and `β α ᾱ = det M = ±1` are derived here.)  A reductio
lemma: the matrix-level hypotheses (and `β²α²` a root of a rational `q` with roots of modulus
`≤ β`) hold for the plastic roots (`plastic_220_control`); no child system with this Perron
data at `β > 1` is known. -/
theorem no_220_root (hM : Irreducible (incQ S).charpoly) {β : ℝ} {α γ : ℂ}
    (hβ : aeval (β : ℂ) (incQ S).charpoly = 0) (hα : aeval α (incQ S).charpoly = 0)
    (hγ : aeval γ (incQ S).charpoly = 0) (hαγ : α ≠ γ) (hβ1 : 1 < β) (hα1 : ‖α‖ < 1)
    (hγ1 : ‖γ‖ < 1) (hαr : α.im ≠ 0) (hunit : |(incZ S).det| = 1)
    (hSC : StronglyConnected (P.Nrep.map (Nat.cast : ℕ → ℝ))) (L : P.Rep → ℝ)
    (hL : ∀ i, 0 < L i) (hLN : L ᵥ* P.Nrep.map (Nat.cast : ℕ → ℝ) = β • L)
    (h220 : aeval ((β : ℂ) ^ 2 * α ^ 2) (SsignQ P).charpoly = 0) : False := by
  have hβα : (β : ℂ) ≠ α := fun h => hαr (by rw [← h]; simp)
  have hβγ : (β : ℂ) ≠ γ := fun h => by
    rw [← h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at hγ1; linarith
  have hcγ : starRingEnd ℂ α = γ := by
    rcases Psc.GaloisOrbit.root_eq_of_three hM.ne_zero (natDegree_charpoly _) hβ hα hγ hβα hβγ
      hαγ (Psc.GaloisOrbit.aeval_conj_eq_zero hα) with h | h | h
    · exfalso; apply hαr
      have : α = starRingEnd ℂ (β : ℂ) := by rw [← h, Complex.conj_conj]
      rw [this, Complex.conj_ofReal, Complex.ofReal_im]
    · exact absurd (Complex.conj_eq_iff_im.1 h) hαr
    · exact h
  have hd := SectorBridge.det_eq_mul_roots (incQ S) hβ hα hγ hβα hβγ hαγ
  obtain ⟨x, hx0, hx⟩ := exists_real_eigen_of_root_ssign P h220
  exact Psc.Wielandt.no_220_eigenvalue _ hM (natDegree_charpoly _) β hβ1 hβ α hα hαr hα1 _
    (by rw [hcγ, hd]) (det_sq_eq_one hunit) _ hSC L hL hLN _
    (Psc.CocycleSpectrum.ssign_real_abs_le P) x hx0 hx

variable (hbal : ∀ T ∈ S.C, Psc.Defect4.Equiv3 T.1 T.2)

/-- **Theorem A(ii): only the `(2,1,1)` sector survives**, on the level of eigenvalues.
Under the hypotheses of `sieve4` with `β` real and `hρ` replaced by the Perron data of
`Psc.Wielandt` (`N_C` strongly connected, `L > 0`, `L N_C = β L`; `hρ` is then derived by
`ssign_root_bound_of_perron`): `|det M| = 1`; `d β` (`d = det M = ±1`) is a root of `q₄` and
of `χ_S`; and every root of `q₄ = χ(Φ₄|_{im Q₄})` is `d β`, `d α` or `d γ`, i.e. a root of
`χ_{dM}`. -/
theorem sieve4_211 (hM : Irreducible (incQ S).charpoly)
    (hK : ∃ j : P.Rep, Psc.Defect4Lie.k4Vec j.1.1 j.1.2 ≠ 0) {β : ℝ} {α γ : ℂ}
    (hβ : aeval (β : ℂ) (incQ S).charpoly = 0) (hα : aeval α (incQ S).charpoly = 0)
    (hγ : aeval γ (incQ S).charpoly = 0) (hαγ : α ≠ γ) (hβ1 : 1 < β) (hα1 : ‖α‖ < 1)
    (hγ1 : ‖γ‖ < 1) (hSC : StronglyConnected (P.Nrep.map (Nat.cast : ℕ → ℝ)))
    (L : P.Rep → ℝ) (hL : ∀ i, 0 < L i) (hLN : L ᵥ* P.Nrep.map (Nat.cast : ℕ → ℝ) = β • L) :
    |(incZ S).det| = 1 ∧ aeval (((incZ S).det : ℂ) * β) (q4 P hbal) = 0 ∧
      aeval (((incZ S).det : ℂ) * β) (SsignQ P).charpoly = 0 ∧
      ∀ z : ℂ, aeval z (q4 P hbal) = 0 →
        z = (incZ S).det * β ∨ z = (incZ S).det * α ∨ z = (incZ S).det * γ := by
  have hnβ : ‖(β : ℂ)‖ = β := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hβ1' : 1 < ‖(β : ℂ)‖ := by rw [hnβ]; exact hβ1
  have hρ' : ∀ μ : ℂ, aeval μ (SsignQ P).charpoly = 0 → ‖μ‖ ≤ ‖(β : ℂ)‖ := by
    rw [hnβ]; exact SectorBridge.ssign_root_bound_of_perron P L hL hLN
  obtain ⟨hunit, hd, -⟩ := sieve4 P hbal hM hK hβ hα hγ hαγ hβ1' hα1 hγ1 hρ'
  have hdz : ((incZ S).det : ℂ) = β * α * γ := by rw [← hd, det_incQ, Rat.cast_intCast]
  have key : ∀ z : ℂ, aeval z (q4 P hbal) = 0 → aeval (β * (β * α * γ)) (q4 P hbal) = 0 ∧
      (z = β * (β * α * γ) ∨ z = α * (β * α * γ) ∨ z = γ * (β * α * γ)) := by
    intro z hz
    rcases sieve4_roots P hbal hM hβ hα hγ hαγ hβ1' hα1 hγ1 hρ' hz with h | ⟨-, hαr, -, hA, -⟩
    · exact h
    · exact (no_220_root P hM hβ hα hγ hαγ hβ1 hα1 hγ1 hαr hunit hSC L hL hLN
        (aeval_eq_zero_of_dvd_aeval_eq_zero (q4_dvd_ssign P hbal) hA)).elim
  obtain ⟨z, hz⟩ := exists_root_q4 P hbal hK
  have hB : aeval (((incZ S).det : ℂ) * β) (q4 P hbal) = 0 := by
    rw [hdz, show β * α * γ * (β : ℂ) = β * (β * α * γ) by ring]; exact (key z hz).1
  refine ⟨hunit, hB, aeval_eq_zero_of_dvd_aeval_eq_zero (q4_dvd_ssign P hbal) hB,
    fun w hw => ?_⟩
  rw [hdz]
  rcases (key w hw).2 with h | h | h <;> rw [h]
  · exact Or.inl (by ring)
  · exact Or.inr (Or.inl (by ring))
  · exact Or.inr (Or.inr (by ring))

include hbal in
/-- **Theorem A(iii): the cocycle is a gauge or an anti-gauge** (`Psc.Wielandt.gauge_of_real`
at the eigenvalue `d β` of `sieve4_211`).  Under the hypotheses of `sieve4_211`,
`S = d · D N_C D` for an integer sign vector `D` (`D i = ±1`), `d = det M = ±1`. -/
theorem gauge_of_sieve4 (hM : Irreducible (incQ S).charpoly)
    (hK : ∃ j : P.Rep, Psc.Defect4Lie.k4Vec j.1.1 j.1.2 ≠ 0) {β : ℝ} {α γ : ℂ}
    (hβ : aeval (β : ℂ) (incQ S).charpoly = 0) (hα : aeval α (incQ S).charpoly = 0)
    (hγ : aeval γ (incQ S).charpoly = 0) (hαγ : α ≠ γ) (hβ1 : 1 < β) (hα1 : ‖α‖ < 1)
    (hγ1 : ‖γ‖ < 1) (hSC : StronglyConnected (P.Nrep.map (Nat.cast : ℕ → ℝ)))
    (L : P.Rep → ℝ) (hL : ∀ i, 0 < L i) (hLN : L ᵥ* P.Nrep.map (Nat.cast : ℕ → ℝ) = β • L) :
    ∃ D : P.Rep → ℤ, (∀ i, D i = 1 ∨ D i = -1) ∧
      ∀ i j, P.Ssign i j = (incZ S).det * D i * P.Nrep i j * D j := by
  obtain ⟨hunit, -, hS, -⟩ :=
    sieve4_211 P hbal hM hK hβ hα hγ hαγ hβ1 hα1 hγ1 hSC L hL hLN
  obtain ⟨x, hx0, hx⟩ := exists_real_eigen_of_root_ssign P hS
  have hs : ((incZ S).det : ℝ) = 1 ∨ ((incZ S).det : ℝ) = -1 := by
    rcases (abs_eq zero_le_one).1 hunit with h | h <;> rw [h] <;> norm_num
  have e : ((((incZ S).det : ℝ) * β : ℝ) : ℂ) = ((incZ S).det : ℂ) * (β : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_intCast]
  obtain ⟨D, hD, hSD⟩ := Psc.Wielandt.gauge_of_real _ hSC L hL β hLN _
    (Psc.CocycleSpectrum.ssign_real_abs_le P) _ hs x hx0 (by rw [e]; exact hx)
  choose D' hD' hDD using fun i => Psc.CocycleSpectrum.exists_int_sign (hD i)
  refine ⟨D', hD', fun i j => ?_⟩
  have := hSD i j
  simp only [Matrix.map_apply, ← hDD] at this
  exact_mod_cast this

include hbal in
/-- **Theorem A(iii) in the vocabulary of `Psc.CocycleSpectrum`**: under the hypotheses of
`sieve4_211`, either `det M = 1` and the cocycle has a gauge (`IsGauge`), or `det M = −1`
and it has an anti-gauge (`IsAntiGauge`) — `gauge_of_sieve4` read through
`Psc.CocycleSpectrum.isGauge_iff` and `isAntiGauge_iff`. -/
theorem gauge_or_antiGauge_of_sieve4 (hM : Irreducible (incQ S).charpoly)
    (hK : ∃ j : P.Rep, Psc.Defect4Lie.k4Vec j.1.1 j.1.2 ≠ 0) {β : ℝ} {α γ : ℂ}
    (hβ : aeval (β : ℂ) (incQ S).charpoly = 0) (hα : aeval α (incQ S).charpoly = 0)
    (hγ : aeval γ (incQ S).charpoly = 0) (hαγ : α ≠ γ) (hβ1 : 1 < β) (hα1 : ‖α‖ < 1)
    (hγ1 : ‖γ‖ < 1) (hSC : StronglyConnected (P.Nrep.map (Nat.cast : ℕ → ℝ)))
    (L : P.Rep → ℝ) (hL : ∀ i, 0 < L i) (hLN : L ᵥ* P.Nrep.map (Nat.cast : ℕ → ℝ) = β • L) :
    ((incZ S).det = 1 ∧ ∃ g, Psc.CocycleSpectrum.IsGauge P g) ∨
      ((incZ S).det = -1 ∧ ∃ g, Psc.CocycleSpectrum.IsAntiGauge P g) := by
  obtain ⟨hunit, -⟩ := sieve4_211 P hbal hM hK hβ hα hγ hαγ hβ1 hα1 hγ1 hSC L hL hLN
  obtain ⟨D, hD, hSD⟩ := gauge_of_sieve4 P hbal hM hK hβ hα hγ hαγ hβ1 hα1 hγ1 hSC L hL hLN
  rcases (abs_eq zero_le_one).1 hunit with h | h
  · exact Or.inl ⟨h, D, (Psc.CocycleSpectrum.isGauge_iff P D).2
      ⟨hD, fun i j => by rw [hSD, h]; ring⟩⟩
  · exact Or.inr ⟨h, D, (Psc.CocycleSpectrum.isAntiGauge_iff P D).2
      ⟨hD, fun i j => by rw [hSD, h]; ring⟩⟩

end Wielandt

/-! ### Theorem A(i)–(iii) for a primitive substitution -/

section PrimitiveA

open Psc.Binomial Psc.Incidence Psc.SignedCocycle Psc.ParikhRank Psc.Degree2Sector
  Psc.SectorBridge Psc.PerronExistence Psc.PerronCore

variable {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Psc.Defect4.Equiv3 T.1 T.2)

/-- **Theorem A(i)–(iii) at the level of eigenvalues, for a primitive substitution.**  Let
`σ = S.s` be primitive with irreducible `χ_M` and a Pisot root `β`, `P` a normalisation with
`∼₃` states and a nonzero `K₄` column, and `N_C` strongly connected.  Then `β = r` for a real
`r > 1` that is the Perron root of `M` (`PerronData` for `M` at `r`), `|det M| = 1`, `d r`
(`d = det M`) is a root of `q₄` and of `χ_S`, every root of `q₄` is `d x` for a root `x` of
`χ_M` (the `(2,1,1)` sector; `(3,1,0)` and `(2,2,0)` are excluded), and `S = d · D N_C D`
with `D` an integer sign vector.  The Perron data `L = Lrep ℓ` of `Psc.Wielandt` come from
`Psc.PerronExistence.perron_inc` and `thm:parikh`
(`Psc.SignedCocycle.Normalisation.rep_eigen`); strong connectivity of `N_C` is not
derived. -/
theorem theoremA_of_primitive (hM : Irreducible (incQ S).charpoly)
    (hK : ∃ j : P.Rep, Psc.Defect4Lie.k4Vec j.1.1 j.1.2 ≠ 0)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc S.s ^ k) a c) {β : ℂ}
    (hβ : aeval β (incQ S).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z (incQ S).charpoly = 0 → z ≠ β → ‖z‖ < 1)
    (hSC : StronglyConnected (P.Nrep.map (Nat.cast : ℕ → ℝ))) :
    ∃ r : ℝ, (∃ ℓ u : Fin 3 → ℝ, PerronData ((inc S.s).map (Nat.cast : ℕ → ℝ)) r ℓ u) ∧
      1 < r ∧ (r : ℂ) = β ∧ |(incZ S).det| = 1 ∧
      aeval (((incZ S).det : ℂ) * r) (q4 P hbal) = 0 ∧
      aeval (((incZ S).det : ℂ) * r) (SsignQ P).charpoly = 0 ∧
      (∀ z : ℂ, aeval z (q4 P hbal) = 0 →
        ∃ x : ℂ, aeval x (incQ S).charpoly = 0 ∧ z = (incZ S).det * x) ∧
      ∃ D : P.Rep → ℤ, (∀ i, D i = 1 ∨ D i = -1) ∧
        ∀ i j, P.Ssign i j = (incZ S).det * D i * P.Nrep i j * D j := by
  have hbal1 : ∀ T ∈ S.C, Equiv1 T.1 T.2 := fun T hT => (hbal T hT).1.1
  obtain ⟨r, ℓ, u, h, -, -⟩ := perron_inc S.s hprim
  have hr := perron_eq_pisot h hβ hβ1 hpisot
  obtain ⟨α, γ, hα, hγ, hβα, hβγ, hαγ, -⟩ := exists_other_roots _ hM hβ
  have hα1 := hpisot α hα (Ne.symm hβα)
  have hγ1 := hpisot γ hγ (Ne.symm hβγ)
  subst hr
  have hnr : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h.pos]
  have hr1 : 1 < r := hnr ▸ hβ1
  have hL := P.lrep_pos ℓ h.left_pos (P.top_ne_nil hbal1)
  have hLN := P.rep_eigen ℓ r h.left hbal1
  obtain ⟨hunit, hB, hBS, hall⟩ :=
    sieve4_211 P hbal hM hK hβ hα hγ hαγ hr1 hα1 hγ1 hSC _ hL hLN
  refine ⟨r, ⟨ℓ, u, h⟩, hr1, rfl, hunit, hB, hBS, fun z hz => ?_,
    gauge_of_sieve4 P hbal hM hK hβ hα hγ hαγ hr1 hα1 hγ1 hSC _ hL hLN⟩
  rcases hall z hz with h' | h' | h'
  · exact ⟨_, hβ, h'⟩
  · exact ⟨_, hα, h'⟩
  · exact ⟨_, hγ, h'⟩

end PrimitiveA

/-! ### Controls -/

section Controls

open Psc.Binomial Psc.Incidence Psc.SignedCocycle Psc.ParikhRank Psc.Degree2Sector
  Psc.SectorBridge Psc.PerronExistence

/-- **State-level control.**  `Psc.Defect4.w4Norm` (the zero-return system of the
3-binomially equivalent pair `w4Pair` under the identity substitution) meets, jointly, the
state hypotheses of `sieve4` (`∼₃` states and a nonzero `K₄` column) and its spectral
hypothesis `hρ` at `β = 1` (`ssign_root_bound_of_perron` with `L = Lrep 1`, the identity
having the left eigenvector `ℓ = 1` for `1`: a control of `ssign_root_bound_of_perron`
too); it fails `hM` (`χ_M = (X-1)³` has the root `1`), and with it the Pisot moduli. -/
theorem w4_controls : (∀ T ∈ Psc.Defect4.w4.C, Psc.Defect4.Equiv3 T.1 T.2) ∧
    (∃ j : Psc.Defect4.w4Norm.Rep, Psc.Defect4Lie.k4Vec j.1.1 j.1.2 ≠ 0) ∧
    (∀ μ : ℂ, aeval μ (SsignQ Psc.Defect4.w4Norm).charpoly = 0 → ‖μ‖ ≤ 1) ∧
    ¬ Irreducible (incQ Psc.Defect4.w4).charpoly := by
  have h1 : ∀ T ∈ Psc.Defect4.w4.C, Equiv1 T.1 T.2 := fun T hT =>
    (Psc.Defect4.w4_equiv3 T hT).1.1
  have hℓ : (fun _ => (1 : ℝ)) ᵥ* (inc Psc.Defect4.w4.s).map (Nat.cast : ℕ → ℝ) =
      (1 : ℝ) • fun _ => (1 : ℝ) := by
    funext j
    fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_three, Psc.Defect4.w4,
      Psc.Reduction.redSystem, Psc.SignedIntertwiner.idSubst, inc]
  refine ⟨Psc.Defect4.w4_equiv3, ⟨Psc.Defect4.w4Rep, Psc.Defect4Lie.w4_k4Vec_ne⟩,
    SectorBridge.ssign_root_bound_of_perron Psc.Defect4.w4Norm _
      (Psc.Defect4.w4Norm.lrep_pos _ (fun _ => one_pos) (Psc.Defect4.w4Norm.top_ne_nil h1))
      (Psc.Defect4.w4Norm.rep_eigen _ 1 hℓ h1), fun h =>
    Psc.Cyclicity.not_isRoot_of_irreducible _ h 1 (by
      rw [eval_charpoly, Matrix.det_fin_three]
      simp [Psc.Defect4.w4, Psc.Reduction.redSystem, Psc.SignedIntertwiner.idSubst, inc])⟩

/-- A primitive substitution with incidence matrix `Psc.M0Pisot.M0 = [[5,21,1],[6,26,1],[6,24,1]]`:
`σ(0) = 0⁵1⁶2⁶`, `σ(1) = 0²¹1²⁶2²⁴`, `σ(2) = 012`. -/
def m0Subst : Fin 3 → List (Fin 3) :=
  ![List.replicate 5 0 ++ List.replicate 6 1 ++ List.replicate 6 2,
    List.replicate 21 0 ++ List.replicate 26 1 ++ List.replicate 24 2, [0, 1, 2]]

theorem inc_m0Subst : inc m0Subst = Matrix.of ![![5, 21, 1], ![6, 26, 1], ![6, 24, 1]] := by
  decide

theorem incQ_m0Subst : (inc m0Subst).map (Nat.cast : ℕ → ℚ) = Psc.M0Pisot.M0 := by
  rw [inc_m0Subst]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Psc.M0Pisot.M0]

theorem m0Subst_primitive : ∃ k ≥ 1, ∀ a c, 0 < (inc m0Subst ^ k) a c :=
  ⟨1, le_rfl, by rw [pow_one]; show ∀ a c : Fin 3, 0 < (m0Subst c).count a; decide⟩

/-- **Full control of `perron_eq_pisot` on `m0Subst`**: the Perron data of the primitive
`M0` (`Psc.PerronExistence.perron_inc`) and the Pisot root of `Psc.M0Pisot.m0_pisot` meet
every hypothesis, and the conclusion identifies them. -/
theorem m0_perron_control : ∃ (r : ℝ) (ℓ u : Fin 3 → ℝ),
    PerronData ((inc m0Subst).map (Nat.cast : ℕ → ℝ)) r ℓ u ∧ ∃ β : ℂ,
      aeval β Psc.M0Pisot.M0.charpoly = 0 ∧ 1 < ‖β‖ ∧
      (∀ z : ℂ, aeval z Psc.M0Pisot.M0.charpoly = 0 → z ≠ β → ‖z‖ < 1) ∧ (r : ℂ) = β := by
  obtain ⟨r, ℓ, u, h, -, -⟩ := perron_inc m0Subst m0Subst_primitive
  obtain ⟨b, hb1, hb, hbp⟩ := Psc.M0Pisot.m0_pisot
  rw [← Psc.M0Pisot.f_is_charpoly] at hb hbp
  have hb1' : 1 < ‖(b : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; exact hb1
  refine ⟨r, ℓ, u, h, b, hb, hb1', hbp, ?_⟩
  rw [← incQ_m0Subst] at hb hbp
  exact perron_eq_pisot h hb hb1' hbp

/-- **The conclusion has content: no degree-four first defect over `M0`.**  `σ = m0Subst`
is primitive with the irreducible Pisot `χ_M = X³ − 32X² + 5X + 2` (`Psc.M0Pisot`) and
`det M = −2`.  By `sieve4_of_primitive`, every child system over `σ` with a normalisation
and `∼₃` states has all `K₄` columns zero: `r(C) = 4` is impossible.  (This uses every
hypothesis of the theorem except the state-level ones, which it refutes; it is not a
control meeting all hypotheses, which `sieve4` predicts cannot exist when `|det M| ≠ 1`.) -/
theorem m0_no_degree4 (S : ChildSystem (Fin 3)) (hs : S.s = m0Subst) (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Psc.Defect4.Equiv3 T.1 T.2) :
    ∀ j : P.Rep, Psc.Defect4Lie.k4Vec j.1.1 j.1.2 = 0 := by
  by_contra hK
  push Not at hK
  have hq : incQ S = Psc.M0Pisot.M0 := by
    show (inc S.s).map (Nat.cast : ℕ → ℚ) = _
    rw [hs]; exact incQ_m0Subst
  have hM : Irreducible (incQ S).charpoly := hq ▸ Psc.KernelCofactor.ctrl_irreducible
  obtain ⟨b, hb1, hb, hbp⟩ := Psc.M0Pisot.m0_pisot
  rw [← Psc.M0Pisot.f_is_charpoly, ← hq] at hb hbp
  have hb1' : 1 < ‖(b : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; exact hb1
  obtain ⟨-, hunit, -⟩ := sieve4_of_primitive P hbal hM hK (hs ▸ m0Subst_primitive) hb hb1' hbp
  have hd : ((incZ S).det : ℚ) = -2 := by rw [← det_incQ, hq, SectorBridge.M0_det]
  have hd' : (incZ S).det = -2 := by exact_mod_cast hd
  rw [hd'] at hunit
  norm_num at hunit

/-! #### The plastic substitution: a unimodular primitive Pisot matrix -/

/-- The rational incidence matrix of `Psc.Degree2Sector.plasticSubst` (`0 ↦ 1`, `1 ↦ 2`,
`2 ↦ 01`), `χ = X³ − X − 1` (`Psc.Degree2Sector.plastic_charpoly`). -/
abbrev plasticQ : Matrix (Fin 3) (Fin 3) ℚ := (inc plasticSubst).map (Nat.cast : ℕ → ℚ)

/-- The plastic number: a real root `b ∈ (1, 2)` of `x³ − x − 1` (intermediate value
theorem). -/
theorem plastic_real_root : ∃ b : ℝ, 1 < b ∧ b < 2 ∧ b ^ 3 - b - 1 = 0 := by
  have hc : Continuous fun x : ℝ => x ^ 3 - x - 1 := by fun_prop
  obtain ⟨b, ⟨h1, h2⟩, hb⟩ := intermediate_value_Ioo (show (1 : ℝ) ≤ 2 by norm_num)
    hc.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo ((fun x : ℝ => x ^ 3 - x - 1) 1) ((fun x : ℝ => x ^ 3 - x - 1) 2) by
      norm_num)
  exact ⟨b, h1, h2, hb⟩

/-- **The other two plastic roots.**  Every complex root `z ≠ b` of `x³ − x − 1` solves
`z² + b z + (b² − 1) = 0`, whose discriminant `4 − 3b²` is negative (`b³ = b + 1` and
`b > 1` give `4/3 < b² < 2`); so `z` is non-real, `Re z = −b/2`, and
`‖z‖² = b² − 1 < 1`. -/
theorem plastic_other {b : ℝ} (hb1 : 1 < b) (hb : b ^ 3 - b - 1 = 0) {z : ℂ}
    (hz : z ^ 3 - z - 1 = 0) (hzb : z ≠ b) : ‖z‖ ^ 2 = b ^ 2 - 1 ∧ z.im ≠ 0 ∧ ‖z‖ < 1 := by
  have hq : z ^ 2 + b * z + (b ^ 2 - 1) = 0 := by
    have hbC : (b : ℂ) ^ 3 - b - 1 = 0 := by exact_mod_cast hb
    have h : (z - b) * (z ^ 2 + b * z + (b ^ 2 - 1)) = 0 := by
      linear_combination hz - hbC
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hzb)
  have hre := congrArg Complex.re hq
  have him := congrArg Complex.im hq
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.one_re, Complex.zero_re, Complex.add_im, Complex.mul_im,
    Complex.sub_im, Complex.one_im, Complex.zero_im] at hre him
  have hb2 : b ^ 2 < 2 := by nlinarith
  have hb3 : 4 < 3 * b ^ 2 := by nlinarith
  set x := z.re
  set y := z.im
  have hy : y ≠ 0 := by
    intro hy0
    rw [hy0] at hre
    nlinarith [sq_nonneg (2 * x + b)]
  have hx : 2 * x + b = 0 := by
    have : y * (2 * x + b) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hy
  have hn : ‖z‖ ^ 2 = b ^ 2 - 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    linear_combination (-1 : ℝ) * hre + x * hx
  refine ⟨hn, hy, ?_⟩
  nlinarith [norm_nonneg z]

/-- **`χ = X³ − X − 1` is Pisot**: a real root `b > 1` and every other complex root of
modulus `< 1`. -/
theorem plastic_pisot : ∃ b : ℝ, 1 < b ∧ aeval (b : ℂ) plasticQ.charpoly = 0 ∧
    ∀ z : ℂ, aeval z plasticQ.charpoly = 0 → z ≠ b → ‖z‖ < 1 := by
  obtain ⟨b, hb1, -, hb⟩ := plastic_real_root
  have hev : ∀ z : ℂ, aeval z plasticQ.charpoly = z ^ 3 - z - 1 := by
    intro z; rw [plastic_charpoly]; simp
  exact ⟨b, hb1, by rw [hev]; exact_mod_cast hb, fun z hz hzb =>
    (plastic_other hb1 hb (by rw [← hev]; exact hz) hzb).2.2⟩

/-- `det = 1` for the plastic matrix (`det = (−1)³ χ(0)`). -/
theorem plastic_det : plasticQ.det = 1 := by
  rw [Matrix.det_eq_sign_charpoly_coeff, plastic_charpoly]
  simp; norm_num

/-- **Matrix-level control of `sieve4_pisot`, `sieve4_of_primitive`, `theoremA_of_primitive`.**
`plasticSubst` has irreducible `χ_M` (`Psc.Degree2Sector.plastic_irreducible`), a primitive
incidence matrix (`M⁵ > 0`), a Pisot root, and `det M = 1`, in agreement with the
conclusion `|det M| = 1`.  It carries no child system: the state-level hypotheses are
`w4_controls`'. -/
theorem plastic_matrix_controls : Irreducible plasticQ.charpoly ∧
    (∃ k ≥ 1, ∀ a c, 0 < (inc plasticSubst ^ k) a c) ∧
    (∃ b : ℝ, 1 < b ∧ aeval (b : ℂ) plasticQ.charpoly = 0 ∧
      ∀ z : ℂ, aeval z plasticQ.charpoly = 0 → z ≠ b → ‖z‖ < 1) ∧ plasticQ.det = 1 :=
  ⟨plastic_irreducible,
    ⟨5, by norm_num, fun a c => by fin_cases a <;> fin_cases c <;> decide +kernel⟩,
    plastic_pisot, plastic_det⟩

/-- **Full control of `perron_eq_pisot` on `plasticSubst`**: the Perron data of the
primitive plastic matrix and its Pisot root (`plastic_pisot`) meet every hypothesis, and the
conclusion identifies them. -/
theorem plastic_perron_control : ∃ (r : ℝ) (ℓ u : Fin 3 → ℝ),
    PerronData ((inc plasticSubst).map (Nat.cast : ℕ → ℝ)) r ℓ u ∧ ∃ β : ℂ,
      aeval β plasticQ.charpoly = 0 ∧ 1 < ‖β‖ ∧
      (∀ z : ℂ, aeval z plasticQ.charpoly = 0 → z ≠ β → ‖z‖ < 1) ∧ (r : ℂ) = β := by
  obtain ⟨r, ℓ, u, h, -, -⟩ := perron_inc plasticSubst plastic_matrix_controls.2.1
  obtain ⟨b, hb1, hb, hbp⟩ := plastic_pisot
  have hb1' : 1 < ‖(b : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; exact hb1
  exact ⟨r, ℓ, u, h, b, hb, hb1', hbp, perron_eq_pisot h hb hb1' hbp⟩

/-- The empty child system over `plasticSubst`: no states. -/
def plasticEmpty : ChildSystem (Fin 3) where
  s := plasticSubst
  C := ∅
  children := fun _ => []
  top := by simp
  bot := by simp
  closed := by simp
  nonempty := by simp

/-- The (empty) normalisation of `plasticEmpty`. -/
def plasticEmptyNorm : Normalisation plasticEmpty where
  R := ∅
  swap_mem := by simp [plasticEmpty]
  children_swap := by simp [plasticEmpty]
  sub := by simp
  cover := by simp [plasticEmpty]
  not_both := by simp

/-- **Degenerate full control of `ssign_root_bound_of_primitive`.**  The empty child system
over the primitive Pisot `plasticSubst` meets every hypothesis (primitivity, balanced states
vacuously, a Pisot root `b`); the conclusion holds but is vacuous, since `χ_S = 1` has no
root.  No non-empty control is formalized (see the module docstring). -/
theorem plastic_empty_control : (∃ k ≥ 1, ∀ a c, 0 < (inc plasticEmpty.s ^ k) a c) ∧
    (∀ T ∈ plasticEmpty.C, Equiv1 T.1 T.2) ∧
    ∃ b : ℝ, 1 < b ∧ aeval (b : ℂ) (incQ plasticEmpty).charpoly = 0 ∧
      (∀ z : ℂ, aeval z (incQ plasticEmpty).charpoly = 0 → z ≠ b → ‖z‖ < 1) ∧
      (∀ μ : ℂ, aeval μ (SsignQ plasticEmptyNorm).charpoly = 0 → ‖μ‖ ≤ ‖(b : ℂ)‖) ∧
      (SsignQ plasticEmptyNorm).charpoly = 1 := by
  have hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc plasticEmpty.s ^ k) a c := plastic_matrix_controls.2.1
  have hbal : ∀ T ∈ plasticEmpty.C, Equiv1 T.1 T.2 := by simp [plasticEmpty]
  obtain ⟨b, hb1, hb, hbp⟩ := plastic_pisot
  have hb1' : 1 < ‖(b : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; exact hb1
  have : IsEmpty plasticEmptyNorm.Rep := ⟨fun i => by simpa [plasticEmptyNorm] using i.2⟩
  exact ⟨hprim, hbal, b, hb1, hb, hbp,
    ssign_root_bound_of_primitive plasticEmptyNorm hprim hbal hb hb1' hbp,
    Matrix.charpoly_isEmpty⟩

/-- **Full control of `sieve4_weight` (and `weight_root_cases`, `weight_211`).**  With
`f = q = X³ − X − 1`, `β` the plastic number and `α, γ` the other two roots: every hypothesis
holds (`β² α γ = β · det = β` is a root of `q` of shape `(2,1,1)`, and every root of `q` has
modulus at most `‖β‖`), and the conclusion is `‖βαγ‖ = 1` with a root of modulus `‖β‖`. -/
theorem plastic_weight_control : ∃ β α γ : ℂ,
    aeval β plasticQ.charpoly = 0 ∧ aeval α plasticQ.charpoly = 0 ∧
    aeval γ plasticQ.charpoly = 0 ∧ β ≠ α ∧ β ≠ γ ∧ α ≠ γ ∧
    1 < ‖β‖ ∧ ‖α‖ < 1 ∧ ‖γ‖ < 1 ∧ 1 ≤ ‖β * α * γ‖ ∧
    (∀ z : ℂ, aeval z plasticQ.charpoly = 0 → ‖z‖ ≤ ‖β‖) ∧
    aeval (β ^ 2 * α ^ 1 * γ ^ 1) plasticQ.charpoly = 0 ∧
    ‖β * α * γ‖ = 1 ∧ ∃ z : ℂ, aeval z plasticQ.charpoly = 0 ∧ ‖z‖ = ‖β‖ := by
  obtain ⟨b, hb1, hb, hbp⟩ := plastic_pisot
  obtain ⟨α, γ, hα, hγ, hβα, hβγ, hαγ, -⟩ := exists_other_roots _ plastic_irreducible hb
  have hnb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hβ1 : 1 < ‖(b : ℂ)‖ := by rw [hnb]; exact hb1
  have hα1 := hbp α hα (Ne.symm hβα)
  have hγ1 := hbp γ hγ (Ne.symm hβγ)
  have hd := SectorBridge.det_eq_mul_roots _ hb hα hγ hβα hβγ hαγ
  rw [plastic_det, Rat.cast_one] at hd
  have hdet : 1 ≤ ‖(b : ℂ) * α * γ‖ := by rw [← hd, norm_one]
  have hbound : ∀ z : ℂ, aeval z plasticQ.charpoly = 0 → ‖z‖ ≤ ‖(b : ℂ)‖ := fun z hz => by
    by_cases h : z = b
    · rw [h]
    · exact (hbp z hz h).le.trans hβ1.le
  have hq : aeval ((b : ℂ) ^ 2 * α ^ 1 * γ ^ 1) plasticQ.charpoly = 0 := by
    rw [show (b : ℂ) ^ 2 * α ^ 1 * γ ^ 1 = b * (b * α * γ) by ring, ← hd, mul_one]; exact hb
  exact ⟨b, α, γ, hb, hα, hγ, hβα, hβγ, hαγ, hβ1, hα1, hγ1, hdet, hbound, hq,
    sieve4_weight plastic_irreducible (natDegree_charpoly _) hb hα hγ hβα hβγ hαγ hβ1 hα1 hγ1
      hdet _ hbound 2 1 1 (Or.inr (Or.inr (Or.inl rfl))) hq⟩

/-- `q = X³ − X² + 2X − 1`: for the plastic roots `β, α, γ` (`βαγ = 1`), its roots are
`β²α² = γ⁻²`, `β²γ² = α⁻²`, `α²γ² = β⁻²`, the `(2,2,0)` orbit. -/
noncomputable def q220 : ℚ[X] := X ^ 3 - X ^ 2 + C 2 * X - 1

theorem q220_natDegree : q220.natDegree = 3 := by unfold q220; compute_degree!

theorem aeval_q220 (z : ℂ) : aeval z q220 = z ^ 3 - z ^ 2 + 2 * z - 1 := by
  simp [q220]

/-- If `x³ = x + 1` and `w x² = 1`, then `q(w) = 0` (`x⁶ q(w)` is a combination of the two
relations). -/
theorem q220_root {w x : ℂ} (hx : x ^ 3 - x - 1 = 0) (hw : w * x ^ 2 = 1) :
    aeval w q220 = 0 := by
  rw [aeval_q220]
  have hx0 : x ≠ 0 := fun h => by rw [h] at hx; norm_num at hx
  have h6 : (w ^ 3 - w ^ 2 + 2 * w - 1) * x ^ 6 = 0 := by
    linear_combination ((w * x ^ 2) ^ 2 + w * x ^ 2 + 1 - (w * x ^ 2 + 1) * x ^ 2 + 2 * x ^ 4) * hw
      + (-x ^ 3 + x - 1) * hx
  exact (mul_eq_zero.1 h6).resolve_right (pow_ne_zero _ hx0)

/-- Three pairwise distinct roots of `x³ − x − 1` sum to `0`. -/
theorem plastic_sum_roots {a b c : ℂ} (ha : a ^ 3 - a - 1 = 0) (hb : b ^ 3 - b - 1 = 0)
    (hc : c ^ 3 - c - 1 = 0) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : a + b + c = 0 := by
  have qab : a ^ 2 + a * b + b ^ 2 - 1 = 0 :=
    (mul_eq_zero.1 (by linear_combination ha - hb :
      (a - b) * (a ^ 2 + a * b + b ^ 2 - 1) = 0)).resolve_left (sub_ne_zero.2 hab)
  have qac : a ^ 2 + a * c + c ^ 2 - 1 = 0 :=
    (mul_eq_zero.1 (by linear_combination ha - hc :
      (a - c) * (a ^ 2 + a * c + c ^ 2 - 1) = 0)).resolve_left (sub_ne_zero.2 hac)
  exact (mul_eq_zero.1 (by linear_combination qab - qac : (b - c) * (a + b + c) = 0)).resolve_left
    (sub_ne_zero.2 hbc)

/-- **Full control of `weight_220`: the Galois/modulus sieve alone does not exclude
`(2,2,0)`.**  For the plastic roots and `q = X³ − X² + 2X − 1` (`q220`), every hypothesis of
`weight_220` holds: `β² α²` is a root of `q` of shape `(2,2,0)`, and every root of `q` has
modulus at most `‖β‖` (`‖β²α²‖ = ‖β²γ²‖ = β`, `‖α²γ²‖ = (β² − 1)² < 1`).  The conclusion is
the complex unit case: `‖βαγ‖ = 1`, `‖α‖ = ‖γ‖`, `α`, `γ` non-real.  So excluding the
`(2,2,0)` sector needs more than the roots of `q₄`: in `sieve4_211` it is the Wielandt step
`no_220_root`, which uses the child system (`N_C`, `|S| ≤ N_C`, the Perron vector `L`). -/
theorem plastic_220_control : ∃ β α γ : ℂ,
    aeval β plasticQ.charpoly = 0 ∧ aeval α plasticQ.charpoly = 0 ∧
    aeval γ plasticQ.charpoly = 0 ∧ β ≠ α ∧ β ≠ γ ∧ α ≠ γ ∧
    1 < ‖β‖ ∧ ‖α‖ < 1 ∧ ‖γ‖ < 1 ∧ 1 ≤ ‖β * α * γ‖ ∧
    (∀ z : ℂ, aeval z q220 = 0 → ‖z‖ ≤ ‖β‖) ∧ aeval (β ^ 2 * α ^ 2 * γ ^ 0) q220 = 0 ∧
    ‖β * α * γ‖ = 1 ∧ ‖α‖ = ‖γ‖ ∧ α.im ≠ 0 ∧ γ.im ≠ 0 := by
  have hev : ∀ z : ℂ, aeval z plasticQ.charpoly = z ^ 3 - z - 1 := by
    intro z; rw [plastic_charpoly]; simp
  obtain ⟨b, hb1, -, hbR⟩ := plastic_real_root
  have hbC : (b : ℂ) ^ 3 - b - 1 = 0 := by exact_mod_cast hbR
  have hb : aeval (b : ℂ) plasticQ.charpoly = 0 := by rw [hev]; exact hbC
  obtain ⟨α, γ, hα, hγ, hβα, hβγ, hαγ, -⟩ := exists_other_roots _ plastic_irreducible hb
  have hα' : α ^ 3 - α - 1 = 0 := by rw [← hev]; exact hα
  have hγ' : γ ^ 3 - γ - 1 = 0 := by rw [← hev]; exact hγ
  obtain ⟨hαn, -, hα1⟩ := plastic_other hb1 hbR hα' (Ne.symm hβα)
  obtain ⟨hγn, -, hγ1⟩ := plastic_other hb1 hbR hγ' (Ne.symm hβγ)
  have hnb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hβ1 : 1 < ‖(b : ℂ)‖ := by rw [hnb]; exact hb1
  have hd := SectorBridge.det_eq_mul_roots _ hb hα hγ hβα hβγ hαγ
  rw [plastic_det, Rat.cast_one] at hd
  have hdet : 1 ≤ ‖(b : ℂ) * α * γ‖ := by rw [← hd, norm_one]
  have hsum := plastic_sum_roots hbC hα' hγ' hβα hβγ hαγ
  have hw1 : aeval ((b : ℂ) ^ 2 * α ^ 2) q220 = 0 := q220_root hγ' (by
    rw [show (b : ℂ) ^ 2 * α ^ 2 * γ ^ 2 = (b * α * γ) ^ 2 by ring, ← hd, one_pow])
  have hw2 : aeval ((b : ℂ) ^ 2 * γ ^ 2) q220 = 0 := q220_root hα' (by
    rw [show (b : ℂ) ^ 2 * γ ^ 2 * α ^ 2 = (b * α * γ) ^ 2 by ring, ← hd, one_pow])
  have hw3 : aeval (α ^ 2 * γ ^ 2) q220 = 0 := q220_root hbC (by
    rw [show α ^ 2 * γ ^ 2 * (b : ℂ) ^ 2 = (b * α * γ) ^ 2 by ring, ← hd, one_pow])
  have hb2 : b * (b ^ 2 - 1) = 1 := by linear_combination hbR
  have hbsq : b ^ 2 < 2 := by nlinarith
  have hn1 : ‖(b : ℂ) ^ 2 * α ^ 2‖ = b := by
    rw [norm_mul, norm_pow, norm_pow, hnb, hαn]; linear_combination b * hb2
  have hn2 : ‖(b : ℂ) ^ 2 * γ ^ 2‖ = b := by
    rw [norm_mul, norm_pow, norm_pow, hnb, hγn]; linear_combination b * hb2
  have hn3 : ‖α ^ 2 * γ ^ 2‖ < 1 := by
    rw [norm_mul, norm_pow, norm_pow, hαn, hγn]; nlinarith
  have hb0 : (b : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (fun h => by rw [h, norm_zero] at hβ1; linarith)
  have h12 : (b : ℂ) ^ 2 * α ^ 2 ≠ (b : ℂ) ^ 2 * γ ^ 2 := by
    intro h
    have h' : (α - γ) * (α + γ) = 0 := by
      linear_combination mul_left_cancel₀ hb0 h
    have hag : α + γ = 0 := (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hαγ)
    have : (b : ℂ) = 0 := by linear_combination hsum - hag
    rw [this, norm_zero] at hβ1; linarith
  have h13 : (b : ℂ) ^ 2 * α ^ 2 ≠ α ^ 2 * γ ^ 2 := fun h => by
    have := hn3; rw [← h, hn1] at this; linarith
  have h23 : (b : ℂ) ^ 2 * γ ^ 2 ≠ α ^ 2 * γ ^ 2 := fun h => by
    have := hn3; rw [← h, hn2] at this; linarith
  have hq0 : q220 ≠ 0 := fun h => by have := q220_natDegree; rw [h, natDegree_zero] at this; omega
  have hbound : ∀ z : ℂ, aeval z q220 = 0 → ‖z‖ ≤ ‖(b : ℂ)‖ := by
    intro z hz
    rcases Psc.GaloisOrbit.root_eq_of_three hq0 q220_natDegree hw1 hw2 hw3 h12 h13 h23 hz with
      h | h | h <;> rw [h, hnb]
    · rw [hn1]
    · rw [hn2]
    · linarith
  have hq : aeval ((b : ℂ) ^ 2 * α ^ 2 * γ ^ 0) q220 = 0 := by rw [pow_zero, mul_one]; exact hw1
  obtain ⟨h1, h2, h3, h4, -⟩ := weight_220 plastic_irreducible (natDegree_charpoly _) hb hα hγ
    hβα hβγ hαγ hβ1 hdet q220 hbound 2 2 0 (Or.inl rfl) hq
  exact ⟨b, α, γ, hb, hα, hγ, hβα, hβγ, hαγ, hβ1, hα1, hγ1, hdet, hbound, hq, h1, h2, h3, h4⟩

end Controls

end Psc.Degree4Floor
