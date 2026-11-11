import PscVerif.Degree5Sieve

/-!
# The reciprocal cubic and the actual degree-five image rank

The standard polynomial arguments reviewed in
`docs/c4-degree-five-completion-literature-2026-11-10.md` complete the
multiplicity consequence of the existing image-root sieve. No strict-carrier
realizability or universal crossing productivity is asserted here.
-/

namespace Psc.Degree5Completion

open Polynomial Matrix Psc.Cyclicity Psc.Binomial Psc.SignedCocycle
open Psc.ParikhRank Psc.Incidence Psc.Defect5 Psc.Degree5Transport
open Psc.Degree5Sieve Psc.Degree4Floor Psc.SectorBridge

/-- The monic cubic with roots `d²/rᵢ`, where `rᵢ` are the incidence roots. -/
noncomputable def reciprocal (M : Matrix (Fin 3) (Fin 3) ℚ) : ℚ[X] :=
  X ^ 3 - C (M.det * (wedge2 M).trace) * X ^ 2 +
    C (M.det ^ 3 * M.trace) * X - C (M.det ^ 5)

theorem reciprocal_monic (M : Matrix (Fin 3) (Fin 3) ℚ) : (reciprocal M).Monic := by
  unfold reciprocal
  monicity!

theorem reciprocal_natDegree (M : Matrix (Fin 3) (Fin 3) ℚ) :
    (reciprocal M).natDegree = 3 := by
  unfold reciprocal
  compute_degree!

/-- A rational reciprocal root would give a rational incidence root. -/
theorem reciprocal_irreducible (M : Matrix (Fin 3) (Fin 3) ℚ)
    (hM : Irreducible M.charpoly) : Irreducible (reciprocal M) := by
  have hd := det_ne_zero_of_irreducible M hM
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [reciprocal_natDegree]
    decide
  intro x hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    have h : -(M.det ^ 5) = 0 := by simpa [reciprocal, IsRoot.def] using hx
    exact (pow_ne_zero 5 hd) (neg_eq_zero.mp h)
  apply not_isRoot_of_irreducible M hM (M.det ^ 2 / x)
  calc
    M.charpoly.eval (M.det ^ 2 / x) =
        -(M.det / x ^ 3) * (reciprocal M).eval x := by
      simp only [charpoly_fin_three, reciprocal, eval_sub, eval_add, eval_mul,
        eval_pow, eval_X, eval_C]
      field_simp
      ring
    _ = 0 := by rw [show (reciprocal M).eval x = 0 from hx, mul_zero]

/-- Exact evaluation under the scaled reciprocal change of variable. -/
theorem reciprocal_aeval_of_root (M : Matrix (Fin 3) (Fin 3) ℚ)
    {z : ℂ} (hz0 : z ≠ 0) (hz : aeval z M.charpoly = 0) :
    aeval (((M.det : ℚ) : ℂ) ^ 2 / z) (reciprocal M) = 0 := by
  have hid : aeval (((M.det : ℚ) : ℂ) ^ 2 / z) (reciprocal M) =
      -((((M.det : ℚ) : ℂ) ^ 5) / z ^ 3) * aeval z M.charpoly := by
    simp only [reciprocal, charpoly_fin_three, map_sub, map_add, map_mul, map_pow,
      aeval_X, aeval_C, eq_ratCast]
    field_simp
    ring
  rw [hid, hz, mul_zero]

/-- Over the rationals, root containment in one irreducible monic polynomial
forces a monic polynomial to be its power. This includes the constant `1`. -/
theorem eq_pow_of_roots {g p : ℚ[X]} (hg : g.Monic) (hgi : Irreducible g)
    (hp : p.Monic)
    (hroots : ∀ z : ℂ, aeval z p = 0 → aeval z g = 0) :
    ∃ k : ℕ, p = g ^ k := by
  classical
  suffices ∀ n : ℕ, ∀ p : ℚ[X], p.natDegree = n → p.Monic →
      (∀ z : ℂ, aeval z p = 0 → aeval z g = 0) → ∃ k : ℕ, p = g ^ k from
    this p.natDegree p rfl hp hroots
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hn hp hroots
    by_cases hp0 : p.natDegree = 0
    · refine ⟨0, ?_⟩
      simpa using hp.natDegree_eq_zero.mp hp0
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective ℂ
      (algebraMap ℚ ℂ).injective p
      (natDegree_pos_iff_degree_pos.1 (Nat.pos_of_ne_zero hp0)).ne'
    have hdvd : g ∣ p := (hgi.dvd_iff_aeval_eq_zero (hroots z hz)).1 hz
    obtain ⟨q, hq⟩ := hdvd
    have hqm : q.Monic := by
      exact hg.of_mul_monic_left (hq ▸ hp)
    have hqdeg : q.natDegree < n := by
      have hgp : 0 < g.natDegree := hgi.natDegree_pos
      rw [← hn, hq, natDegree_mul hg.ne_zero hqm.ne_zero]
      omega
    obtain ⟨k, hk⟩ := ih q.natDegree hqdeg q rfl hqm (fun w hw => hroots w (by
      rw [hq, map_mul, hw, mul_zero]))
    exact ⟨k + 1, by rw [hq, hk, pow_succ']⟩

/-- All surviving mixed weights are roots of the displayed reciprocal cubic. -/
theorem reciprocal_roots_of_sieve {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2)
    (hM : Irreducible (incQ S).charpoly)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc S.s ^ k) a c) {β : ℂ}
    (hβ : aeval β (incQ S).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z (incQ S).charpoly = 0 → z ≠ β → ‖z‖ < 1) :
    ∀ z : ℂ, aeval z (q5 P hbal) = 0 → aeval z (reciprocal (incQ S)) = 0 := by
  obtain ⟨α, γ, hα, hγ, hβα, hβγ, hαγ, hsieve⟩ :=
    sieve5_of_primitive P hbal hM hprim hβ hβ1 hpisot
  have hd := det_ne_zero_of_irreducible (incQ S) hM
  have hdc : (((incQ S).det : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hd
  have hprod : (((incQ S).det : ℚ) : ℂ) = β * α * γ :=
    (pisot_setup hM hβ hα hγ hαγ hβ1
      (hpisot α hα hβα.symm) (hpisot γ hγ hβγ.symm)).2.2.1
  have hp0 : β * α * γ ≠ 0 := hprod ▸ hdc
  have hβ0 : β ≠ 0 := (mul_ne_zero_iff.1 (mul_ne_zero_iff.1 hp0).1).1
  have hα0 : α ≠ 0 := (mul_ne_zero_iff.1 (mul_ne_zero_iff.1 hp0).1).2
  have hγ0 : γ ≠ 0 := (mul_ne_zero_iff.1 hp0).2
  have hb := reciprocal_aeval_of_root (incQ S) hβ0 hβ
  have ha := reciprocal_aeval_of_root (incQ S) hα0 hα
  have hc := reciprocal_aeval_of_root (incQ S) hγ0 hγ
  have eb : (((incQ S).det : ℚ) : ℂ) ^ 2 / β = β * α^2 * γ^2 := by
    rw [hprod]
    field_simp
  have ea : (((incQ S).det : ℚ) : ℂ) ^ 2 / α = β^2 * α * γ^2 := by
    rw [hprod]
    field_simp
  have ec : (((incQ S).det : ℚ) : ℂ) ^ 2 / γ = β^2 * α^2 * γ := by
    rw [hprod]
    field_simp
  rw [eb] at hb
  rw [ea] at ha
  rw [ec] at hc
  intro z hz
  rcases hsieve z hz with rfl | rfl | rfl
  · exact hb
  · exact ha
  · exact hc

/-- The actual image polynomial is a power of the irreducible reciprocal
cubic, and the actual image rank is three times that exponent. -/
theorem q5_eq_pow_rank {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2)
    (hM : Irreducible (incQ S).charpoly)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc S.s ^ k) a c) {β : ℂ}
    (hβ : aeval β (incQ S).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z (incQ S).charpoly = 0 → z ≠ β → ‖z‖ < 1) :
    ∃ k : ℕ, q5 P hbal = reciprocal (incQ S) ^ k ∧
      Module.finrank ℚ (LinearMap.range (columns P)) = 3 * k := by
  obtain ⟨k, hk⟩ := eq_pow_of_roots (reciprocal_monic (incQ S))
    (reciprocal_irreducible (incQ S) hM)
    (imCharpoly_monic (intertwine P hbal))
    (reciprocal_roots_of_sieve P hbal hM hprim hβ hβ1 hpisot)
  change q5 P hbal = reciprocal (incQ S) ^ k at hk
  refine ⟨k, hk, ?_⟩
  have hn := natDegree_imCharpoly (intertwine P hbal)
  change (q5 P hbal).natDegree = _ at hn
  rw [← hn, hk, natDegree_pow, reciprocal_natDegree]
  omega

/-- The degree-five column map vanishes exactly when all representative
degree-five defect columns vanish. -/
theorem columns_eq_zero_iff {S : ChildSystem (Fin 3)} (P : Normalisation S) :
    columns P = 0 ↔ ∀ j : P.Rep, Psc.Defect5Lie.k5Vec j.1.1 j.1.2 = 0 := by
  classical
  constructor
  · intro h j
    have hj := LinearMap.congr_fun h (Pi.single j 1)
    simpa only [columns, Fintype.linearCombination_apply_single, one_smul,
      LinearMap.zero_apply] using hj
  · intro h
    apply LinearMap.ext
    intro v
    simp [columns, Fintype.linearCombination_apply, h]

/-- The zero image is the constant-polynomial case, without any Pisot or
nonzero-column assumption. -/
theorem q5_eq_one_iff {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2) : q5 P hbal = 1 ↔ columns P = 0 := by
  have hn := natDegree_imCharpoly (intertwine P hbal)
  change (q5 P hbal).natDegree = _ at hn
  constructor
  · intro h
    apply LinearMap.range_eq_bot.1
    apply Submodule.finrank_eq_zero.1
    rw [← hn, h, natDegree_one]
  · intro h
    have hm : (q5 P hbal).Monic := imCharpoly_monic (intertwine P hbal)
    apply hm.natDegree_eq_zero.mp
    rw [hn, LinearMap.range_eq_bot.2 h]
    simp

/-- Positive exponent is a consequence of a genuine nonzero image column,
not an additional condition in the factorization theorem. -/
theorem q5_eq_pow_rank_of_nonzero {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2)
    (hM : Irreducible (incQ S).charpoly)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc S.s ^ k) a c)
    (hne : ∃ j : P.Rep, Psc.Defect5Lie.k5Vec j.1.1 j.1.2 ≠ 0) {β : ℂ}
    (hβ : aeval β (incQ S).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z (incQ S).charpoly = 0 → z ≠ β → ‖z‖ < 1) :
    ∃ k : ℕ, 0 < k ∧ q5 P hbal = reciprocal (incQ S) ^ k ∧
      Module.finrank ℚ (LinearMap.range (columns P)) = 3 * k := by
  obtain ⟨k, hk, hr⟩ := q5_eq_pow_rank P hbal hM hprim hβ hβ1 hpisot
  refine ⟨k, Nat.pos_of_ne_zero ?_, hk, hr⟩
  intro hk0
  rw [hk0, pow_zero] at hk
  have hz := (columns_eq_zero_iff P).1 ((q5_eq_one_iff P hbal).1 hk)
  obtain ⟨j, hj⟩ := hne
  exact hj (hz j)

/-- Strictly violating the nonzero-image determinant bound forces the entire
actual degree-five defect map to vanish. -/
theorem columns_eq_zero_of_det_bound {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2)
    (hM : Irreducible (incQ S).charpoly)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc S.s ^ k) a c) {β : ℂ}
    (hβ : aeval β (incQ S).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z (incQ S).charpoly = 0 → z ≠ β → ‖z‖ < 1)
    (hsmall : ‖β‖ < ‖(((incQ S).det : ℚ) : ℂ)‖ ^ 3) : columns P = 0 := by
  classical
  rw [columns_eq_zero_iff]
  intro j
  by_contra hj
  exact (not_lt_of_ge (det_cube_le_of_nonzero P hbal hM hprim ⟨j, hj⟩ hβ hβ1 hpisot))
    hsmall

/-- The explicit non-unit exclusion requested by the C4 continuation note. -/
theorem columns_eq_zero_of_nonunit_small_perron {S : ChildSystem (Fin 3)}
    (P : Normalisation S) (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2)
    (hM : Irreducible (incQ S).charpoly)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc S.s ^ k) a c) {β : ℂ}
    (hβ : aeval β (incQ S).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z (incQ S).charpoly = 0 → z ≠ β → ‖z‖ < 1)
    (hd2 : 2 ≤ ‖(((incQ S).det : ℚ) : ℂ)‖) (hb8 : ‖β‖ < 8) : columns P = 0 := by
  apply columns_eq_zero_of_det_bound P hbal hM hprim hβ hβ1 hpisot
  calc
    ‖β‖ < 8 := hb8
    _ = (2 : ℝ) ^ 3 := by norm_num
    _ ≤ ‖(((incQ S).det : ℚ) : ℂ)‖ ^ 3 := pow_le_pow_left₀ (by norm_num) hd2 3

/-- The reciprocal cubic of the plastic incidence is the stated abstract
surviving-sector control. This is not a nonzero actual child-image witness. -/
theorem reciprocal_plastic_control :
    reciprocal plasticQ = X ^ 3 + X ^ 2 - 1 ∧ Irreducible (reciprocal plasticQ) := by
  constructor
  · have ht : plasticQ.trace = 0 := by decide +kernel
    have hu : (wedge2 plasticQ).trace = -1 := by decide +kernel
    simp [reciprocal, plastic_det, ht, hu]
  · exact reciprocal_irreducible plasticQ Psc.Degree2Sector.plastic_irreducible

/-- Degree-four balance of the existing empty plastic child system. -/
theorem plasticEmpty_equiv4 : ∀ T ∈ plasticEmpty.C, Equiv4 T.1 T.2 := by
  simp [plasticEmpty]

/-- A full zero-image control over the existing primitive irreducible Pisot
substitution: the empty image has polynomial `1` and rank zero. -/
theorem plastic_zero_image_control :
    q5 plasticEmptyNorm plasticEmpty_equiv4 = 1 ∧
      Module.finrank ℚ (LinearMap.range (columns plasticEmptyNorm)) = 0 := by
  have hz : columns plasticEmptyNorm = 0 := by
    rw [columns_eq_zero_iff]
    intro j
    have hfalse : False := by simpa [plasticEmptyNorm] using j.2
    exact hfalse.elim
  refine ⟨(q5_eq_one_iff plasticEmptyNorm plasticEmpty_equiv4).2 hz, ?_⟩
  rw [LinearMap.range_eq_bot.2 hz]
  simp

/-- Root containment alone does not imply a power when irreducibility is
dropped: `X-1` has its only root among those of `X³-1`. -/
theorem reducible_root_containment_control :
    (∀ z : ℂ, aeval z (X - 1 : ℚ[X]) = 0 → aeval z (X ^ 3 - 1 : ℚ[X]) = 0) ∧
      ¬ ∃ k : ℕ, (X - 1 : ℚ[X]) = (X ^ 3 - 1) ^ k := by
  constructor
  · intro z hz
    have hz1 : z = 1 := by simpa only [map_sub, aeval_X, map_one, sub_eq_zero] using hz
    simp [hz1]
  · rintro ⟨k, hk⟩
    have hn := congrArg Polynomial.natDegree hk
    have h1 : (X - 1 : ℚ[X]).natDegree = 1 := by compute_degree!
    have h3 : (X ^ 3 - 1 : ℚ[X]).natDegree = 3 := by compute_degree!
    rw [h1, natDegree_pow, h3] at hn
    omega

end Psc.Degree5Completion
