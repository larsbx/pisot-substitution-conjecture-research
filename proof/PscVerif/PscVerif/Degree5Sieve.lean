/- The signed Perron sieve on the actual degree-five image. -/
import PscVerif.Degree4Floor
import PscVerif.Degree5RootLift
import PscVerif.Degree5Sector

namespace Psc.Degree5Sieve

open Polynomial Psc.Binomial Psc.SignedCocycle Psc.ParikhRank Psc.Incidence
open Psc.Defect5 Psc.Degree5Transport Psc.Degree5RootLift Psc.Degree5Weights
open Psc.Degree5Sector Psc.Degree4Floor Psc.SectorBridge

/-- The three forbidden shapes after placing their largest exponent first. -/
abbrev Large (a b c : ℕ) : Prop :=
  (a,b,c) = (4,1,0) ∨ (a,b,c) = (4,0,1) ∨
  (a,b,c) = (3,2,0) ∨ (a,b,c) = (3,0,2) ∨ (a,b,c) = (3,1,1)

theorem large_swap {a b c : ℕ} (h : Large a b c) : Large a c b := by
  rcases h with h | h | h | h | h <;> simp_all [Large, Prod.mk.injEq]

/-- One of the three cyclic positions places the largest exponent first. -/
theorem forbidden_placements : ∀ σ : Equiv.Perm (Fin 3), ∀ i : Fin 3,
    let κ := (![![4,1,0], ![3,2,0], ![3,1,1]] i : Fin 3 → ℕ) ∘ σ
    Large (κ 0) (κ 1) (κ 2) ∨ Large (κ 1) (κ 0) (κ 2) ∨ Large (κ 2) (κ 0) (κ 1) := by
  decide +kernel

theorem surviving_placements : ∀ σ : Equiv.Perm (Fin 3),
    let κ := (![2,2,1] : Fin 3 → ℕ) ∘ σ
    (κ 0, κ 1, κ 2) = (1,2,2) ∨ (κ 0, κ 1, κ 2) = (2,1,2) ∨
      (κ 0, κ 1, κ 2) = (2,2,1) := by
  decide +kernel

theorem large_bound {β α γ : ℂ} (hβ : 1 < ‖β‖) (hα : ‖α‖ < 1) (hγ : ‖γ‖ < 1)
    (hd : 1 ≤ ‖β * α * γ‖) {a b c : ℕ} (h : Large a b c) :
    ‖β‖ < ‖β ^ a * α ^ b * γ ^ c‖ := by
  have hd' : 1 ≤ ‖β‖ * ‖α‖ * ‖γ‖ := by simpa only [norm_mul] using hd
  have hα0 : 0 < ‖α‖ := by
    by_contra! hn
    have hz := le_antisymm hn (norm_nonneg α)
    simp [hz] at hd'
  have hγ0 : 0 < ‖γ‖ := by
    by_contra! hn
    have hz := le_antisymm hn (norm_nonneg γ)
    simp [hz] at hd'
  obtain ⟨h41, h32, h311⟩ := excluded_weights _ _ _ hβ hα0 hγ hd'
  obtain ⟨h41', h32', -⟩ := excluded_weights _ _ _ hβ hγ0 hα
    (by simpa only [mul_assoc, mul_comm ‖α‖ ‖γ‖] using hd')
  rcases h with h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl, rfl⟩ := h
  all_goals simp only [norm_mul, norm_pow, pow_zero, pow_one, mul_one]
  · exact h41
  · exact h41'
  · exact h32
  · exact h32'
  · exact h311

/-- Galois transitivity needs only to move the maximal exponent. Both orders
of the two contracting roots are covered by the modulus estimate. -/
theorem forbidden_of_root {f q : ℚ[X]} (hf : Irreducible f) (hdeg : f.natDegree = 3)
    {β α γ : ℂ} (hβ : aeval β f = 0) (hα : aeval α f = 0) (hγ : aeval γ f = 0)
    (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ)
    (hβ1 : 1 < ‖β‖) (hα1 : ‖α‖ < 1) (hγ1 : ‖γ‖ < 1) (hd : 1 ≤ ‖β * α * γ‖)
    (hbound : ∀ z : ℂ, aeval z q = 0 → ‖z‖ ≤ ‖β‖) {a b c : ℕ}
    (hroot : aeval (β ^ a * α ^ b * γ ^ c) q = 0)
    (hshape : Large a b c ∨ Large b a c ∨ Large c a b) : False := by
  have exclude {u v w : ℕ} (h : Large u v w)
      (hr : aeval (β ^ u * α ^ v * γ ^ w) q = 0) : False :=
    (not_lt_of_ge (hbound _ hr)) (large_bound hβ1 hα1 hγ1 hd h)
  have exclude_orbit {u v w : ℕ} (h : Large u v w)
      (hr : ∃ x y : ℂ, ((x = α ∧ y = γ) ∨ (x = γ ∧ y = α)) ∧
        aeval (β ^ u * x ^ v * y ^ w) q = 0) : False := by
    obtain ⟨x, y, hxy, hr⟩ := hr
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact exclude h hr
    · apply exclude (large_swap h)
      simpa only [mul_assoc, mul_comm (γ ^ v) (α ^ w)] using hr
  have horbit := Psc.GaloisOrbit.orbit_exponent_on_beta hf hdeg hβ hα hγ hβα hβγ hαγ
    q a b c hroot
  rcases hshape with h | h | h
  · exact exclude h hroot
  · exact exclude_orbit h horbit.1
  · exact exclude_orbit h horbit.2

/-- Once a (2,2,1) value occurs, Galois transitivity can put its
single exponent on the first root. The order of the doubled roots is immaterial. -/
theorem orbit_221_first {f q : ℚ[X]} (hf : Irreducible f) (hdeg : f.natDegree = 3)
    {β α γ : ℂ} (hβ : aeval β f = 0) (hα : aeval α f = 0) (hγ : aeval γ f = 0)
    (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ)
    (h : aeval (β * α^2 * γ^2) q = 0 ∨ aeval (β^2 * α * γ^2) q = 0 ∨
      aeval (β^2 * α^2 * γ) q = 0) :
    aeval (β * α^2 * γ^2) q = 0 := by
  have normalize (hr : ∃ x y : ℂ, ((x = α ∧ y = γ) ∨ (x = γ ∧ y = α)) ∧
      aeval (β ^ 1 * x ^ 2 * y ^ 2) q = 0) : aeval (β * α^2 * γ^2) q = 0 := by
    obtain ⟨x, y, hxy, hr⟩ := hr
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simpa only [pow_one, mul_assoc, mul_comm (γ ^ 2) (α ^ 2)] using hr
  rcases h with h | h | h
  · exact h
  · exact normalize (Psc.GaloisOrbit.orbit_exponent_on_beta hf hdeg hβ hα hγ hβα hβγ hαγ
      q 2 1 2 (by simpa only [pow_one] using h)).1
  · exact normalize (Psc.GaloisOrbit.orbit_exponent_on_beta hf hdeg hβ hα hγ hβα hβγ hαγ
      q 2 2 1 (by simpa only [pow_one] using h)).2

/-- Every root of the actual image polynomial belongs to the surviving
(2,2,1) sector, under the signed spectral bound. -/
theorem sieve5_roots {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2)
    (hM : Irreducible (incQ S).charpoly) {β α γ : ℂ}
    (hβ : aeval β (incQ S).charpoly = 0) (hα : aeval α (incQ S).charpoly = 0)
    (hγ : aeval γ (incQ S).charpoly = 0) (hαγ : α ≠ γ)
    (hβ1 : 1 < ‖β‖) (hα1 : ‖α‖ < 1) (hγ1 : ‖γ‖ < 1)
    (hbound : ∀ z : ℂ, aeval z (P.Ssign.map (Int.cast : ℤ → ℚ)).charpoly = 0 →
      ‖z‖ ≤ ‖β‖) {z : ℂ} (hz : aeval z (q5 P hbal) = 0) :
    z = β * α^2 * γ^2 ∨ z = β^2 * α * γ^2 ∨ z = β^2 * α^2 * γ := by
  obtain ⟨hβα, hβγ, -, hd⟩ := pisot_setup hM hβ hα hγ hαγ hβ1 hα1 hγ1
  have hbq : ∀ w : ℂ, aeval w (q5 P hbal) = 0 → ‖w‖ ≤ ‖β‖ :=
    fun w hw => hbound w (aeval_eq_zero_of_dvd_aeval_eq_zero (q5_dvd_signed P hbal) hw)
  obtain ⟨κ, ⟨σ, h410 | h320 | h311 | h221⟩, rfl⟩ :=
    root_q5_is_mixed P hbal ![β, α, γ] (vec3_injective hβα hβγ hαγ)
      (vec3_roots hβ hα hγ) hz
  all_goals rw [show Psc.LieWeights.mono ![β, α, γ] κ =
    β ^ κ 0 * α ^ κ 1 * γ ^ κ 2 by rw [mono_fin_three]; rfl] at hz ⊢
  · exact (forbidden_of_root hM (natDegree_charpoly _) hβ hα hγ hβα hβγ hαγ
      hβ1 hα1 hγ1 hd hbq hz (h410.symm ▸ forbidden_placements σ 0)).elim
  · exact (forbidden_of_root hM (natDegree_charpoly _) hβ hα hγ hβα hβγ hαγ
      hβ1 hα1 hγ1 hd hbq hz (h320.symm ▸ forbidden_placements σ 1)).elim
  · exact (forbidden_of_root hM (natDegree_charpoly _) hβ hα hγ hβα hβγ hαγ
      hβ1 hα1 hγ1 hd hbq hz (h311.symm ▸ forbidden_placements σ 2)).elim
  · have h := h221.symm ▸ surviving_placements σ
    rcases h with h | h | h <;> simp only [Prod.mk.injEq] at h
    · exact Or.inl (by rw [h.1, h.2.1, h.2.2, pow_one])
    · exact Or.inr (Or.inl (by rw [h.1, h.2.1, h.2.2, pow_one]))
    · exact Or.inr (Or.inr (by rw [h.1, h.2.1, h.2.2, pow_one]))

/-- The signed bound is supplied by primitivity and balance. -/
theorem sieve5_of_primitive {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2)
    (hM : Irreducible (incQ S).charpoly)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc S.s ^ k) a c) {β : ℂ}
    (hβ : aeval β (incQ S).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z (incQ S).charpoly = 0 → z ≠ β → ‖z‖ < 1) :
    ∃ α γ : ℂ, aeval α (incQ S).charpoly = 0 ∧ aeval γ (incQ S).charpoly = 0 ∧
      β ≠ α ∧ β ≠ γ ∧ α ≠ γ ∧
      ∀ z : ℂ, aeval z (q5 P hbal) = 0 →
        z = β * α^2 * γ^2 ∨ z = β^2 * α * γ^2 ∨ z = β^2 * α^2 * γ := by
  obtain ⟨α, γ, hα, hγ, hβα, hβγ, hαγ, -⟩ := exists_other_roots _ hM hβ
  have hbound := ssign_root_bound_of_primitive P hprim
    (fun T hT => (hbal T hT).1.1.1) hβ hβ1 hpisot
  exact ⟨α, γ, hα, hγ, hβα, hβγ, hαγ, fun _ hz =>
    sieve5_roots P hbal hM hβ hα hγ hαγ hβ1 (hpisot α hα hβα.symm)
      (hpisot γ hγ hβγ.symm) hbound hz⟩

/-- A nonzero degree-five image has the full reciprocal orbit. This
identifies the set of roots and leaves their multiplicities to factorization. -/
theorem sieve5_full_orbit_of_primitive {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2)
    (hM : Irreducible (incQ S).charpoly)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc S.s ^ k) a c)
    (hne : ∃ j : P.Rep, Psc.Defect5Lie.k5Vec j.1.1 j.1.2 ≠ 0) {β : ℂ}
    (hβ : aeval β (incQ S).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z (incQ S).charpoly = 0 → z ≠ β → ‖z‖ < 1) :
    ∃ α γ : ℂ, aeval α (incQ S).charpoly = 0 ∧ aeval γ (incQ S).charpoly = 0 ∧
      β ≠ α ∧ β ≠ γ ∧ α ≠ γ ∧
      ∀ z : ℂ, aeval z (q5 P hbal) = 0 ↔
        z = β * α^2 * γ^2 ∨ z = β^2 * α * γ^2 ∨ z = β^2 * α^2 * γ := by
  obtain ⟨α, γ, hα, hγ, hβα, hβγ, hαγ, hsieve⟩ :=
    sieve5_of_primitive P hbal hM hprim hβ hβ1 hpisot
  obtain ⟨z, hz⟩ := exists_root_q5 P hbal hne
  have h : aeval (β * α^2 * γ^2) (q5 P hbal) = 0 ∨
      aeval (β^2 * α * γ^2) (q5 P hbal) = 0 ∨
      aeval (β^2 * α^2 * γ) (q5 P hbal) = 0 := by
    rcases hsieve z hz with rfl | rfl | rfl
    · exact Or.inl hz
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr hz)
  have hβ' := orbit_221_first hM (natDegree_charpoly _) hβ hα hγ hβα hβγ hαγ h
  have hα' := orbit_221_first hM (natDegree_charpoly _) hα hβ hγ hβα.symm hαγ hβγ
    (q := q5 P hbal) (Or.inr (Or.inl (by simpa only [mul_comm β (α ^ 2)] using hβ')))
  have hγ' := orbit_221_first hM (natDegree_charpoly _) hγ hβ hα hβγ.symm hαγ.symm hβα
    (q := q5 P hbal) (Or.inr (Or.inl (by simpa [mul_assoc, mul_comm, mul_left_comm] using hβ')))
  refine ⟨α, γ, hα, hγ, hβα, hβγ, hαγ, fun z => ⟨hsieve z, ?_⟩⟩
  rintro (rfl | rfl | rfl)
  · exact hβ'
  · simpa only [mul_comm α (β ^ 2)] using hα'
  · simpa [mul_assoc, mul_comm, mul_left_comm] using hγ'

/-- For a nonzero image, the signed bounds on the two reciprocal
contracting roots imply the determinant-cube obstruction. -/
theorem det_cube_le_of_nonzero {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2)
    (hM : Irreducible (incQ S).charpoly)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc S.s ^ k) a c)
    (hne : ∃ j : P.Rep, Psc.Defect5Lie.k5Vec j.1.1 j.1.2 ≠ 0) {β : ℂ}
    (hβ : aeval β (incQ S).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z (incQ S).charpoly = 0 → z ≠ β → ‖z‖ < 1) :
    ‖(((incQ S).det : ℚ) : ℂ)‖ ^ 3 ≤ ‖β‖ := by
  obtain ⟨α, γ, hα, hγ, hβα, hβγ, hαγ, horbit⟩ :=
    sieve5_full_orbit_of_primitive P hbal hM hprim hne hβ hβ1 hpisot
  obtain ⟨-, -, hd, -⟩ :=
    pisot_setup hM hβ hα hγ hαγ hβ1 (hpisot α hα hβα.symm) (hpisot γ hγ hβγ.symm)
  have hbound := ssign_root_bound_of_primitive P hprim
    (fun T hT => (hbal T hT).1.1.1) hβ hβ1 hpisot
  have bound (z : ℂ) (hz : aeval z (q5 P hbal) = 0) : ‖z‖ ≤ ‖β‖ :=
    hbound z (aeval_eq_zero_of_dvd_aeval_eq_zero (q5_dvd_signed P hbal) hz)
  have hb : 0 < ‖β‖ := by linarith
  have hx : ‖β‖ * ‖α‖ * ‖γ‖ * ‖α‖ ≤ 1 := by
    refine le_of_mul_le_mul_left ?_ hb
    rw [mul_one, show ‖β‖ * (‖β‖ * ‖α‖ * ‖γ‖ * ‖α‖) = ‖β‖^2 * ‖α‖^2 * ‖γ‖ by ring]
    simpa only [norm_mul, norm_pow] using bound _ ((horbit _).2 (Or.inr (Or.inr rfl)))
  have hy : ‖β‖ * ‖α‖ * ‖γ‖ * ‖γ‖ ≤ 1 := by
    refine le_of_mul_le_mul_left ?_ hb
    rw [mul_one, show ‖β‖ * (‖β‖ * ‖α‖ * ‖γ‖ * ‖γ‖) = ‖β‖^2 * ‖α‖ * ‖γ‖^2 by ring]
    simpa only [norm_mul, norm_pow] using bound _ ((horbit _).2 (Or.inr (Or.inl rfl)))
  rw [hd, norm_mul, norm_mul]
  calc
    (‖β‖ * ‖α‖ * ‖γ‖)^3 =
        ‖β‖ * ((‖β‖ * ‖α‖ * ‖γ‖ * ‖α‖) * (‖β‖ * ‖α‖ * ‖γ‖ * ‖γ‖)) := by ring
    _ ≤ ‖β‖ * (1 * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hx hy (by positivity) (by norm_num)) hb.le
    _ = ‖β‖ := by simp

end Psc.Degree5Sieve
