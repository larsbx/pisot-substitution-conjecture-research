import PscVerif.C4FamilyCharacterOrbits
import PscVerif.PeriodicPartnerSolenoidHaar
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Haar ergodicity of literal family inflation

The existing injective character orbits give arbitrarily long orthonormal
samples. Finite Bessel and the Archimedean property force every nontrivial
character coefficient of an invariant vector to vanish. The continuous
character density then transfers to Haar `L²`.

Source decision: `docs/c4-family-haar-spectrum-2026-11-21.md`.
-/

namespace Psc.C4FamilyHaarErgodicity

open Function Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal InnerProductSpace Psc.PeriodicPartnerSolenoidHaar
open Psc.ParameterFamilyTiling (geometry)
open Psc.PeriodicPartnerRealization (Solenoid shiftS)
open Psc.PeriodicPartnerSolenoidHaar (haar measurePreserving_shiftS)
open Psc.PeriodicPartnerSolenoidCharacters
open Psc.C4FamilyCharacterOrbits

variable (k : ℕ) (hk : 1 ≤ k)

local notation "G" => Solenoid (geometry k hk)
local notation "μₛ" => haar (geometry k hk)
local notation "σ" => shiftS (geometry k hk)
local notation "H" => Lp ℂ 2 μₛ
local notation "toH" => ContinuousMap.toLp 2 μₛ ℂ

private theorem mul_conj_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z * conj z = 1 := by
  simp [Complex.mul_conj', hz]

/-- Haar translation invariance makes distinct unit-modulus characters orthogonal. -/
theorem haar_inner_eq_zero {f g : C(G, ℂ)} (hne : f ≠ g)
    (hf : ∀ x y, f (x + y) = f x * f y) (hg : ∀ x y, g (x + y) = g x * g y)
    (hnorm : ∀ x, ‖f x‖ = 1) : ⟪toH f, toH g⟫_ℂ = 0 := by
  classical
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ g y := by
    by_contra! hall
    exact hne (ContinuousMap.ext hall)
  let a := g y * conj (f y)
  have hne_one : a ≠ 1 := by
    intro ha
    apply hy
    calc
      f y = a * f y := by rw [ha, one_mul]
      _ = g y := by
        simp only [a, mul_assoc, mul_comm (conj (f y)), mul_conj_eq_one (hnorm y), mul_one]
  rw [ContinuousMap.inner_toLp]
  let J := ∫ x : G, g x * conj (f x) ∂μₛ
  change J = 0
  have hJ : J = a * J := calc
    J = ∫ x : G, g (y + x) * conj (f (y + x)) ∂μₛ :=
      (integral_add_left_eq_self (μ := μₛ) (fun x => g x * conj (f x)) y).symm
    _ = ∫ x : G, a * (g x * conj (f x)) ∂μₛ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change g (y + x) * conj (f (y + x)) = a * (g x * conj (f x))
        rw [hf, hg, map_mul]
        dsimp only [a]
        ac_rfl
    _ = a * J := integral_const_mul a _
  have hz : (a - 1) * J = 0 := by rw [sub_mul, one_mul, ← hJ, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne_one)

/-- Normalization of Haar probability makes every unit-modulus character a unit vector. -/
theorem haar_inner_self {f : C(G, ℂ)} (hnorm : ∀ x, ‖f x‖ = 1) :
    ⟪toH f, toH f⟫_ℂ = 1 := by
  rw [ContinuousMap.inner_toLp]
  simp [mul_conj_eq_one (hnorm _)]

/-- Each certificate represents an element of Haar `L²`. -/
noncomputable def characterLp (c : Certificate (Fin 3)) : H :=
  toH (character (geometry k hk) c)

/-- The Haar `L²` span uses the existing full-history characters. -/
theorem span_characterLp_closure_eq_top :
    (Submodule.span ℂ (range (characterLp k hk))).topologicalClosure = ⊤ := by
  have hd := ContinuousMap.toLp_denseRange (μ := μₛ) (𝕜 := ℂ) (E := ℂ)
    (show (2 : ℝ≥0∞) ≠ ⊤ by norm_num)
  have h := hd.topologicalClosure_map_submodule (span_character_closure_eq_top (geometry k hk))
  rw [Submodule.map_span, ← range_comp] at h
  exact h

/-- Any finite sample of the nontrivial character orbit is orthonormal. -/
theorem orthonormal_finite_orbit (c : Certificate (Fin 3))
    (hc : character (geometry k hk) c ≠ 1) (N : ℕ) :
    Orthonormal ℂ (fun i : Fin N => toH (orbitCharacter k hk c i.1)) := by
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i = j
  · subst j
    simpa using haar_inner_self k hk (orbitCharacter_norm k hk c i.1)
  · rw [ite_eq_right hij]
    exact haar_inner_eq_zero k hk (fun h => hij (finite_orbit_injective k hk c hc N h))
      (orbitCharacter_map_add k hk c i.1) (orbitCharacter_map_add k hk c j.1)
      (orbitCharacter_norm k hk c i.1)

private theorem orbit_toLp_eq (c : Certificate (Fin 3)) (n : ℕ) :
    toH (orbitCharacter k hk c n) =
      Lp.compMeasurePreserving (σ^[n]) ((measurePreserving_shiftS _).iterate n)
        (characterLp k hk c) := by
  apply Lp.ext
  have hp := (measurePreserving_shiftS (geometry k hk)).iterate n
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μₛ (orbitCharacter k hk c n),
    Lp.coeFn_compMeasurePreserving (characterLp k hk c) hp,
    hp.quasiMeasurePreserving.ae (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μₛ
      (character (geometry k hk) c))] with x hleft hright hcomp
  rw [hleft, hright, Function.comp_apply]
  exact hcomp.symm

/-- Finite Bessel on the first `N` distinct characters bounds `N` times the
squared modulus of the original coefficient of a fixed vector. -/
theorem finite_bessel_bound (u : H)
    (hu : Lp.compMeasurePreserving σ (measurePreserving_shiftS _) u = u)
    (c : Certificate (Fin 3)) (hc : character (geometry k hk) c ≠ 1) (N : ℕ) :
    (N : ℝ) * ‖⟪characterLp k hk c, u⟫_ℂ‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  have hcoeff (n : ℕ) : ⟪toH (orbitCharacter k hk c n), u⟫_ℂ =
      ⟪characterLp k hk c, u⟫_ℂ := by
    have hu' : Lp.compMeasurePreserving (σ^[n]) ((measurePreserving_shiftS _).iterate n) u = u := by
      rw [← Lp.compMeasurePreserving_iterate]
      exact IsFixedPt.iterate hu n
    let U : H →ₗᵢ[ℂ] H := Lp.compMeasurePreservingₗᵢ ℂ (σ^[n])
      ((measurePreserving_shiftS _).iterate n)
    calc
      _ = ⟪U (characterLp k hk c), U u⟫_ℂ := by
        change _ = ⟪_, Lp.compMeasurePreserving (σ^[n]) _ u⟫_ℂ
        rw [orbit_toLp_eq, hu']
        rfl
      _ = _ := U.inner_map_map _ _
  have h := (orthonormal_finite_orbit k hk c hc N).sum_inner_products_le u (s := Finset.univ)
  simpa only [hcoeff, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h

/-- An invariant vector has zero coefficient at every nontrivial character. -/
theorem fixed_coefficient_eq_zero (u : H)
    (hu : Lp.compMeasurePreserving σ (measurePreserving_shiftS _) u = u)
    (c : Certificate (Fin 3)) (hc : character (geometry k hk) c ≠ 1) :
    ⟪characterLp k hk c, u⟫_ℂ = 0 := by
  by_contra h
  have hpos : 0 < ‖⟪characterLp k hk c, u⟫_ℂ‖ ^ 2 := pow_pos (norm_pos_iff.mpr h) 2
  obtain ⟨N, hN⟩ := exists_nat_gt (‖u‖ ^ 2 / ‖⟪characterLp k hk c, u⟫_ℂ‖ ^ 2)
  exact (not_lt_of_ge (finite_bessel_bound k hk u hu c hc N)) ((div_lt_iff₀ hpos).mp hN)

/-- Every fixed vector for actual solenoid inflation is constant. -/
theorem fixed_eq_smul_one (u : H)
    (hu : Lp.compMeasurePreserving σ (measurePreserving_shiftS _) u = u) :
    u = ⟪characterLp k hk 0, u⟫_ℂ • characterLp k hk 0 := by
  let one := characterLp k hk 0
  let v := u - ⟪one, u⟫_ℂ • one
  have hone : ⟪one, one⟫_ℂ = 1 := haar_inner_self k hk (character_norm (geometry k hk) 0)
  have hcoeff (c : Certificate (Fin 3)) : ⟪characterLp k hk c, v⟫_ℂ = 0 := by
    by_cases hc : character (geometry k hk) c = 1
    · have heq : characterLp k hk c = one := by
        simp only [one, characterLp, hc, character_zero]
      dsimp only [v]
      rw [heq, inner_sub_right, inner_smul_right, hone, mul_one, sub_self]
    · have horth : ⟪characterLp k hk c, one⟫_ℂ = 0 :=
        haar_inner_eq_zero k hk (by simpa only [character_zero] using hc)
          (character_map_add (geometry k hk) c) (character_map_add (geometry k hk) 0)
          (character_norm (geometry k hk) c)
      simp [v, fixed_coefficient_eq_zero k hk u hu c hc, horth, inner_sub_right, inner_smul_right]
  have horth : v ∈ (Submodule.span ℂ (range (characterLp k hk)))ᗮ := by
    refine (Submodule.mem_orthogonal _ _).mpr (fun x hx => ?_)
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; exact hcoeff c
    | zero => exact inner_zero_left _
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
  rw [← Submodule.orthogonal_closure, span_characterLp_closure_eq_top,
    Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at horth
  exact sub_eq_zero.mp horth

/-- The actual full-history inflation is ergodic for normalized Haar measure. -/
theorem ergodic_shiftS : Ergodic σ μₛ where
  toMeasurePreserving := measurePreserving_shiftS _
  aeconst_set {A} hA hinv := by
    let u : H := indicatorConstLp 2 hA (measure_ne_top μₛ A) (1 : ℂ)
    have hu : Lp.compMeasurePreserving σ (measurePreserving_shiftS _) u = u := by
      dsimp only [u]
      rw [Lp.indicatorConstLp_compMeasurePreserving]
      congr 1
    let a := ⟪characterLp k hk 0, u⟫_ℂ
    have hconstant : u = a • characterLp k hk 0 := fixed_eq_smul_one k hk u hu
    have hAe : ∀ᵐ x ∂μₛ, A.indicator (fun _ => (1 : ℂ)) x = a := by
      have hOne : (characterLp k hk 0 : G → ℂ) =ᵐ[μₛ] fun _ => 1 := by
        simpa only [characterLp, character_zero, ContinuousMap.coe_one, Pi.one_def] using
          (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μₛ (1 : C(G, ℂ)))
      filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := μₛ) (c := (1 : ℂ))
        (hs := hA) (hμs := measure_ne_top μₛ A), Lp.coeFn_smul a (characterLp k hk 0), hOne]
        with x hx hs hxOne
      change u x = A.indicator (fun _ => (1 : ℂ)) x at hx
      calc
        _ = u x := hx.symm
        _ = (a • characterLp k hk 0) x := congrArg (fun v : H => v x) hconstant
        _ = a * characterLp k hk 0 x := hs
        _ = a := by rw [hxOne, mul_one]
    rw [eventuallyEmptyOrUniv_iff]
    by_cases ha : a = 1
    · left
      filter_upwards [hAe] with x hx
      by_contra hxA
      simp [Set.indicator_of_notMem hxA, ha] at hx
    · right
      filter_upwards [hAe] with x hx hxA
      exact ha (hx.symm.trans (Set.indicator_of_mem hxA _))

end Psc.C4FamilyHaarErgodicity
