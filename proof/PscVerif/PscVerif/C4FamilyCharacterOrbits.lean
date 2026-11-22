import PscVerif.C4FamilySolenoidCharacters

/-!
# Distinct finite samples of actual character inflation orbits

Inflation scales the actual real flow by the positive expansion. The finite
certificate frequency therefore scales by the corresponding expansion power.
Equality of two orbit characters forces equality of those real frequencies.
A nontrivial character has nonzero frequency because the already constructed
real flow is dense. Its forward inflation orbit is consequently injective.

The argument uses finite matrix algebra, circle coordinates, and the existing
dense-flow theorem. It supplies arbitrary finite samples of distinct continuous
characters, without assuming Haar orthogonality, `L2` completeness, or ergodicity.
The nontriviality hypothesis is on the replayed character, not on the certificate.
Source decision: `docs/c4-finite-fibre-obligations-2026-11-21.md`.
-/

namespace Psc.C4FamilyCharacterOrbits

open Function Set Matrix
open Psc.ParameterFamilyTiling Psc.ParameterFamilySolenoid
open Psc.PeriodicPartnerRealization Psc.PeriodicPartnerRealizationOnto
open Psc.PeriodicPartnerSolenoidCharacters

variable (k : ℕ) (hk : 1 ≤ k)

/-- Actual solenoid inflation scales the real-flow parameter by the
family's expansion. This is the finite unstable-eigenvector identity. -/
theorem shiftS_flow (t : ℝ) (z : Solenoid (geometry k hk)) :
    shiftS (geometry k hk) (flow (pisotData k hk) t z) =
      flow (pisotData k hk) ((geometry k hk).β * t) (shiftS (geometry k hk) z) := by
  apply Subtype.ext
  funext n
  change torusMap (geometry k hk)
      (z.1 n + (((t / (geometry k hk).β ^ n) • (pisotData k hk).u : Fin 3 → ℝ) :
        Torus (Fin 3))) =
    torusMap (geometry k hk) (z.1 n) +
      (((((geometry k hk).β * t) / (geometry k hk).β ^ n) •
        (pisotData k hk).u : Fin 3 → ℝ) : Torus (Fin 3))
  rw [map_add, torusMap_mk, mulVec_smul, (pisotData k hk).u_eigen, smul_smul]
  have hscalar : (t / (geometry k hk).β ^ n) * (geometry k hk).β =
      ((geometry k hk).β * t) / (geometry k hk).β ^ n := by ring
  rw [hscalar]

/-- Finite iteration scales the real-flow parameter by the matching power. -/
theorem shiftS_iterate_flow (n : ℕ) (t : ℝ) (z : Solenoid (geometry k hk)) :
    (shiftS (geometry k hk))^[n] (flow (pisotData k hk) t z) =
      flow (pisotData k hk) ((geometry k hk).β ^ n * t)
        ((shiftS (geometry k hk))^[n] z) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iterate_succ_apply', ih, shiftS_flow]
      simp only [iterate_succ_apply', pow_succ', mul_assoc]

theorem shiftS_iterate_zero (n : ℕ) :
    (shiftS (geometry k hk))^[n] 0 = 0 :=
  IsFixedPt.iterate (shiftS_zero (geometry k hk)) n

/-- The continuous character obtained by composing with a finite number
of actual full-history inflation steps. -/
noncomputable def orbitCharacter (c : Certificate (Fin 3)) (n : ℕ) :
    C(Solenoid (geometry k hk), ℂ) where
  toFun z := character (geometry k hk) c ((shiftS (geometry k hk))^[n] z)
  continuous_toFun := (character (geometry k hk) c).continuous.comp
    ((shiftHomeomorph (geometry k hk)).continuous.iterate n)

@[simp]
theorem orbitCharacter_apply (c : Certificate (Fin 3)) (n : ℕ)
    (z : Solenoid (geometry k hk)) :
    orbitCharacter k hk c n z = character (geometry k hk) c
      ((shiftS (geometry k hk))^[n] z) := rfl

@[simp]
theorem orbitCharacter_zero (c : Certificate (Fin 3)) :
    orbitCharacter k hk c 0 = character (geometry k hk) c := by
  ext z
  rfl

/-- Every orbit sample still has unit modulus at every actual history. -/
theorem orbitCharacter_norm (c : Certificate (Fin 3)) (n : ℕ)
    (z : Solenoid (geometry k hk)) : ‖orbitCharacter k hk c n z‖ = 1 :=
  character_norm (geometry k hk) c _

/-- Finite inflation preserves addition, so every orbit sample is an
actual multiplicative group character, not only a continuous function. -/
theorem orbitCharacter_map_add (c : Certificate (Fin 3)) (n : ℕ)
    (z w : Solenoid (geometry k hk)) :
    orbitCharacter k hk c n (z + w) =
      orbitCharacter k hk c n z * orbitCharacter k hk c n w := by
  have hadd (m : ℕ) : (shiftS (geometry k hk))^[m] (z + w) =
      (shiftS (geometry k hk))^[m] z + (shiftS (geometry k hk))^[m] w := by
    induction m with
    | zero => rfl
    | succ m ih =>
        simp only [iterate_succ_apply', ih]
        apply Subtype.ext
        funext j
        exact map_add (torusMap (geometry k hk))
          (((shiftS (geometry k hk))^[m] z).1 j) (((shiftS (geometry k hk))^[m] w).1 j)
  simp only [orbitCharacter_apply, hadd, character_map_add]

/-- On the dense real flow, the orbit character has the explicit scaled
finite-certificate frequency. -/
theorem orbitCharacter_flow_zero (c : Certificate (Fin 3)) (n : ℕ) (t : ℝ) :
    orbitCharacter k hk c n (flow (pisotData k hk) t 0) =
      (AddCircle.toCircle (((t * ((geometry k hk).β ^ n *
        frequency (geometry k hk) (pisotData k hk) c) : ℝ) : UnitAddCircle)) : ℂ) := by
  rw [orbitCharacter_apply, shiftS_iterate_flow, shiftS_iterate_zero,
    character_apply, phase_flow_zero]
  have hscalar : ((geometry k hk).β ^ n * t) *
      frequency (geometry k hk) (pisotData k hk) c =
      t * ((geometry k hk).β ^ n * frequency (geometry k hk) (pisotData k hk) c) := by
    ring
  rw [hscalar]

/-- Vanishing of a real frequency follows from its vanishing modulo one
at every real parameter. One half-period refutes a nonzero frequency. -/
private theorem real_eq_zero_of_circle_multiples_zero (d : ℝ)
    (h : ∀ t : ℝ, ((t * d : ℝ) : UnitAddCircle) = 0) : d = 0 := by
  by_contra hd
  have hhalf := h ((1 / 2) / d)
  rw [div_mul_cancel₀ _ hd] at hhalf
  have hzero : (1 / 2 : ℝ) = 0 :=
    (AddCircle.coe_eq_zero_iff_of_mem_Ico
      (by norm_num : (1 / 2 : ℝ) ∈ Ico 0 1)).mp hhalf
  norm_num at hzero

/-- Equality of orbit characters forces equality of their actual real
frequencies, not merely agreement modulo an integer at one time. -/
theorem scaled_frequency_eq_of_orbitCharacter_eq (c : Certificate (Fin 3)) {m n : ℕ}
    (h : orbitCharacter k hk c m = orbitCharacter k hk c n) :
    (geometry k hk).β ^ m * frequency (geometry k hk) (pisotData k hk) c =
      (geometry k hk).β ^ n * frequency (geometry k hk) (pisotData k hk) c := by
  have hphase (t : ℝ) :
      ((t * ((geometry k hk).β ^ m * frequency (geometry k hk) (pisotData k hk) c) : ℝ) :
        UnitAddCircle) =
      ((t * ((geometry k hk).β ^ n * frequency (geometry k hk) (pisotData k hk) c) : ℝ) :
        UnitAddCircle) := by
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.coe_injective
    simpa only [orbitCharacter_flow_zero] using
      congrArg (fun f : C(Solenoid (geometry k hk), ℂ) => f (flow (pisotData k hk) t 0)) h
  apply sub_eq_zero.mp
  apply real_eq_zero_of_circle_multiples_zero
  intro t
  rw [mul_sub, AddCircle.coe_sub]
  exact sub_eq_zero.mpr (hphase t)

/-- A zero-frequency finite character is trivial on the dense real flow,
hence everywhere by continuity. The dense-flow theorem is reused explicitly. -/
theorem character_eq_one_of_frequency_eq_zero (c : Certificate (Fin 3))
    (h : frequency (geometry k hk) (pisotData k hk) c = 0) :
    character (geometry k hk) c = 1 := by
  apply ContinuousMap.coe_injective
  apply (denseRange_flow_zero (pisotData k hk)).equalizer
    (character (geometry k hk) c).continuous (continuous_const : Continuous (fun _ => (1 : ℂ)))
  funext t
  simp only [Function.comp_apply, character_flow, character_at_zero, h, mul_zero,
    Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]

/-- The forward inflation orbit of a nontrivial actual character is
injective. Distinctness is not inferred from a nonzero certificate alone. -/
theorem orbitCharacter_injective (c : Certificate (Fin 3))
    (hc : character (geometry k hk) c ≠ 1) : Injective (orbitCharacter k hk c) := by
  intro m n h
  have hfreq : frequency (geometry k hk) (pisotData k hk) c ≠ 0 :=
    fun hzero => hc (character_eq_one_of_frequency_eq_zero k hk c hzero)
  have hpowers := mul_right_cancel₀ hfreq (scaled_frequency_eq_of_orbitCharacter_eq k hk c h)
  exact (pow_right_strictMono₀ (expansion_gt_one k hk)).injective hpowers

/-- No nontrivial finite-certificate character has a positive inflation
period on the actual solenoid. -/
theorem character_eq_one_of_inflation_period (c : Certificate (Fin 3))
    {p : ℕ} (hp : 0 < p)
    (hperiod : ∀ z : Solenoid (geometry k hk),
      character (geometry k hk) c ((shiftS (geometry k hk))^[p] z) =
        character (geometry k hk) c z) :
    character (geometry k hk) c = 1 := by
  by_contra hc
  have heq : orbitCharacter k hk c p = orbitCharacter k hk c 0 := by
    ext z
    simpa only [orbitCharacter_apply, iterate_zero_apply] using hperiod z
  exact (Nat.ne_of_gt hp) (orbitCharacter_injective k hk c hc heq)

/-- Every requested finite initial orbit sample consists of distinct
continuous characters. This is the algebraic input for a later finite Bessel argument. -/
theorem finite_orbit_injective (c : Certificate (Fin 3))
    (hc : character (geometry k hk) c ≠ 1) (N : ℕ) :
    Injective (fun i : Fin N => orbitCharacter k hk c i.1) :=
  (orbitCharacter_injective k hk c hc).comp Fin.val_injective

/-! ## A nonzero certificate can replay to the trivial character -/

/-- The literal third-row compatibility equation between levels zero and one. -/
noncomputable def compatibilityCertificate : Certificate (Fin 3) :=
  Finsupp.single (0, (2 : Fin 3)) 1 + -Finsupp.single (1, (1 : Fin 3)) 1

theorem compatibilityCertificate_ne_zero : compatibilityCertificate ≠ 0 := by
  intro h
  have hcoord := congrArg (fun c : Certificate (Fin 3) => c (0, (2 : Fin 3))) h
  norm_num [compatibilityCertificate] at hcoord

/-- The exact incidence row gives zero frequency for this nonzero certificate. -/
theorem compatibilityCertificate_frequency :
    frequency (geometry k hk) (pisotData k hk) compatibilityCertificate = 0 := by
  have heigen : (pisotData k hk).u 1 = (geometry k hk).β * (pisotData k hk).u 2 := by
    have h := congrFun (pisotData k hk).u_eigen (2 : Fin 3)
    rw [mat_eq, Psc.ParameterFamilyPisot.incidenceQ_eq] at h
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.map_apply] using h
  simp only [compatibilityCertificate, frequency_add, frequency_neg, frequency_single,
    Int.cast_one, one_mul, pow_zero, div_one, pow_one]
  rw [heigen]
  simp [(geometry k hk).β_pos.ne']

/-- This actual nonzero compatibility certificate has the constant orbit.
It refutes replacing the nontrivial-character hypothesis by `c ≠ 0`. -/
theorem compatibilityCertificate_character :
    character (geometry k hk) compatibilityCertificate = 1 :=
  character_eq_one_of_frequency_eq_zero k hk compatibilityCertificate
    (compatibilityCertificate_frequency k hk)

end Psc.C4FamilyCharacterOrbits
