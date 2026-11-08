import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
Deductive interface for the fixed-incidence overlap certificates of PR #496.

Occurrences are indexed independently of their targets: parallel edges count
separately. The generic theorem does not assert that a supplied graph covers
the actual prefix-set intersections. That semantic cover, the compact model,
its scaling, and the strict-cut lower bound remain explicit hypotheses.
No concrete 18-source certificate is asserted to have been imported into Lean.
-/

namespace PscVerif.OverlapContraction

open scoped BigOperators NNReal ENNReal
open Function MeasureTheory

/-- Uniqueness of a fixed iterate supplies one-step invariance. -/
theorem fixed_of_unique_iterate {α : Type*} (F : α → α) (m : ℕ) (K : α)
    (hK : F^[m] K = K)
    (unique : ∀ L, F^[m] L = L → L = K) : F K = K := by
  apply unique
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hK]

/-- Banach uniqueness authenticates every refinement step, even when it does
not divide the period of the originally chosen fixed word. -/
theorem invariant_of_contracting_iterate {α : Type*} [MetricSpace α]
    (F : α → α) (m : ℕ) (K : α) (c : ℝ≥0)
    (hc : ContractingWith c (F^[m])) (hK : F^[m] K = K) (step : ℕ) :
    F^[step] K = K := by
  have one : F K = K := fixed_of_unique_iterate F m K hK (by
    intro L hL
    exact hc.fixedPoint_unique' hL hK)
  exact (show IsFixedPt F K from one).iterate step

/-- In particular the period-three prefix sets can use the two-step graph,
once their F^12 identity and its contraction have been supplied. -/
theorem two_step_of_twelve {α : Type*} [MetricSpace α]
    (F : α → α) (K : α) (c : ℝ≥0)
    (hc : ContractingWith c (F^[12])) (hK : F^[12] K = K) :
    F^[2] K = K := invariant_of_contracting_iterate F 12 K c hc hK 2

/-- The original prefix-word period need only divide the contracting block. -/
theorem block_fixed_of_period {α : Type*} (F : α → α) (K : α) (q m : ℕ)
    (divides : q ∣ m) (period : F^[q] K = K) : F^[m] K = K := by
  obtain ⟨r, rfl⟩ := divides
  rw [Function.iterate_mul]
  exact (show IsFixedPt (F^[q]) K from period).iterate r

theorem period_three_two_step {α : Type*} [MetricSpace α]
    (F : α → α) (K : α) (c : ℝ≥0)
    (hc : ContractingWith c (F^[12])) (period : F^[3] K = K) :
    F^[2] K = K := by
  exact two_step_of_twelve F K c hc
    (block_fixed_of_period F K 3 12 (by decide) period)

section FiniteComparison

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable (κ : ι → Type*) [∀ i, Fintype (κ i)]
variable (target : (i : ι) → κ i → ι)

/-- Finite weighted maximum argument. No spectral-radius approximation or
convergence of a weight-search algorithm is used. -/
theorem zero_of_subinvariant (v w : ι → ℝ) (scale rate : ℝ)
    (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 < w i)
    (recurrence : ∀ i, scale * v i ≤ ∑ e, v (target i e))
    (weights : ∀ i, (∑ e, w (target i e)) ≤ rate * w i)
    (gap : rate < scale) : ∀ i, v i = 0 := by
  obtain ⟨k, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => v i / w i) Finset.univ_nonempty
  let C := v k / w k
  have hC : 0 ≤ C := div_nonneg (hv k) (hw k).le
  have bound : ∀ i, v i ≤ C * w i := by
    intro i
    exact (div_le_iff₀ (hw i)).mp (hmax i (Finset.mem_univ i))
  have at_max : C * w k = v k := div_mul_cancel₀ _ (ne_of_gt (hw k))
  have sum_bound : (∑ e, v (target k e)) ≤ C * ∑ e, w (target k e) := by
    calc
      _ ≤ ∑ e, C * w (target k e) := Finset.sum_le_sum (fun e _ => bound _)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have impossible : scale * v k ≤ rate * v k := by
    calc
      _ ≤ ∑ e, v (target k e) := recurrence k
      _ ≤ C * ∑ e, w (target k e) := sum_bound
      _ ≤ C * (rate * w k) := mul_le_mul_of_nonneg_left (weights k) hC
      _ = rate * v k := by rw [← at_max]; ring
  have vk : v k = 0 := by nlinarith [hv k]
  have Cz : C = 0 := by simp [C, vk]
  intro i
  have hi := bound i
  rw [Cz, zero_mul] at hi
  exact le_antisymm hi (hv i)

end FiniteComparison

/-- A typed occurrence graph. `degree` counts occurrences, not distinct
targets; malformed target indices cannot inhabit this structure. -/
structure Certificate (n : ℕ) where
  degree : Fin n → ℕ
  target : (i : Fin n) → Fin (degree i) → Fin n
  weight : Fin n → ℕ
  numerator : ℕ
  denominator : ℕ

def Certificate.Valid {n : ℕ} (cert : Certificate n) : Prop :=
  0 < cert.denominator ∧ ∀ i, 0 < cert.weight i ∧
    cert.denominator * (∑ e, cert.weight (cert.target i e)) ≤
      cert.numerator * cert.weight i

instance {n : ℕ} (cert : Certificate n) : Decidable cert.Valid := by
  unfold Certificate.Valid
  infer_instance

/-- Kernel-decidable integer certificate validation. This definition does not
authenticate a packet or the geometry of the graph supplied to it. -/
def Certificate.check {n : ℕ} (cert : Certificate n) : Bool := decide cert.Valid

theorem Certificate.check_iff {n : ℕ} (cert : Certificate n) :
    cert.check = true ↔ cert.Valid := by simp [Certificate.check]

/-- Accepted natural-number inequalities imply the real comparison theorem. -/
theorem Certificate.sound {n : ℕ} [Nonempty (Fin n)] (cert : Certificate n)
    (accepted : cert.check = true) (v : Fin n → ℝ) (scale : ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (recurrence : ∀ i, scale * v i ≤ ∑ e, v (cert.target i e))
    (gap : (cert.numerator : ℝ) < cert.denominator * scale) :
    ∀ i, v i = 0 := by
  obtain ⟨hd, hc⟩ := cert.check_iff.mp accepted
  have hdR : (0 : ℝ) < cert.denominator := by exact_mod_cast hd
  apply zero_of_subinvariant (fun i => Fin (cert.degree i)) cert.target v
    (fun i => (cert.weight i : ℝ)) scale
    ((cert.numerator : ℝ) / cert.denominator) hv
  · intro i
    exact_mod_cast (hc i).1
  · exact recurrence
  · intro i
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hdR).mpr
    have h := (hc i).2
    have hR : (cert.denominator : ℝ) * (∑ e, (cert.weight (cert.target i e) : ℝ)) ≤
        cert.numerator * cert.weight i := by exact_mod_cast h
    nlinarith
  · exact (div_lt_iff₀ hdR).mpr (by nlinarith)

section MeasureCover

variable {α ι : Type*} [MeasurableSpace α]
variable (κ : ι → Type*) [∀ i, Fintype (κ i)]
variable (target : (i : ι) → κ i → ι)

/-- Complete set covers and per-occurrence scaling yield the real recurrence.
No disjointness of retained pieces is assumed. -/
theorem recurrence_of_cover (μ : Measure α) (E : ι → Set α)
    (piece : (i : ι) → κ i → Set α) (scale : ℝ)
    (hs : 0 ≤ scale) (finite : ∀ i, μ (E i) ≠ ⊤)
    (cover : ∀ i, E i ⊆ ⋃ e, piece i e)
    (scaling : ∀ i e, ENNReal.ofReal scale * μ (piece i e) ≤ μ (E (target i e))) :
    ∀ i, scale * (μ (E i)).toReal ≤ ∑ e, (μ (E (target i e))).toReal := by
  intro i
  have bound : ENNReal.ofReal scale * μ (E i) ≤ ∑ e, μ (E (target i e)) := by
    calc
      _ ≤ ENNReal.ofReal scale * μ (⋃ e, piece i e) :=
        mul_le_mul_right (measure_mono (cover i)) _
      _ ≤ ENNReal.ofReal scale * ∑ e, μ (piece i e) :=
        mul_le_mul_right (measure_iUnion_fintype_le μ (piece i)) _
      _ = ∑ e, ENNReal.ofReal scale * μ (piece i e) := Finset.mul_sum _ _ _
      _ ≤ _ := Finset.sum_le_sum (fun e _ => scaling i e)
  have right_finite : (∑ e, μ (E (target i e))) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.mpr (fun e _ => finite _)
  have h := ENNReal.toReal_mono right_finite bound
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hs,
    ENNReal.toReal_sum (fun e _ => finite (target i e))] using h

/-- Formal null-overlap theorem at an explicit geometric interface. -/
theorem null_of_cover [Fintype ι] [Nonempty ι] (μ : Measure α) (E : ι → Set α)
    (piece : (i : ι) → κ i → Set α) (scale rate : ℝ) (w : ι → ℝ)
    (hs : 0 ≤ scale) (finite : ∀ i, μ (E i) ≠ ⊤)
    (cover : ∀ i, E i ⊆ ⋃ e, piece i e)
    (scaling : ∀ i e, ENNReal.ofReal scale * μ (piece i e) ≤ μ (E (target i e)))
    (hw : ∀ i, 0 < w i)
    (weights : ∀ i, (∑ e, w (target i e)) ≤ rate * w i)
    (gap : rate < scale) : ∀ i, μ (E i) = 0 := by
  have hz := zero_of_subinvariant κ target (fun i => (μ (E i)).toReal) w scale rate
    (fun _ => ENNReal.toReal_nonneg) hw
    (recurrence_of_cover κ target μ E piece scale hs finite cover scaling) weights gap
  intro i
  exact (ENNReal.toReal_eq_zero_iff (μ (E i))).mp (hz i) |>.resolve_right (finite i)

end MeasureCover

/-- Composition of the integer checker with the analytic cover interface.
Acceptance alone cannot supply the cover or Haar scaling hypotheses. -/
theorem Certificate.null_of_cover {n : ℕ} [Nonempty (Fin n)]
    {α : Type*} [MeasurableSpace α] (cert : Certificate n)
    (accepted : cert.check = true) (μ : Measure α) (E : Fin n → Set α)
    (piece : (i : Fin n) → Fin (cert.degree i) → Set α) (scale : ℝ)
    (hs : 0 ≤ scale) (finite : ∀ i, μ (E i) ≠ ⊤)
    (cover : ∀ i, E i ⊆ ⋃ e, piece i e)
    (scaling : ∀ i e, ENNReal.ofReal scale * μ (piece i e) ≤ μ (E (cert.target i e)))
    (gap : (cert.numerator : ℝ) < cert.denominator * scale) :
    ∀ i, μ (E i) = 0 := by
  have hz := cert.sound accepted (fun i => (μ (E i)).toReal) scale
    (fun _ => ENNReal.toReal_nonneg)
    (recurrence_of_cover (fun i => Fin (cert.degree i)) cert.target
      μ E piece scale hs finite cover scaling) gap
  intro i
  exact (ENNReal.toReal_eq_zero_iff (μ (E i))).mp (hz i) |>.resolve_right (finite i)

/-- The specific 102/20 rate of the canonical class, conditional on importing
a valid certificate and establishing its full geometric cover. -/
theorem Certificate.class_rate_null {n : ℕ} [Nonempty (Fin n)]
    {α : Type*} [MeasurableSpace α] (cert : Certificate n)
    (accepted : cert.check = true) (num : cert.numerator = 102)
    (den : cert.denominator = 20) (μ : Measure α) (E : Fin n → Set α)
    (piece : (i : Fin n) → Fin (cert.degree i) → Set α) (β : ℝ)
    (spectral : (103 / 20 : ℝ) < β ^ 2)
    (finite : ∀ i, μ (E i) ≠ ⊤) (cover : ∀ i, E i ⊆ ⋃ e, piece i e)
    (scaling : ∀ i e, ENNReal.ofReal (β ^ 2) * μ (piece i e) ≤ μ (E (cert.target i e))) :
    ∀ i, μ (E i) = 0 := by
  apply cert.null_of_cover accepted μ E piece (β ^ 2) (sq_nonneg β) finite cover scaling
  rw [num, den]
  norm_num
  linarith

/-- Positive measure inside a finite union of null roots is impossible.
The strict-cut lower bound must be proved by the caller, not postulated globally. -/
theorem no_positive_subset_of_null {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) (roots : ι → Set α) (Z : Set α)
    (null : ∀ i, μ (roots i) = 0) (cover : Z ⊆ ⋃ i, roots i)
    (positive : 0 < μ Z) : False := by
  have hz : μ Z ≤ 0 := by
    calc
      _ ≤ μ (⋃ i, roots i) := measure_mono cover
      _ ≤ ∑ i, μ (roots i) := measure_iUnion_fintype_le μ roots
      _ = 0 := by simp [null]
  exact (not_lt_of_ge hz) positive

/-- The determinant/Haar factors in the stated compact model cancel exactly.
This is scalar algebra, not a construction of M-adic Haar measure. -/
theorem product_scaling (β D : ℝ) (hβ : β ≠ 0) (hD : D ≠ 0) :
    (D / β) * (1 / D) = 1 / β := by field_simp

theorem common_box_arithmetic :
    (473 / 1000 : ℚ) + (390 / 1000) / 2 = 167 / 250 ∧
    2 * (147 / 1000 : ℚ) + 344 / 1000 < 167 / 250 ∧
    (13 / 2 : ℚ) + (473 * 24 + 390 * 12) / 1000 < 24 ∧
    (4 : ℚ) + (147 * 24 + 344 * 12) / 1000 < 12 := by norm_num

/-- A calibration with parallel edges. Removing multiplicity would change it. -/
def parallelControl : Certificate 1 where
  degree := fun _ => 6
  target := fun _ _ => 0
  weight := fun _ => 1
  numerator := 102
  denominator := 20

theorem six_parallel_edges_refused : parallelControl.check = false := by decide

def zeroWeightControl : Certificate 1 where
  degree := fun _ => 0
  target := fun _ e => Fin.elim0 e
  weight := fun _ => 0
  numerator := 102
  denominator := 20

theorem zero_weight_refused : zeroWeightControl.check = false := by decide

def terminalControl : Certificate 1 where
  degree := fun _ => 0
  target := fun _ e => Fin.elim0 e
  weight := fun _ => 1
  numerator := 102
  denominator := 20

theorem terminal_control_accepted : terminalControl.check = true := by decide

def equalRateControl : Certificate 1 where
  degree := fun _ => 1
  target := fun _ _ => 0
  weight := fun _ => 1
  numerator := 1
  denominator := 1

/-- Without a strict rate gap a valid certificate can support positive mass. -/
theorem equal_rate_does_not_force_zero :
    equalRateControl.check = true ∧
    (∀ i : Fin 1, (1 : ℝ) * 1 ≤ ∑ _e : Fin (equalRateControl.degree i), (1 : ℝ)) ∧
    ¬ (∀ _i : Fin 1, (1 : ℝ) = 0) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro i
    norm_num [equalRateControl]
  · norm_num

def periodThreeControl (i : Fin 3) : Fin 3 :=
  ⟨(i.val + 1) % 3, Nat.mod_lt _ (by decide)⟩

/-- Period three by itself does not justify using step two. -/
theorem period_alone_does_not_supply_two_step :
    periodThreeControl^[3] 0 = 0 ∧ periodThreeControl^[2] 0 ≠ 0 := by decide

end PscVerif.OverlapContraction
