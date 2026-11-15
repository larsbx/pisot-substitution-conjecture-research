/-
# Literal lower-chamber minus-Class-A arithmetic

This module connects a bracketed root of the displayed literal cubic to the
positive tile lengths, the actual substitution scaling, and the constant-tail
recurrence. Root existence is proved separately. No spectral identification,
half-unit exclusion, or all-source central entrance is hidden in the adapter.

Pre-code scope: `docs/bh-class-a-literal-lean-stop-go-2026-11-14.md`.
-/
import PscVerif.ClassAMinusConstantRecurrence
import Mathlib.Topology.Order.IntermediateValue

namespace Psc.ClassAMinusLiteralArithmetic

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn Psc.OccurrenceTransport
open Psc.ClassAZeroDefectEscape Psc.ClassAMinusConstantRecurrence Matrix

def cubic (n d : ℕ) (β : ℝ) : ℝ :=
  β^3 - ((n : ℝ)+2)*β^2 + ((n : ℝ)-(d : ℝ)-1)*β + 2

/-- The finite algebraic root interface, before any spectral identification. -/
structure RootData (n d : ℕ) (β : ℝ) : Prop where
  cubic_eq_zero : cubic n d β = 0
  lower : (n : ℝ)+1 < β
  upper : β < (n : ℝ)+2

/-- Coordinate order is x,c,y; y has unit length. -/
noncomputable def lengths (n : ℕ) (β : ℝ) : Fin 3 → ℝ :=
  ![β-(n : ℝ)-1/β, 1+1/β, 1]

theorem lower_chamber_n (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n) : 6 ≤ n := by
  omega

theorem root_pos {n d : ℕ} {β : ℝ} (hroot : RootData n d β) : 0 < β := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith [hroot.lower]

theorem root_sub_one_pos {n d : ℕ} {β : ℝ} (hroot : RootData n d β) : 0 < β-1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith [hroot.lower]

/-- The cubic supplies the exact positive contraction reserve. -/
theorem root_delta_identity {n d : ℕ} {β : ℝ} (hroot : RootData n d β) :
    1-2/β-((n : ℝ)+2-β) = (d : ℝ)/(β-1) := by
  have hβ : β ≠ 0 := ne_of_gt (root_pos hroot)
  have hβm : β-1 ≠ 0 := ne_of_gt (root_sub_one_pos hroot)
  have hc := hroot.cubic_eq_zero
  dsimp [cubic] at hc
  apply (eq_div_iff hβm).2
  field_simp
  nlinarith [hc]

theorem lengths_difference {n d : ℕ} {β : ℝ} (hroot : RootData n d β) :
    lengths n β 0 - lengths n β 1 = (d : ℝ)/(β-1) := by
  calc
    lengths n β 0 - lengths n β 1 = 1-2/β-((n : ℝ)+2-β) := by
      dsimp [lengths]
      ring
    _ = (d : ℝ)/(β-1) := root_delta_identity hroot

/-- The actual lower-chamber root discharges every abstract coefficient condition. -/
theorem root_coefficient_parameters (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) :
    Parameters (2/β) ((n : ℝ)+2-β) := by
  have hn6 : (6 : ℝ) ≤ n := by exact_mod_cast lower_chamber_n n d hd hn
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hβ := root_pos hroot
  have hδ := div_pos hd0 (root_sub_one_pos hroot)
  have he := root_delta_identity hroot
  refine ⟨(div_pos (by norm_num) hβ).le, ?_, ?_, ?_⟩
  · apply (div_lt_iff₀ hβ).2
    linarith [hroot.lower]
  · linarith [hroot.upper]
  · linarith

/-- Every length is positive; non-y lengths are strictly between one and two. -/
theorem literal_lengths_bounds (n d : ℕ) (hd : 5 ≤ d) (_hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) :
    1 < lengths n β 1 ∧ lengths n β 1 < lengths n β 0 ∧
      lengths n β 0 < 2 ∧ lengths n β 2 = 1 ∧
      ∀ a, 1 ≤ lengths n β a ∧ lengths n β a < 2 := by
  have hβ := root_pos hroot
  have hinv : 0 < 1/β := div_pos (by norm_num) hβ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hδ := div_pos hd0 (root_sub_one_pos hroot)
  have he := lengths_difference hroot
  have hc : 1 < lengths n β 1 := by dsimp [lengths]; linarith
  have hcx : lengths n β 1 < lengths n β 0 := by linarith
  have hx : lengths n β 0 < 2 := by dsimp [lengths]; linarith [hroot.upper]
  refine ⟨hc, hcx, hx, rfl, ?_⟩
  intro a
  fin_cases a
  · change 1 ≤ lengths n β 0 ∧ lengths n β 0 < 2
    exact ⟨hc.le.trans hcx.le, hx⟩
  · change 1 ≤ lengths n β 1 ∧ lengths n β 1 < 2
    exact ⟨hc.le, hcx.trans hx⟩
  · norm_num [lengths]

theorem literal_lengths_pos (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) : ∀ a, 0 < lengths n β a := by
  intro a
  have hh := (literal_lengths_bounds n d hd hn β hroot).2.2.2.2 a
  linarith

/-- The lower bound used in the uniform one-level density reserve. -/
theorem literal_x_length_lower (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) :
    1+5/((n : ℝ)+1) < lengths n β 0 := by
  have hn0 : (0 : ℝ) < n+1 := by positivity
  have hd5 : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hfrac : 5/((n : ℝ)+1) < (d : ℝ)/(β-1) := by
    apply (div_lt_div_iff₀ hn0 (root_sub_one_pos hroot)).2
    nlinarith [hroot.upper, mul_nonneg (show (0 : ℝ) ≤ d-5 by linarith) hn0.le]
  have hc := (literal_lengths_bounds n d hd hn β hroot).1
  have he := lengths_difference hroot
  linarith

theorem physicalLength_replicate (ℓ : Fin 3 → ℝ) (a : Fin 3) (k : ℕ) :
    physicalLength ℓ (List.replicate k a) = (k : ℝ)*ℓ a := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, physicalLength_cons, ih, Nat.cast_add, add_mul]; ring

/-- All three equations concern the literal image words, rather than a supplied
matrix eigenvector hypothesis. -/
theorem literal_length_scaling (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) :
    ∀ a, physicalLength (lengths n β) (sigma n d a) = β*lengths n β a := by
  have hn1 : 1 ≤ n := by omega
  have hβ : β ≠ 0 := ne_of_gt (root_pos hroot)
  have hc := hroot.cubic_eq_zero
  dsimp [cubic] at hc
  intro a
  fin_cases a <;>
    simp [sigma, first, last, runLength, physicalLength_replicate, lengths,
      Nat.cast_sub hn1, Nat.cast_add]
  · field_simp
    nlinarith [hc]
  · field_simp
    ring
  · ring

/-- The displayed cubic has an actual real root in the required open bracket.
This is an algebraic existence theorem, not a spectral-radius assertion. -/
theorem root_exists (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n) :
    ∃ β : ℝ, RootData n d β := by
  have hn6 : (6 : ℝ) ≤ n := by exact_mod_cast lower_chamber_n n d hd hn
  have hd5 : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hnd : (d : ℝ)+1 ≤ n := by exact_mod_cast hn
  have hlo : cubic n d ((n : ℝ)+1) = -((d : ℝ)+2)*((n : ℝ)+1)+2 := by
    dsimp [cubic]
    ring
  have hhi : cubic n d ((n : ℝ)+2) = ((n : ℝ)-(d : ℝ)-1)*((n : ℝ)+2)+2 := by
    dsimp [cubic]
    ring
  have hloneg : cubic n d ((n : ℝ)+1) < 0 := by
    rw [hlo]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ d-5 by linarith)
      (show (0 : ℝ) ≤ n+1 by linarith)]
  have hhipos : 0 < cubic n d ((n : ℝ)+2) := by
    rw [hhi]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ n-d-1 by linarith)
      (show (0 : ℝ) ≤ n+2 by linarith)]
  have hcont : Continuous (cubic n d) := by unfold cubic; fun_prop
  obtain ⟨β, hβ, hc⟩ := intermediate_value_Ioo
    (show (n : ℝ)+1 ≤ (n : ℝ)+2 by linarith) hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (cubic n d ((n : ℝ)+1))
      (cubic n d ((n : ℝ)+2)) from ⟨hloneg, hhipos⟩)
  exact ⟨β, hc, hβ.1, hβ.2⟩

/-- A constant nearest tail automatically lies in the exact integral range
required by the three original RUN decrements. No height bound is assumed. -/
theorem constant_amplitude_run_bound (n d : ℕ) (hd : 5 ≤ d) (_hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (H : ℤ)
    (hamp : |(1-2/β-((n : ℝ)+2-β))*(H : ℝ)| < 1/2) :
    2*(d : ℤ)*|H| ≤ (n : ℤ) := by
  have hβm := root_sub_one_pos hroot
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hδ := div_pos hd0 hβm
  rw [root_delta_identity hroot, abs_mul, abs_of_pos hδ] at hamp
  have hfrac : (d : ℝ)*|(H : ℝ)|/(β-1) < 1/2 := by
    simpa only [div_mul_eq_mul_div] using hamp
  have hmul := (div_lt_iff₀ hβm).1 hfrac
  have hreal : 2*(d : ℝ)*|(H : ℝ)| < (n : ℝ)+1 := by
    nlinarith [hroot.upper]
  have hint : 2*(d : ℤ)*|H| < (n : ℤ)+1 := by exact_mod_cast hreal
  omega

/-- Specialization of the proved abstract recurrence to the literal family.
The actual occurrence recurrence remains an explicit premise. -/
theorem literal_eventual_constant_tail (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (u : ℕ → ℤ)
    (hrec : ∀ j, |(u (j+2) : ℝ)-((2/β)*(u j : ℝ)+
      ((n : ℝ)+2-β)*(u (j+1) : ℝ))| < 1/2) :
    ∃ N : ℕ, ∃ H : ℤ, 2*(d : ℤ)*|H| ≤ (n : ℤ) ∧ ∀ m, u (N+m) = H := by
  have hp := root_coefficient_parameters n d hd hn β hroot
  obtain ⟨N, H, hamp, htail⟩ := eventual_constant_tail (2/β) ((n : ℝ)+2-β)
    hp.anonneg hp.asmall hp.bpos hp.contraction u hrec
  exact ⟨N, H, constant_amplitude_run_bound n d hd hn β hroot H hamp, htail⟩

/-- The constant full packet's actual composable path now requires only its
arithmetic amplitude condition and the literal cubic-root interface. -/
theorem literal_constant_composable_path (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (H : ℤ)
    (hamp : |(1-2/β-((n : ℝ)+2-β))*(H : ℝ)| < 1/2) :
    (packet 2 2 H (-H) 0).Interior (lengths n β) ∧
      Relation.ReflTransGen (InteriorStep (sigma n d) (lengths n β))
        (packet 2 2 H (-H) 0) (packet 2 2 0 0 0) :=
  constant_composable_path n d hd H
    (constant_amplitude_run_bound n d hd hn β hroot H hamp)
    (lengths n β) β (literal_lengths_pos n d hd hn β hroot)
    (root_pos hroot) (literal_length_scaling n d hd hn β hroot)

end Psc.ClassAMinusLiteralArithmetic
