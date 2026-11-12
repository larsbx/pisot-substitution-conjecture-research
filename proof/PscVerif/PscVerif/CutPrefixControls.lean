import PscVerif.NamedPrefixCompact
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Boundaries of literal cut-prefix approximation

These controls retain actual named fixed words, signed prefix differences,
and genuine inverse-limit residue coordinates.  The scalar doubling carrier
is an elementary non-Pisot calibration of the residue interface, not a new
PSC specimen.  The last controls keep the source correction fixed in the
convergence contract: a shrinking coefficient alone is insufficient.

Pre-code gate: `docs/c4-cut-prefix-embedding-literature-2026-11-12.md`.
-/

namespace Psc.CutPrefixControls

open Psc.OccurrenceTransport Psc.OccurrenceInverse Psc.PrefixAddress Psc.NamedPrefixCompact
open Psc.NamedStableChart

/-- The literal source words remain different despite identical incidence. -/
theorem same_incidence_different_words :
    incidenceZ (substitution 0) = incidenceZ (substitution 1) ∧ word 0 ≠ word 1 :=
  ⟨(incidence_eq 0).trans (incidence_eq 1).symm, words_distinct⟩

/-- Position one is a real occurrence in each authenticated infinite word,
but selects different letters.  An incidence identity cannot transport it. -/
theorem reference_occurrence_not_interchangeable : word 0 1 = 2 ∧ word 1 1 = 1 :=
  ⟨word_initial 0 1, word_initial 1 1⟩

/-- The available fixed-word period cannot be silently changed to one. -/
theorem actual_period_two_not_one (f : Fin 2) :
    FixedPrefix (iterateImages (substitution f) 2) (word f) ∧
      ¬ FixedPrefix (substitution f) (word f) :=
  ⟨word_fixed_two f, word_not_fixed_one f⟩

theorem actual_reference_prefix : wordPrefix (word 0) 2 = [0, 2] := by
  rw [prefix_succ (word 0) 1, prefix_succ (word 0) 0, prefix_zero, word_zero]
  rw [show word 0 1 = 2 from word_initial 0 1]
  rfl

/-- The source word `[1]` and the actual reference at index two both select
letter one.  Their preceding Parikh columns differ by `(-1,0,-1)`. -/
theorem literal_nonzero_correction :
    word 0 2 = (1 : Fin 3) ∧
      parikhZ ([] : Word) - parikhZ (wordPrefix (word 0) 2) = ![-1, 0, -1] := by
  refine ⟨word_initial 0 2, ?_⟩
  rw [actual_reference_prefix]
  funext i
  fin_cases i <;> decide

/-- The signed correction remains nonzero in the actual stable chart. -/
theorem literal_correction_projection :
    piZ (parikhZ ([] : Word) - parikhZ (wordPrefix (word 0) 2)) = ![-1, -1] := by
  rw [literal_nonzero_correction.2, piZ_apply, W_mulVec]
  ext i
  fin_cases i <;> norm_num [castZ]

/-- Reversing source-minus-reference changes the real prefix discrepancy. -/
theorem wrong_correction_sign :
    piZ (parikhZ ([] : Word) - parikhZ (wordPrefix (word 0) 2)) ≠
      piZ (parikhZ (wordPrefix (word 0) 2) - parikhZ ([] : Word)) := by
  intro h
  have hn : piZ (parikhZ (wordPrefix (word 0) 2) - parikhZ ([] : Word)) =
      -piZ (parikhZ ([] : Word) - parikhZ (wordPrefix (word 0) 2)) := by
    rw [← map_neg, neg_sub]
  rw [hn, literal_correction_projection] at h
  have hc := congrFun h 0
  norm_num at hc

/-! ## Actual quotient and inverse-limit controls -/

/-- Multiplication by two on the integral lattice, with its genuine
quotients and coherent inverse limit supplied by `MadicResidue`. -/
def doubling : ℤ →ₗ[ℤ] ℤ where
  toFun z := 2 * z
  map_add' x y := by ring
  map_smul' a z := by simp only [smul_eq_mul, RingHom.id_apply]; ring

theorem doubling_pow_apply (q : ℕ) (z : ℤ) : (doubling ^ q) z = 2 ^ q * z := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ']
    change 2 * (2 ^ q * z) = 2 * 2 ^ q * z
    ring

theorem same_finite_residue (q : ℕ) :
    MadicResidue.quotient doubling q (2 ^ q) = 0 := by
  apply (MadicResidue.quotient_eq_zero_iff doubling q _).mpr
  exact ⟨1, by rw [doubling_pow_apply, mul_one]⟩

/-- Agreement through the declared level does not extend one level deeper. -/
theorem different_next_residue (q : ℕ) :
    MadicResidue.quotient doubling (q + 1) (2 ^ q) ≠ 0 := by
  intro h
  obtain ⟨z, hz⟩ := (MadicResidue.quotient_eq_zero_iff doubling (q + 1) _).mp h
  rw [doubling_pow_apply, pow_succ] at hz
  have he : (2 : ℤ) ^ q * (2 * z) = (2 : ℤ) ^ q * 1 := by
    simpa only [mul_assoc, mul_one] using hz
  have hc := mul_left_cancel₀ (pow_ne_zero q (by norm_num : (2 : ℤ) ≠ 0)) he
  omega

theorem agreement_through_level (k q : ℕ) (hq : q ≤ k) :
    MadicResidue.eval doubling q (MadicResidue.star doubling (2 ^ k)) =
      MadicResidue.eval doubling q 0 := by
  have hk : MadicResidue.eval doubling k (MadicResidue.star doubling (2 ^ k)) = 0 :=
    same_finite_residue k
  have hr := congrArg (MadicResidue.reduction doubling hq) hk
  simpa only [MadicResidue.reduction_eval, map_zero] using hr

/-- Both witnesses are actual coherent points, not unrelated finite labels. -/
theorem finite_agreement_not_limit_equality (k : ℕ) :
    ∃ x y : MadicResidue.Carrier doubling,
      (∀ q ≤ k, MadicResidue.eval doubling q x = MadicResidue.eval doubling q y) ∧
      MadicResidue.eval doubling (k + 1) x ≠ MadicResidue.eval doubling (k + 1) y ∧
      x ≠ y := by
  refine ⟨MadicResidue.star doubling (2 ^ k), 0, agreement_through_level k, ?_, ?_⟩
  · simpa only [MadicResidue.eval_star, map_zero] using different_next_residue k
  · intro h
    have he := congrArg (MadicResidue.eval doubling (k + 1)) h
    exact different_next_residue k (by simpa only [MadicResidue.eval_star, map_zero] using he)

/-! ## A fixed correction bound is essential -/

open Filter Topology

/-- The same numerical contraction rate used by the named estimate tends
to zero.  This does not bound corrections chosen anew at each depth. -/
theorem shrinking_factor : Tendsto (fun n : ℕ => (7 / 8 : ℝ) ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem growing_correction_constant_error (n : ℕ) :
    (7 / 8 : ℝ) ^ n * (8 / 7 : ℝ) ^ n = 1 := by
  rw [← mul_pow]
  norm_num

/-- Depth-dependent source corrections can cancel every contraction step.
The finite fixed-source correction set in the positive theorem prevents this. -/
theorem growing_corrections_do_not_converge :
    ¬ Tendsto (fun n : ℕ => (7 / 8 : ℝ) ^ n * (8 / 7 : ℝ) ^ n) atTop (𝓝 0) := by
  intro h
  have hsame : Tendsto (fun n : ℕ => (7 / 8 : ℝ) ^ n * (8 / 7 : ℝ) ^ n) atTop
      (𝓝 (1 : ℝ)) := by
    simpa only [growing_correction_constant_error] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  exact one_ne_zero (tendsto_nhds_unique hsame h)

end Psc.CutPrefixControls
