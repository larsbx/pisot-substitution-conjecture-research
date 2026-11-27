/-
# Full-packet controls for upper central completion

For every upper J=1 member, the central source (1,2,-5) has transformed
initial scalar pair (1,1), but it is not any full W packet. The actual
original RUN pair (1,1) reaches -W_1. This preserves the necessary one-step
reconstruction delay and the complete integral coordinates.

The existing nonzero-cycle and strict-half-tie controls remain explicit.
This specializes the reviewed central-source contract without assuming
that the selected nearest recurrence itself reaches zero.
-/
import PscVerif.ClassAPlusUpperLiteralEntry

namespace Psc.ClassAPlusUpperCentralControls

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn
open Psc.OccurrenceTransport Psc.ClassAZeroDefectEscape
open Psc.ClassAMinusPrefixAssembly Psc.ClassAPlusUpperCycles
open Psc.ClassAPlusUpperRecurrence Psc.ClassAPlusUpperLiteralEntry Matrix

def source : Packet := packet 2 2 1 2 (-5)
def target : Packet := packet 2 2 (-1) (-3) 6

/-- The physical source shift uses all three integral coordinates. -/
theorem source_shift (n : ℕ) (β : ℝ) :
    shift n β source = 1/β - V n β := by
  simp [shift, source, packet, offset, dotProduct, Fin.sum_univ_three,
    xLength, cLength, V, A, C]
  ring

theorem target_shift (n : ℕ) (β : ℝ) :
    shift n β target = V n β := by
  simp [shift, target, packet, offset, dotProduct, Fin.sum_univ_three,
    xLength, cLength, V, A, C]
  ring

/-- On J=1, 1/beta-1/(beta+1) is strictly positive and below one half. -/
theorem source_central {n : ℕ} {β : ℝ} (hp : Family n 1 β) :
    Central n β source := by
  have hV : V n β = 1/(β+1) := by simpa using hp.reserve_identity
  have hb1 : 0 < β+1 := by linarith [hp.beta_pos]
  have hless : 1/(β+1) < 1/β :=
    (div_lt_div_iff_of_pos_left (by norm_num) hb1 hp.beta_pos).2 (by linarith)
  have hlo : 0 < 1/β-V n β := by rw [hV]; linarith
  have hhalf : 1/β < 1/2 :=
    (div_lt_div_iff_of_pos_left (by norm_num) hp.beta_pos (by norm_num)).2
      (by linarith [hp.beta_gt_eleven])
  refine ⟨rfl, rfl, ?_⟩
  rw [source_shift, abs_of_pos hlo]
  linarith [hp.V_pos]

theorem target_central {n : ℕ} {β : ℝ} (hp : Family n 1 β) :
    Central n β target := by
  refine ⟨rfl, rfl, ?_⟩
  rw [target_shift, abs_of_pos hp.V_pos, hp.reserve_identity]
  norm_num only [Nat.cast_one]
  exact (div_lt_div_iff_of_pos_left (by norm_num)
    (by linarith [hp.beta_pos]) (by norm_num)).2
      (by linarith [hp.beta_gt_eleven])

/-- The two original RUN occurrences retain the exact full target packet. -/
theorem actual_first_edge (n : ℕ) :
    IndexedDigitStep (upperSigma n 1) source 1 1 target := by
  have he := run_gap_digit_step n (2*n+11) 1 2 (-5) 0 (by omega) (by omega)
  have hd : 2*n+12-1 = 2*n+11 := by omega
  convert he using 1 <;>
    simp [source, target, upperSigma, hd, Nat.cast_add, Nat.cast_mul]
  congr 1
  ring

theorem target_signed_cycle : target = signedSource true 1 := by
  symm
  simpa [signedSource, cyclePacket, target] using
    ClassAMinusConstantRecurrence.packet_swap 2 2 1 3 (-6)

/-- The scalar pair agrees with a constant transformed tail already at zero. -/
theorem original_scalar_pair :
    (-source.delta 0, -(2*source.delta 0+source.delta 1+source.delta 2)) =
      (1, -1) := by
  norm_num [source, packet]

theorem transformed_scalar_pair :
    (-source.delta 0, 2*source.delta 0+source.delta 1+source.delta 2) =
      (1, 1) := by
  norm_num [source, packet]

/-- Neither sign nor any height can turn the original source into a W packet. -/
theorem source_not_full_cycle (H : ℤ) :
    source ≠ packet 2 2 H (3*H) (-6*H) := by
  intro he
  have hx := congrArg (fun p : Packet => p.delta 0) he
  have hq := congrArg (fun p : Packet => p.delta 1) he
  norm_num [source, packet] at hx hq
  omega

theorem source_ne_cycle_one : source ≠ cyclePacket 1 := by
  simpa [cyclePacket] using source_not_full_cycle 1

/-- A genuinely strict one-edge prefix, not an orientation operation. -/
theorem strict_reconstruction_prefix {n : ℕ} {β : ℝ} (hp : Family n 1 β) :
    OrderedInteriorPath (upperSigma n 1) (lengths n β) source [(1,1)]
      (signedSource true 1) := by
  rw [← target_signed_cycle]
  exact .snoc (.nil source (central_interior hp (source_central hp))) 1 1
    (actual_first_edge n) (central_interior hp (target_central hp))

/-- Combined unbounded-family control for the one-step reconstruction delay. -/
theorem reconstruction_delay_control {n : ℕ} {β : ℝ} (hp : Family n 1 β) :
    Central n β source ∧ source ≠ cyclePacket 1 ∧
      (-source.delta 0, 2*source.delta 0+source.delta 1+source.delta 2) = (1,1) ∧
      IndexedDigitStep (upperSigma n 1) source 1 1 (signedSource true 1) ∧
      Central n β (signedSource true 1) := by
  refine ⟨source_central hp, source_ne_cycle_one, transformed_scalar_pair, ?_, ?_⟩
  · rw [← target_signed_cycle]
    exact actual_first_edge n
  · rw [← target_signed_cycle]
    exact target_central hp

theorem retained_nonzero_cycle_control :
    (1 : ℝ) < 1/8+1 ∧
      ClassAPlusConstantRecurrence.Nearest (1/8) 1 1 1 1 ∧
      OriginalNearest (1/8) 1 1 (-1) 1 ∧ (1 : ℤ) ≠ 0 :=
  ClassAPlusUpperRecurrence.nonzero_upper_cycle_control

theorem retained_half_tie_control :
    ¬ClassAPlusConstantRecurrence.Nearest (1/8) 1 4 0 0 :=
  ClassAPlusUpperRecurrence.half_tie_control

end Psc.ClassAPlusUpperCentralControls
