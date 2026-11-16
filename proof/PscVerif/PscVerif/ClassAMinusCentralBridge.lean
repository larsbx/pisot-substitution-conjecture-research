/-
# Actual central RUN selectors and the literal scalar recurrence

The root and coefficient algebra is supplied by the literal arithmetic module.
The half-unit exclusion is proved by the literal cubic irreducibility module.
Every step retains the complete integral packet and the original two RUN
positions. No all-source central-entry premise is hidden.

Pre-code scope: `docs/bh-class-a-literal-lean-stop-go-2026-11-14.md`.
-/
import PscVerif.ClassAMinusLiteralArithmetic
import PscVerif.ClassAMinusNoHalfUnit
import PscVerif.ClassAMinusPrefixAssembly
import Mathlib.Algebra.Order.Floor.Ring

namespace Psc.ClassAMinusCentralBridge

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn Psc.OccurrenceTransport
open Psc.ClassAZeroDefectEscape Psc.ClassAMinusLiteralArithmetic Matrix

@[ext] structure IntegralState where
  p : ℤ
  q : ℤ
  r : ℤ
  deriving DecidableEq

def IntegralState.toPacket (s : IntegralState) : Packet := packet 2 2 s.p s.q s.r

noncomputable def shift (n : ℕ) (β : ℝ) (s : IntegralState) : ℝ :=
  (β-(n : ℝ)-1/β)*(s.p : ℝ)+(1+1/β)*(s.q : ℝ)+(s.r : ℝ)

/-- This is the exact arithmetic interface for excluding half-unit ties. -/
def NoHalfUnit (n : ℕ) (β : ℝ) : Prop :=
  ∀ s : IntegralState, |shift n β s| ≠ 1/2

def advance (n d : ℕ) (g : ℤ) (s : IntegralState) : IntegralState :=
  ⟨2*s.p+s.q+s.r, s.q+s.r,
    ((n+d : ℕ) : ℤ)*s.p+(n : ℤ)*s.q+((n-1 : ℕ) : ℤ)*s.r+g⟩

/-- The gap is bottom RUN ordinal minus top RUN ordinal. -/
noncomputable def nearestGap (n : ℕ) (β : ℝ) (s : IntegralState) : ℤ :=
  -Int.floor (β*shift n β s+1/2)

theorem advance_physical (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (g : ℤ) (s : IntegralState) :
    shift n β (advance n d g s) = β*shift n β s+(g : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hβ : β ≠ 0 := ne_of_gt (root_pos hroot)
  have hc := hroot.cubic_eq_zero
  dsimp [cubic] at hc
  dsimp [shift, advance]
  push_cast [Nat.cast_sub hn1]
  field_simp
  nlinarith [mul_eq_zero_of_left hc (s.p : ℝ)]

theorem nearestGap_error (n : ℕ) (β : ℝ) (s : IntegralState) :
    |β*shift n β s+(nearestGap n β s : ℝ)| ≤ 1/2 := by
  have hlo := Int.floor_le (β*shift n β s+1/2)
  have hhi := Int.lt_floor_add_one (β*shift n β s+1/2)
  dsimp [nearestGap]
  rw [Int.cast_neg]
  apply abs_le.mpr
  constructor <;> linarith

theorem advance_central (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (hhalf : NoHalfUnit n β)
    (s : IntegralState) :
    |shift n β (advance n d (nearestGap n β s) s)| < 1/2 := by
  apply lt_of_le_of_ne
  · rw [advance_physical n d hd hn β hroot]
    exact nearestGap_error n β s
  · exact hhalf _

/-- The deterministic central selector is a genuine pair of original RUN
occurrences, with all coordinates fixed by the literal incidence action. -/
theorem central_indexed_step (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (hhalf : NoHalfUnit n β)
    (s : IntegralState) (hs : |shift n β s| < 1/2) :
    IndexedDigitStep (sigma n d) s.toPacket
      ((-nearestGap n β s).toNat+1) ((nearestGap n β s).toNat+1)
      (advance n d (nearestGap n β s) s).toPacket := by
  have ht := advance_central n d hd hn β hroot hhalf s
  rw [advance_physical n d hd hn β hroot] at ht
  obtain ⟨hlo, hhi⟩ := ClassACentralRecurrence.central_gap_in_run n
    (lower_chamber_n n d hd hn) β (shift n β s) (root_pos hroot)
    (by linarith [hroot.upper]) hs (nearestGap n β s) ht
  exact ClassACentralRecurrence.run_gap_digit_step n d (by omega)
    s.p s.q s.r (nearestGap n β s) hlo hhi

noncomputable def orbit (n d : ℕ) (β : ℝ) (s : IntegralState) : ℕ → IntegralState
  | 0 => s
  | k+1 => advance n d (nearestGap n β (orbit n d β s k)) (orbit n d β s k)

theorem orbit_central (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (hhalf : NoHalfUnit n β)
    (s : IntegralState) (hs : |shift n β s| < 1/2) :
    ∀ k, |shift n β (orbit n d β s k)| < 1/2 := by
  intro k
  cases k with
  | zero => exact hs
  | succ k => exact advance_central n d hd hn β hroot hhalf _

theorem orbit_digit_path (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (hhalf : NoHalfUnit n β)
    (s : IntegralState) (hs : |shift n β s| < 1/2) (k : ℕ) :
    Relation.ReflTransGen (DigitStep (sigma n d)) s.toPacket
      (orbit n d β s k).toPacket := by
  induction k with
  | zero => exact .refl
  | succ k ih =>
    exact ih.tail (central_indexed_step n d hd hn β hroot hhalf _
      (orbit_central n d hd hn β hroot hhalf s hs k)).digitStep

/-- The full child displacement is exactly the scalar recurrence error.
This algebraic identity does not discard the second or third coordinate. -/
theorem advance_recurrence_identity (n d : ℕ) (β : ℝ) (g : ℤ) (s : IntegralState) :
    shift n β (advance n d g s) =
      ((2*(advance n d g s).p+(advance n d g s).q+(advance n d g s).r : ℤ) : ℝ) -
        (2/β*(s.p : ℝ)+((n : ℝ)+2-β)*((advance n d g s).p : ℝ)) := by
  dsimp [shift, advance]
  push_cast
  ring

/-- The existing abstract theorem now receives its recurrence from the
actual original-index selector, rather than from a caller-supplied sequence. -/
theorem orbit_recurrence (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (hhalf : NoHalfUnit n β)
    (s : IntegralState) :
    ∀ k, ClassAMinusConstantRecurrence.Nearest (2/β) ((n : ℝ)+2-β)
      (orbit n d β s k).p (orbit n d β s (k+1)).p (orbit n d β s (k+2)).p := by
  intro k
  have ht := advance_central n d hd hn β hroot hhalf (orbit n d β s k)
  rw [advance_recurrence_identity] at ht
  exact ht

theorem orbit_second (n d : ℕ) (β : ℝ) (s : IntegralState) (k : ℕ) :
    (orbit n d β s (k+1)).q = (orbit n d β s (k+1)).p-2*(orbit n d β s k).p := by
  simp only [orbit, advance]
  ring

/-- Eventual constancy of first coordinates determines the complete
literal packet U_H=(y,y,H,-H,0), with the admissible RUN height proved. -/
theorem orbit_reaches_constant (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (hhalf : NoHalfUnit n β)
    (s : IntegralState) :
    ∃ N : ℕ, ∃ H : ℤ, 2*(d : ℤ)*|H| ≤ (n : ℤ) ∧
      orbit n d β s (N+1) = ⟨H,-H,0⟩ := by
  have hp := root_coefficient_parameters n d hd hn β hroot
  obtain ⟨N, H, hamp, hconst⟩ := ClassAMinusConstantRecurrence.eventual_constant_tail
    (2/β) ((n : ℝ)+2-β) hp.anonneg hp.asmall hp.bpos hp.contraction
    (fun k => (orbit n d β s k).p) (orbit_recurrence n d hd hn β hroot hhalf s)
  refine ⟨N, H, ?_, ?_⟩
  · exact constant_amplitude_run_bound n d hd hn β hroot H hamp
  · have h0 := hconst 0
    have h1 := hconst 1
    have h2 := hconst 2
    simp only [Nat.add_zero] at h0
    have hq := orbit_second n d β s N
    have hr : (orbit n d β s (N+2)).p =
        2*(orbit n d β s (N+1)).p+(orbit n d β s (N+1)).q+
          (orbit n d β s (N+1)).r := rfl
    apply IntegralState.ext <;> simp only <;> omega

/-- Central sources escape through actual occurrence paths. The sole
remaining algebraic adapter premise is explicitly named NoHalfUnit. -/
theorem central_digit_path (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (hhalf : NoHalfUnit n β)
    (s : IntegralState) (hs : |shift n β s| < 1/2) :
    Relation.ReflTransGen (DigitStep (sigma n d)) s.toPacket (packet 2 2 0 0 0) := by
  obtain ⟨N,H,hH,heq⟩ := orbit_reaches_constant n d hd hn β hroot hhalf s
  have hp := orbit_digit_path n d hd hn β hroot hhalf s hs (N+1)
  rw [heq] at hp
  exact hp.trans (ClassAMinusConstantRecurrence.constant_digit_path n d hd H hH)

theorem central_composable_path (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (hhalf : NoHalfUnit n β)
    (s : IntegralState) (hs : |shift n β s| < 1/2) :
    s.toPacket.Interior (lengths n β) ∧
      Relation.ReflTransGen (InteriorStep (sigma n d) (lengths n β))
        s.toPacket (packet 2 2 0 0 0) :=
  ClassAMinusConstantRecurrence.digit_path_interior (sigma n d) (lengths n β) β
    (literal_lengths_pos n d hd hn β hroot) (root_pos hroot)
    (literal_length_scaling n d hd hn β hroot)
    (central_digit_path n d hd hn β hroot hhalf s hs)
    (zero_packet_interior (lengths n β) (literal_lengths_pos n d hd hn β hroot) 2 2)

/-- The algebraic no-tie interface is discharged for every integral state. -/
theorem literal_no_half_unit (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) : NoHalfUnit n β := by
  intro s
  exact ClassAMinusNoHalfUnit.physical_abs_ne_half n d hd hn β hroot s.p s.q s.r

/-- Every literal central integral source reaches typed coincidence. No
recurrence, finite carrier, periodicity, or no-tie hypothesis is supplied. -/
theorem literal_central_composable_path (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (p q r : ℤ)
    (hs : |(β-(n : ℝ)-1/β)*(p : ℝ)+(1+1/β)*(q : ℝ)+(r : ℝ)| ≤ 1/2) :
    (packet 2 2 p q r).Interior (lengths n β) ∧
      Relation.ReflTransGen (InteriorStep (sigma n d) (lengths n β))
        (packet 2 2 p q r) (packet 2 2 0 0 0) := by
  have hh := literal_no_half_unit n d hd hn β hroot
  exact central_composable_path n d hd hn β hroot hh ⟨p,q,r⟩
    (lt_of_le_of_ne hs (hh ⟨p,q,r⟩))

open ClassAMinusPrefixAssembly

/-- The literal central theorem retains original ordered occurrences and
the complete source identity M^m w=P-Q. Both terminal marks are y. -/
theorem literal_central_original_prefixes (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (p q r : ℤ)
    (hs : |(β-(n : ℝ)-1/β)*(p : ℝ)+(1+1/β)*(q : ℝ)+(r : ℝ)| ≤ 1/2) :
    ∃ xs, OrderedPath (sigma n d) (packet 2 2 p q r) xs (packet 2 2 0 0 0) ∧
      (packet 2 2 p q r).Interior (lengths n β) ∧
      Relation.ReflTransGen (InteriorStep (sigma n d) (lengths n β))
        (packet 2 2 p q r) (packet 2 2 0 0 0) ∧
      ∃ (top : Mark ((subst (sigma n d))^[xs.length] [2]))
        (bottom : Mark ((subst (sigma n d))^[xs.length] [2])),
        top.letter = 2 ∧ bottom.letter = 2 ∧
        incidenceZ (sigma n d)^xs.length *ᵥ ![p,q,r] =
          parikhZ top.before-parikhZ bottom.before := by
  have hh := literal_no_half_unit n d hd hn β hroot
  have hp := central_digit_path n d hd hn β hroot hh ⟨p,q,r⟩
    (lt_of_le_of_ne hs (hh ⟨p,q,r⟩))
  obtain ⟨xs,hxs⟩ := digit_path_has_ordered_path hp
  obtain ⟨hi,hip⟩ := ordered_path_interior (sigma n d) (lengths n β) β
    (literal_lengths_pos n d hd hn β hroot) (root_pos hroot)
    (literal_length_scaling n d hd hn β hroot) hxs
    (zero_packet_interior (lengths n β) (literal_lengths_pos n d hd hn β hroot) 2 2)
  have hz : (packet 2 2 0 0 0).delta = 0 := by
    funext a
    fin_cases a <;> rfl
  obtain ⟨top,bottom,ht,hb,he⟩ := ordered_path_zero_original_prefixes hxs hz
  refine ⟨xs,hxs,hi,hip,top,bottom,ht,hb,?_⟩
  have hsign : -(packet 2 2 p q r).delta = ![p,q,r] := by
    funext a
    fin_cases a <;> simp [packet]
  simpa only [IntegralState.toPacket, hsign] using he

/-- A future all-source density proof need only produce an actual central
descendant. Its supplied ordered path is concatenated at the identical full
packet and the prefix identity remains based at the original source. -/
theorem source_with_central_descendant (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (source : Packet) (p q r : ℤ)
    (entry : List (ℕ × ℕ))
    (hentry : OrderedPath (sigma n d) source entry (packet 2 2 p q r))
    (hs : |(β-(n : ℝ)-1/β)*(p : ℝ)+(1+1/β)*(q : ℝ)+(r : ℝ)| ≤ 1/2) :
    ∃ tail, OrderedPath (sigma n d) source (entry++tail) (packet 2 2 0 0 0) ∧
      source.Interior (lengths n β) ∧
      Relation.ReflTransGen (InteriorStep (sigma n d) (lengths n β))
        source (packet 2 2 0 0 0) ∧
      ∃ (top : Mark ((subst (sigma n d))^[(entry++tail).length] [source.top]))
        (bottom : Mark ((subst (sigma n d))^[(entry++tail).length] [source.bottom])),
        top.letter = 2 ∧ bottom.letter = 2 ∧
        incidenceZ (sigma n d)^(entry++tail).length *ᵥ (-source.delta) =
          parikhZ top.before-parikhZ bottom.before := by
  obtain ⟨tail,htail,_⟩ := literal_central_original_prefixes n d hd hn β hroot p q r hs
  have hp := hentry.trans htail
  have hz : (packet 2 2 0 0 0).delta = 0 := by
    funext a
    fin_cases a <;> rfl
  obtain ⟨hi,hip⟩ := ordered_path_interior (sigma n d) (lengths n β) β
    (literal_lengths_pos n d hd hn β hroot) (root_pos hroot)
    (literal_length_scaling n d hd hn β hroot) hp
    (zero_packet_interior (lengths n β) (literal_lengths_pos n d hd hn β hroot) 2 2)
  exact ⟨tail,hp,hi,hip,ordered_path_zero_original_prefixes hp hz⟩

/-- The central source theorem with a single strictly interior ordered path
and both nested prefix marks explicitly bound to every ordinal in that path. -/
theorem literal_central_traced_prefixes (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (p q r : ℤ)
    (hs : |(β-(n : ℝ)-1/β)*(p : ℝ)+(1+1/β)*(q : ℝ)+(r : ℝ)| ≤ 1/2) :
    ∃ xs, OrderedInteriorPath (sigma n d) (lengths n β)
        (packet 2 2 p q r) xs (packet 2 2 0 0 0) ∧
      ∃ (top : Mark ((subst (sigma n d))^[xs.length] [2]))
        (bottom : Mark ((subst (sigma n d))^[xs.length] [2])),
        MarkTrace (sigma n d) 2 (xs.map Prod.fst) top.before top.letter top.after ∧
        MarkTrace (sigma n d) 2 (xs.map Prod.snd) bottom.before bottom.letter bottom.after ∧
        top.letter = 2 ∧ bottom.letter = 2 ∧
        incidenceZ (sigma n d)^xs.length *ᵥ ![p,q,r] =
          parikhZ top.before-parikhZ bottom.before := by
  obtain ⟨xs,hxs,_⟩ := literal_central_original_prefixes n d hd hn β hroot p q r hs
  have hi := ordered_path_indexed_interior (sigma n d) (lengths n β) β
    (literal_lengths_pos n d hd hn β hroot) (root_pos hroot)
    (literal_length_scaling n d hd hn β hroot) hxs
    (zero_packet_interior (lengths n β) (literal_lengths_pos n d hd hn β hroot) 2 2)
  have hz : (packet 2 2 0 0 0).delta = 0 := by
    funext a
    fin_cases a <;> rfl
  obtain ⟨top,bottom,htt,hbt,ht,hb,he⟩ := ordered_path_traced_zero_original_prefixes hxs hz
  refine ⟨xs,hi,top,bottom,htt,hbt,ht,hb,?_⟩
  have hsign : -(packet 2 2 p q r).delta = ![p,q,r] := by
    funext a
    fin_cases a <;> simp [packet]
  simpa only [hsign] using he

/-- An actual central-entry transcript is retained unchanged, followed by
the central escape transcript. The same ordered interior path witnesses both
original prefix traces and the complete original source identity. -/
theorem source_with_traced_central_descendant (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (source : Packet) (p q r : ℤ)
    (entry : List (ℕ × ℕ))
    (hentry : OrderedPath (sigma n d) source entry (packet 2 2 p q r))
    (hs : |(β-(n : ℝ)-1/β)*(p : ℝ)+(1+1/β)*(q : ℝ)+(r : ℝ)| ≤ 1/2) :
    ∃ tail, OrderedInteriorPath (sigma n d) (lengths n β)
        source (entry++tail) (packet 2 2 0 0 0) ∧
      ∃ (top : Mark ((subst (sigma n d))^[(entry++tail).length] [source.top]))
        (bottom : Mark ((subst (sigma n d))^[(entry++tail).length] [source.bottom])),
        MarkTrace (sigma n d) source.top ((entry++tail).map Prod.fst)
          top.before top.letter top.after ∧
        MarkTrace (sigma n d) source.bottom ((entry++tail).map Prod.snd)
          bottom.before bottom.letter bottom.after ∧
        top.letter = 2 ∧ bottom.letter = 2 ∧
        incidenceZ (sigma n d)^(entry++tail).length *ᵥ (-source.delta) =
          parikhZ top.before-parikhZ bottom.before := by
  obtain ⟨tail,htail,_⟩ := literal_central_original_prefixes n d hd hn β hroot p q r hs
  have hp := hentry.trans htail
  have hi := ordered_path_indexed_interior (sigma n d) (lengths n β) β
    (literal_lengths_pos n d hd hn β hroot) (root_pos hroot)
    (literal_length_scaling n d hd hn β hroot) hp
    (zero_packet_interior (lengths n β) (literal_lengths_pos n d hd hn β hroot) 2 2)
  have hz : (packet 2 2 0 0 0).delta = 0 := by
    funext a
    fin_cases a <;> rfl
  exact ⟨tail,hi,ordered_path_traced_zero_original_prefixes hp hz⟩

/-- Invalid lower-chamber parameters do not enter the formal interface. -/
theorem invalid_parameters_control :
    ¬ (5 ≤ (4:ℕ) ∧ 4+1 ≤ (6:ℕ)) ∧
    ¬ (5 ≤ (5:ℕ) ∧ 5+1 ≤ (5:ℕ)) ∧
    ¬ (5 ≤ (7:ℕ) ∧ 7+1 ≤ (6:ℕ)) := by omega

end Psc.ClassAMinusCentralBridge
