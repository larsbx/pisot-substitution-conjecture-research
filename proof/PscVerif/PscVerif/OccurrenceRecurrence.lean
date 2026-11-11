/-
# Finite recurrent obstructions from actual strict carriers

The actual finite marked carrier, exact positive length scaling and the
literal digit lift produce a finite closed interior graph with a successor
at every vertex.  Every interior marked member of the supplied carrier
reaches a nonempty closed walk of compatible actual marked children.
No packet-label splice, shared legal
limit or productive-route existence is assumed or concluded.

This is a necessary structure of a supplied strict carrier, not a C4
contradiction.  The pre-code review and controls are recorded in
`docs/c4-finite-carrier-dual-literature-2026-11-10.md`.
-/
import PscVerif.OccurrenceFinite
import PscVerif.OccurrenceSuccessor
import PscVerif.OccurrenceStrict
import Mathlib.Data.Fintype.Pigeonhole

namespace Psc.OccurrenceRecurrence

open Psc.Binomial Psc.Reduction Psc.Descendants Psc.OccurrenceNewborn
open Psc.OccurrenceTransport Psc.OccurrenceFinite Psc.OccurrenceSuccessor

/-- A single actual lifted edge, with its complete target mark retained. -/
def ActualStep (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (m n : MarkedPair) : Prop :=
  ∃ q : Packet, ∃ e : LiftedStep s ℓ m q, e.target = n

theorem ActualStep.child {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ}
    {m n : MarkedPair} (h : ActualStep s ℓ m n) : Child s m.words n.words := by
  obtain ⟨q, e, rfl⟩ := h
  exact e.child

theorem ActualStep.packet {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ}
    {m n : MarkedPair} (h : ActualStep s ℓ m n) :
    InteriorStep s ℓ m.packet n.packet := by
  obtain ⟨q, e, rfl⟩ := h
  change DigitStep s m.packet e.localization.target.packet ∧
    e.localization.target.packet.Interior ℓ
  rw [e.packet_eq]
  exact ⟨e.digitStep, e.interior⟩

theorem packetSupport_iff_realized {C : Finset WordPair} {p : Packet} :
    p ∈ packetSupport C ↔ Psc.OccurrenceStrict.Realized C p :=
  mem_packetSupport

theorem interior_closed (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (hpos : ∀ a, 0 < ℓ a) {C : Finset WordPair}
    (hC : Psc.StrictSystem.StrictSystem s C) {p q : Packet}
    (hp : p ∈ interiorSupport C ℓ) (hedge : InteriorStep s ℓ p q) :
    q ∈ interiorSupport C ℓ := by
  obtain ⟨hm, _⟩ := mem_interiorSupport.mp hp
  exact mem_interiorSupport.mpr
    ⟨Psc.OccurrenceStrict.realized_closed s ℓ hpos hC hm hedge, hedge.2⟩

theorem interior_avoids_diagonal {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ}
    {C : Finset WordPair} (hC : Psc.StrictSystem.StrictSystem s C)
    {p : Packet} (hp : p ∈ interiorSupport C ℓ) : ¬ p.Diagonal :=
  Psc.OccurrenceStrict.realized_avoids_diagonal hC (mem_interiorSupport.mp hp).1

theorem interior_serial (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    {C : Finset WordPair} (hC : Psc.StrictSystem.StrictSystem s C)
    {p : Packet} (hp : p ∈ interiorSupport C ℓ) :
    ∃ q ∈ interiorSupport C ℓ, InteriorStep s ℓ p q := by
  obtain ⟨q, hedge⟩ := interiorStep_exists s ℓ β hpos hβ hscale p
    (mem_interiorSupport.mp hp).2
  exact ⟨q, interior_closed s ℓ hpos hC hp hedge, hedge⟩

/-- Successor existence is realized from the supplied actual source,
including its words and both selected positions. -/
theorem actual_step_exists (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    {C : Finset WordPair} (hC : Psc.StrictSystem.StrictSystem s C)
    {m : MarkedPair} (hm : m ∈ interiorMarkedSupport C ℓ) :
    ∃ n ∈ interiorMarkedSupport C ℓ, ActualStep s ℓ m n := by
  obtain ⟨hmem, hi⟩ := mem_interiorMarkedSupport.mp hm
  obtain ⟨q, hedge⟩ := interiorStep_exists s ℓ β hpos hβ hscale m.packet hi
  obtain ⟨e⟩ := lift_digitStep s ℓ hpos m (hC.isBlock _ hmem) hedge.1 hedge.2
  refine ⟨e.target, mem_interiorMarkedSupport.mpr ⟨hC.closed _ hmem _ e.child, ?_⟩,
    q, e, rfl⟩
  change e.localization.target.packet.Interior ℓ
  rw [e.packet_eq]
  exact hedge.2

/-- A finite serial relation has a reachable nonempty cycle from every
root.  This is an elementary graph fact, not an exclusion of recurrence. -/
theorem finite_serial_recurrent {α : Type*} [Finite α] (R : α → α → Prop)
    (hR : ∀ a, ∃ b, R a b) (a : α) :
    ∃ b, Relation.ReflTransGen R a b ∧ Relation.TransGen R b b := by
  classical
  let f : α → α := fun x => Classical.choose (hR x)
  have hf (x : α) : R x (f x) := Classical.choose_spec (hR x)
  have reach (n : ℕ) : Relation.ReflTransGen R a (f^[n] a) := by
    induction n with
    | zero => exact .refl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.tail (hf _)
  have positive_path (n : ℕ) (hn : 0 < n) (x : α) :
      Relation.TransGen R x (f^[n] x) := by
    induction n generalizing x with
    | zero => omega
    | succ n ih =>
      by_cases hzero : n = 0
      · subst n
        exact .single (hf x)
      · rw [Function.iterate_succ_apply']
        exact (ih (Nat.pos_of_ne_zero hzero) x).tail (hf _)
  have cycle (i j : ℕ) (hij : i < j) (heq : f^[i] a = f^[j] a) :
      Relation.TransGen R (f^[i] a) (f^[i] a) := by
    have hpath := positive_path (j - i) (Nat.sub_pos_of_lt hij) (f^[i] a)
    have hreturn : f^[j - i] (f^[i] a) = f^[i] a := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hij)]
      exact heq.symm
    rwa [hreturn] at hpath
  obtain ⟨i, j, hij, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n] a)
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ⟨f^[i] a, reach i, cycle i j hlt heq⟩
  · exact ⟨f^[j] a, reach j, cycle j i hgt heq.symm⟩

/-- The recurrence is on actual marked members of the finite carrier,
not merely on equal packet labels. -/
theorem marked_reaches_cycle (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    {C : Finset WordPair} (hC : Psc.StrictSystem.StrictSystem s C)
    (m : MarkedPair) (hmem : m.words ∈ C) (hi : m.packet.Interior ℓ) :
    ∃ n : MarkedPair, n.words ∈ C ∧ n.packet.Interior ℓ ∧ ¬ n.packet.Diagonal ∧
      Relation.ReflTransGen (ActualStep s ℓ) m n ∧
      Relation.TransGen (ActualStep s ℓ) n n := by
  classical
  let V := {n // n ∈ interiorMarkedSupport C ℓ}
  let R : V → V → Prop := fun x y => ActualStep s ℓ x.val y.val
  have hR (x : V) : ∃ y : V, R x y := by
    obtain ⟨n, hn, he⟩ := actual_step_exists s ℓ β hpos hβ hscale hC x.property
    exact ⟨⟨n, hn⟩, he⟩
  let root : V := ⟨m, mem_interiorMarkedSupport.mpr ⟨hmem, hi⟩⟩
  obtain ⟨n, hreach, hcycle⟩ := finite_serial_recurrent R hR root
  obtain ⟨hnmem, hnint⟩ := mem_interiorMarkedSupport.mp n.property
  refine ⟨n.val, hnmem, hnint,
    Psc.OccurrenceStrict.realized_avoids_diagonal hC ⟨n.val, hnmem, rfl⟩, ?_, ?_⟩
  · exact hreach.lift Subtype.val (fun _ _ h => h)
  · exact hcycle.lift Subtype.val (fun _ _ h => h)

theorem strict_interior_nonempty (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (hpos : ∀ a, 0 < ℓ a) {C : Finset WordPair}
    (hC : Psc.StrictSystem.StrictSystem s C) :
    (interiorMarkedSupport C ℓ).Nonempty := by
  obtain ⟨T, hT⟩ := hC.nonempty
  have hblock := hC.isBlock T hT
  have hb : T.2 ≠ [] := by
    intro hnil
    apply hblock.1
    apply List.length_eq_zero_iff.mp
    rw [hblock.2.1.length_eq, hnil, List.length_nil]
  exact interiorMarkedSupport_nonempty ⟨T, hT, hblock.1, hb⟩ ℓ hpos

/-- A supplied strict system has a nonempty actual interior cycle under
positive length scaling.  Ruling such a system out needs additional C4
input; finite recurrence itself is not that contradiction. -/
theorem strict_actual_cycle (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    {C : Finset WordPair} (hC : Psc.StrictSystem.StrictSystem s C) :
    ∃ n : MarkedPair, n.words ∈ C ∧ n.packet.Interior ℓ ∧ ¬ n.packet.Diagonal ∧
      Relation.TransGen (ActualStep s ℓ) n n := by
  obtain ⟨m, hm⟩ := strict_interior_nonempty s ℓ hpos hC
  obtain ⟨hmem, hi⟩ := mem_interiorMarkedSupport.mp hm
  obtain ⟨n, hnmem, hnint, hndiag, _, hcycle⟩ :=
    marked_reaches_cycle s ℓ β hpos hβ hscale hC m hmem hi
  exact ⟨n, hnmem, hnint, hndiag, hcycle⟩

end Psc.OccurrenceRecurrence
