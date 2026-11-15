/-
# Actual strict systems and interior affine packet paths

This adapter composes the concrete finite occurrence lift with the existing
`StrictSystem` definition. A supplied strict system gives a successor-closed,
diagonal-free set of packets realized by its actual marked word pairs.

No existence of a productive route is asserted. The open C4 obligation is
to exclude the resulting avoiding region for an actual forced crossing
under the full PIP and hub hypotheses. Global strict-component extraction
and completeness of the production packet graph remain separate.

The targeted review is `docs/c4-address-transport-literature-2026-11-10.md`.
-/
import PscVerif.OccurrenceTransport
import PscVerif.StrictSystem

namespace Psc.OccurrenceStrict

open Psc.Binomial Psc.Reduction Psc.Descendants Psc.OccurrenceTransport

/-- Packets projected from actual marked words in the supplied carrier.
This predicate does not assert completeness of a computed packet graph. -/
def Realized (C : Finset WordPair) (p : Packet) : Prop :=
  ∃ m : MarkedPair, m.words ∈ C ∧ m.packet = p

/-- Every interior affine digit edge from a realized packet has an actual
child realization in the same strict system. -/
theorem realized_closed (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (hpos : ∀ a, 0 < ℓ a) {C : Finset WordPair}
    (hC : Psc.StrictSystem.StrictSystem s C) {p q : Packet}
    (hp : Realized C p) (hedge : InteriorStep s ℓ p q) : Realized C q := by
  obtain ⟨m, hm, hmp⟩ := hp
  have hstep : DigitStep s m.packet q := by
    rw [hmp]
    exact hedge.1
  obtain ⟨e⟩ := lift_digitStep s ℓ hpos m (hC.isBlock _ hm) hstep hedge.2
  exact ⟨e.target, hC.closed _ hm _ e.child, e.packet_eq⟩

/-- A diagonal packet inside a member would force that actual irreducible
word pair to be coincident, contradicting the supplied strictness. -/
theorem realized_avoids_diagonal {s : Fin 3 → Word} {C : Finset WordPair}
    (hC : Psc.StrictSystem.StrictSystem s C) {p : Packet}
    (hp : Realized C p) : ¬ p.Diagonal := by
  obtain ⟨m, hm, hmp⟩ := hp
  intro hdiag
  have hd : m.packet.Diagonal := by
    rw [hmp]
    exact hdiag
  exact hC.noncoincident _ hm (m.diagonal_coincident (hC.isBlock _ hm) hd)

/-- Membership persists along the independent interior affine relation;
the one-step closure uses actual child localization. -/
theorem packet_path_mem (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (hpos : ∀ a, 0 < ℓ a) {C : Finset WordPair}
    (hC : Psc.StrictSystem.StrictSystem s C) {p q : Packet}
    (hp : Realized C p)
    (hpath : Relation.ReflTransGen (InteriorStep s ℓ) p q) : Realized C q := by
  induction hpath with
  | refl => exact hp
  | tail _ hedge ih => exact realized_closed s ℓ hpos hC ih hedge

/-- The concrete strict-system counterpart of the earlier generic
closed-set productivity obstruction. This is a conditional exclusion of
packet routes, not a proof that PIP forced crossings have such routes. -/
theorem no_diagonal_route (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (hpos : ∀ a, 0 < ℓ a) {C : Finset WordPair}
    (hC : Psc.StrictSystem.StrictSystem s C) (m : MarkedPair)
    (hm : m.words ∈ C) :
    ¬ ∃ q : Packet, Relation.ReflTransGen (InteriorStep s ℓ) m.packet q ∧
      q.Diagonal := by
  rintro ⟨q, hpath, hdiag⟩
  obtain ⟨U, hchild, _, hco⟩ :=
    packet_path_literal_target s ℓ hpos m (hC.isBlock _ hm) hpath hdiag
  exact hC.no_coincidence_reachable hm hchild hco

/-- Every recorded addressed path remains in the actual strict carrier. -/
theorem addressed_path_mem {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ}
    {C : Finset WordPair} (hC : Psc.StrictSystem.StrictSystem s C)
    {m n : MarkedPair} (hm : m.words ∈ C) (hpath : AddressedPath s ℓ m n) :
    n.words ∈ C := hC.reflTransGen_mem hm hpath.child_path

/-- A supplied strict component inherits the same occurrence-level
obstruction. Strong connectivity is not needed for this deduction. -/
theorem strictComponent_no_diagonal_route (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (hpos : ∀ a, 0 < ℓ a) {C : Finset WordPair}
    (hC : Psc.StrictSystem.StrictComponent s C) (m : MarkedPair)
    (hm : m.words ∈ C) :
    ¬ ∃ q : Packet, Relation.ReflTransGen (InteriorStep s ℓ) m.packet q ∧
      q.Diagonal :=
  no_diagonal_route s ℓ hpos hC.toStrictSystem m hm

end Psc.OccurrenceStrict
