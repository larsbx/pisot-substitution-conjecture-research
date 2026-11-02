import PscVerif.SelectedRank

/-!
Conditional finite graph distance semantics for #442/#447. Actual literal
occurrences and terminalization are inputs, not conclusions about Mojo.
-/
namespace PscVerif.QuotientDistance
open PscVerif.SelectedRank

/-- The lifting hypothesis quantifies over every actual source, not just a
chosen orbit representative. Terminal membership must also be preserved. -/
structure Refinement {n m : Nat}
    (actual : Fin n → Fin n → Prop) (quotient : Fin m → Fin m → Prop)
    (typed : Fin n → Prop) (terminal : Fin m → Prop)
    (project : Fin n → Fin m) : Prop where
  projects : ∀ u v, actual u v → quotient (project u) (project v)
  lifts : ∀ u q, quotient (project u) q →
    ∃ v, actual u v ∧ project v = q
  terminal_iff : ∀ u, typed u ↔ terminal (project u)

/-- An exact length, not a BFS result or a convention for unreachable states. -/
def TerminalPath {n : Nat} (edge : Fin n → Fin n → Prop)
    (terminal : Fin n → Prop) (v : Fin n) (k : Nat) : Prop :=
  ∃ t, terminal t ∧ Path edge v t k

def Shortest {n : Nat} (edge : Fin n → Fin n → Prop)
    (terminal : Fin n → Prop) (v : Fin n) (d : Nat) : Prop :=
  TerminalPath edge terminal v d ∧
    ∀ k, TerminalPath edge terminal v k → d ≤ k

theorem path_lift {n m : Nat}
    {actual : Fin n → Fin n → Prop} {quotient : Fin m → Fin m → Prop}
    {typed : Fin n → Prop} {terminal : Fin m → Prop}
    {project : Fin n → Fin m}
    (h : Refinement actual quotient typed terminal project)
    {a b : Fin m} {k : Nat} (hp : Path quotient a b k) :
    ∀ u, project u = a → ∃ v, project v = b ∧ Path actual u v k := by
  induction hp with
  | nil a =>
    intro u hu
    exact ⟨u, hu, Path.nil u⟩
  | @cons a b c length he _ ih =>
    intro u hu
    have edge : quotient (project u) b := by
      rw [hu]
      exact he
    obtain ⟨v, hv, hproject⟩ := h.lifts u _ edge
    obtain ⟨w, hw, walk⟩ := ih v hproject
    exact ⟨w, hw, Path.cons hv walk⟩

theorem terminal_path_iff {n m : Nat}
    {actual : Fin n → Fin n → Prop} {quotient : Fin m → Fin m → Prop}
    {typed : Fin n → Prop} {terminal : Fin m → Prop}
    {project : Fin n → Fin m}
    (h : Refinement actual quotient typed terminal project) (u : Fin n) (k : Nat) :
    TerminalPath actual typed u k ↔ TerminalPath quotient terminal (project u) k := by
  constructor
  · intro ⟨v, hv, hp⟩
    exact ⟨project v, (h.terminal_iff v).mp hv, path_map project h.projects hp⟩
  · intro ⟨q, hq, hp⟩
    obtain ⟨v, hv, walk⟩ := path_lift h hp u rfl
    have ht : terminal (project v) := by rw [hv]; exact hq
    exact ⟨v, (h.terminal_iff v).mpr ht, walk⟩

theorem no_terminal_path_iff {n m : Nat}
    {actual : Fin n → Fin n → Prop} {quotient : Fin m → Fin m → Prop}
    {typed : Fin n → Prop} {terminal : Fin m → Prop}
    {project : Fin n → Fin m}
    (h : Refinement actual quotient typed terminal project) (u : Fin n) :
    (¬ ∃ k, TerminalPath actual typed u k) ↔
    (¬ ∃ k, TerminalPath quotient terminal (project u) k) := by
  constructor
  · intro hn ⟨k, hp⟩
    exact hn ⟨k, (terminal_path_iff h u k).mpr hp⟩
  · intro hn ⟨k, hp⟩
    exact hn ⟨k, (terminal_path_iff h u k).mp hp⟩

theorem shortest_iff {n m : Nat}
    {actual : Fin n → Fin n → Prop} {quotient : Fin m → Fin m → Prop}
    {typed : Fin n → Prop} {terminal : Fin m → Prop}
    {project : Fin n → Fin m}
    (h : Refinement actual quotient typed terminal project) (u : Fin n) (d : Nat) :
    Shortest actual typed u d ↔ Shortest quotient terminal (project u) d := by
  constructor
  · intro ⟨hp, hmin⟩
    exact ⟨(terminal_path_iff h u d).mp hp,
      fun k hk => hmin k ((terminal_path_iff h u k).mpr hk)⟩
  · intro ⟨hp, hmin⟩
    exact ⟨(terminal_path_iff h u d).mpr hp,
      fun k hk => hmin k ((terminal_path_iff h u k).mp hk)⟩

theorem shortest_unique {n : Nat} {edge : Fin n → Fin n → Prop}
    {terminal : Fin n → Prop} {v : Fin n} {a b : Nat}
    (ha : Shortest edge terminal v a) (hb : Shortest edge terminal v b) : a = b := by
  exact Nat.le_antisymm (ha.2 b hb.1) (hb.2 a ha.1)

/-- Selected descent alone certifies an upper bound; all-edge inequalities
supply the lower bound needed for a shortest-distance certificate. -/
structure ExactWitness {n : Nat} (edge : Fin n → Fin n → Prop)
    (terminal : Fin n → Prop) (rank : Fin n → Nat)
    : Prop extends Witness edge terminal rank where
  bound : ∀ u v, edge u v → rank u ≤ rank v + 1

theorem path_bound {n : Nat} {edge : Fin n → Fin n → Prop}
    {terminal : Fin n → Prop} {rank : Fin n → Nat}
    (h : ExactWitness edge terminal rank)
    {u v : Fin n} {k : Nat} (hp : Path edge u v k) : rank u ≤ rank v + k := by
  induction hp with
  | nil u => exact Nat.le_refl _
  | cons he _ ih =>
    exact Nat.le_trans (h.bound _ _ he)
      (by simpa only [Nat.add_assoc] using Nat.add_le_add_right ih 1)

theorem certified_shortest {n : Nat} {edge : Fin n → Fin n → Prop}
    {terminal : Fin n → Prop} {rank : Fin n → Nat}
    (h : ExactWitness edge terminal rank) (v : Fin n) :
    Shortest edge terminal v (rank v) := by
  refine ⟨selected_path_of_rank h.toWitness v, ?_⟩
  intro k ⟨t, ht, hp⟩
  have hz : rank t = 0 := (h.zero_iff t).mpr ht
  simpa only [hz, Nat.zero_add] using path_bound h hp

theorem certified_quotient_distance {n m : Nat}
    {actual : Fin n → Fin n → Prop} {quotient : Fin m → Fin m → Prop}
    {typed : Fin n → Prop} {terminal : Fin m → Prop}
    {project : Fin n → Fin m} {originalRank : Fin n → Nat} {quotientRank : Fin m → Nat}
    (refines : Refinement actual quotient typed terminal project)
    (original : ExactWitness actual typed originalRank)
    (compressed : ExactWitness quotient terminal quotientRank) (v : Fin n) :
    originalRank v = quotientRank (project v) := by
  exact shortest_unique (certified_shortest original v)
    ((shortest_iff refines v _).mpr (certified_shortest compressed (project v)))

/- A longer real path is not a shortest-distance certificate. -/
def triangle (u v : Fin 3) : Prop :=
  (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨ (u = 0 ∧ v = 2)
def triangleTerminal (v : Fin 3) : Prop := v = 2
def longerRank (v : Fin 3) : Nat := if v = 0 then 2 else if v = 1 then 1 else 0

theorem longer_selected_witness : Witness triangle triangleTerminal longerRank := by
  constructor
  · unfold longerRank triangleTerminal
    decide
  · unfold longerRank triangle
    decide

theorem longer_is_not_exact : ¬ ExactWitness triangle triangleTerminal longerRank := by
  intro h
  have bad := h.bound 0 2 (by unfold triangle; decide)
  change 2 ≤ 0 + 1 at bad
  exact (by decide : ¬ 2 ≤ 1) bad

/- The quotient's edge lifts from original 0, but not from source 1 in the
same fiber. Projection and even exact terminal correspondence are insufficient. -/
def oneSidedActual (u v : Fin 3) : Prop :=
  (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 1)
def oneSidedQuotient (u v : Fin 2) : Prop := u = 0 ∧ (v = 0 ∨ v = 1)
def oneSidedProject (u : Fin 3) : Fin 2 := if u = 2 then 1 else 0

theorem one_sided_projects : ∀ u v, oneSidedActual u v →
    oneSidedQuotient (oneSidedProject u) (oneSidedProject v) := by
  unfold oneSidedActual oneSidedQuotient oneSidedProject
  decide

theorem one_sided_terminal_iff : ∀ u : Fin 3,
    u = 2 ↔ oneSidedProject u = 1 := by
  unfold oneSidedProject
  decide

theorem one_sided_cannot_lift : ¬ (∀ u q, oneSidedQuotient (oneSidedProject u) q →
    ∃ v, oneSidedActual u v ∧ oneSidedProject v = q) := by
  unfold oneSidedQuotient oneSidedProject oneSidedActual
  decide

theorem one_sided_quotient_terminal_path :
    TerminalPath oneSidedQuotient (fun v => v = 1) 0 1 := by
  exact ⟨1, rfl, Path.cons ⟨rfl, Or.inr rfl⟩ (Path.nil 1)⟩

theorem one_sided_original_trapped :
    ¬ ∃ k, TerminalPath oneSidedActual (fun v => v = 2) 1 k := by
  intro ⟨k, v, hv, hp⟩
  have closed : ∀ u w : Fin 3, u = 1 → oneSidedActual u w → w = 1 := by
    unfold oneSidedActual
    decide
  have trapped := path_stays_in (fun u => u = 1) closed hp rfl
  exact (by decide : (2 : Fin 3) ≠ 1) (hv ▸ trapped)

theorem terminal_mismatch_refused : ¬ (∀ v : Fin 2, v = 0 ↔ v = 1) := by
  decide

end PscVerif.QuotientDistance
