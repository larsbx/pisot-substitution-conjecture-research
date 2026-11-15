import Lean

namespace C4Orientation

inductive Path {V : Type} (step : V → V → Prop) : V → V → Prop
  | nil (x : V) : Path step x x
  | cons {x y z : V} : step x y → Path step y z → Path step x z

variable {V : Type} {step : V → V → Prop}

theorem Path.append {x y z : V} (p : Path step x y) (q : Path step y z) :
    Path step x z := by
  revert q
  induction p with
  | nil => exact fun q => q
  | cons edge _ ih => exact fun q => .cons edge (ih q)

def Closed (S : V → Prop) (step : V → V → Prop) : Prop :=
  ∀ ⦃x y⦄, S x → step x y → S y

theorem Path.preserve {S : V → Prop} (closed : Closed S step)
    {x y : V} (p : Path step x y) (hx : S x) : S y := by
  revert hx
  induction p with
  | nil => exact fun hx => hx
  | cons edge _ ih => exact fun hx => ih (closed hx edge)

def Reaches (step : V → V → Prop) (target : V → Prop) (x : V) : Prop :=
  ∃ y, Path step x y ∧ target y

theorem gate_productivity {left right diagonal : V → Prop}
    (leftWitness : ∀ x, left x → Reaches step diagonal x)
    (rightWitness : ∀ x, right x → Reaches step diagonal x)
    {root : V} (h : Reaches step (fun x => left x ∨ right x) root) :
    Reaches step diagonal root := by
  obtain ⟨g, toGate, hg⟩ := h
  have tail : Reaches step diagonal g := by
    cases hg with
    | inl h => exact leftWitness g h
    | inr h => exact rightWitness g h
  obtain ⟨d, toDiagonal, hd⟩ := tail
  exact ⟨d, toGate.append toDiagonal, hd⟩

theorem strict_excludes_productivity {S diagonal : V → Prop}
    (closed : Closed S step) (strict : ∀ x, S x → ¬ diagonal x)
    {root : V} (hr : S root) : ¬ Reaches step diagonal root := by
  rintro ⟨d, p, hd⟩
  exact strict d (p.preserve closed hr) hd

/-- Exact obstruction at a seed, independent of a vertex bound. -/
theorem no_route_iff_closed_avoiding {target : V → Prop} {root : V} :
    (¬ Reaches step target root) ↔
    ∃ S : V → Prop, S root ∧ Closed S step ∧ (∀ x, S x → ¬ target x) := by
  constructor
  · intro h
    refine ⟨Path step root, .nil root, ?_, ?_⟩
    · intro x y hx edge
      exact hx.append (.cons edge (.nil y))
    · intro x hx ht
      exact h ⟨x, hx, ht⟩
  · rintro ⟨S, hs, closed, avoids⟩ ⟨x, p, ht⟩
    exact avoids x (p.preserve closed hs) ht

end C4Orientation
