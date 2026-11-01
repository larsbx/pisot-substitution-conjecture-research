import Init.Data.Nat.Lemmas

/-!
Finite selected-path soundness. The relations below are semantic inputs:
this file does not prove that the Mojo checker refines these definitions.
All-descendant productivity additionally requires the explicit closure premise.
-/
namespace PscVerif.SelectedRank

inductive Path {n : Nat} (edge : Fin n → Fin n → Prop) :
    Fin n → Fin n → Nat → Prop where
  | nil (v : Fin n) : Path edge v v 0
  | cons {u v w : Fin n} {k : Nat} :
      edge u v → Path edge v w k → Path edge u w (k + 1)

structure Witness {n : Nat} (edge : Fin n → Fin n → Prop)
    (terminal : Fin n → Prop) (rank : Fin n → Nat) : Prop where
  zero_iff : ∀ v, rank v = 0 ↔ terminal v
  step : ∀ v, rank v ≠ 0 → ∃ w, edge v w ∧ rank v = rank w + 1

theorem selected_path_of_rank {n : Nat} {edge : Fin n → Fin n → Prop}
    {terminal : Fin n → Prop} {rank : Fin n → Nat}
    (h : Witness edge terminal rank) (v : Fin n) :
    ∃ t, terminal t ∧ Path edge v t (rank v) := by
  have go : ∀ k v, rank v = k → ∃ t, terminal t ∧ Path edge v t k := by
    intro k
    induction k with
    | zero =>
      intro u hu
      exact ⟨u, (h.zero_iff u).mp hu, Path.nil u⟩
    | succ k ih =>
      intro u hu
      have hn : rank u ≠ 0 := by
        rw [hu]
        exact Nat.succ_ne_zero k
      obtain ⟨w, hw, hr⟩ := h.step u hn
      have heq : rank w = k := Nat.succ.inj (hr.symm.trans hu)
      obtain ⟨t, ht, hp⟩ := ih w heq
      exact ⟨t, ht, Path.cons hw hp⟩
  exact go (rank v) v rfl

theorem path_map {n m : Nat} {edge : Fin n → Fin n → Prop}
    {actual : Fin m → Fin m → Prop} (embed : Fin n → Fin m)
    (sound : ∀ u v, edge u v → actual (embed u) (embed v))
    {u v : Fin n} {k : Nat} (hp : Path edge u v k) :
    Path actual (embed u) (embed v) k := by
  induction hp with
  | nil v => exact Path.nil (embed v)
  | cons he _ ih => exact Path.cons (sound _ _ he) ih

theorem selected_path_sound {n m : Nat} {edge : Fin n → Fin n → Prop}
    {terminal : Fin n → Prop} {rank : Fin n → Nat}
    {actual : Fin m → Fin m → Prop} {typed : Fin m → Prop}
    (embed : Fin n → Fin m) (h : Witness edge terminal rank)
    (edge_sound : ∀ u v, edge u v → actual (embed u) (embed v))
    (terminal_sound : ∀ v, terminal v → typed (embed v)) (v : Fin n) :
    ∃ t, typed t ∧ Path actual (embed v) t (rank v) := by
  obtain ⟨t, ht, hp⟩ := selected_path_of_rank h v
  exact ⟨embed t, terminal_sound t ht, path_map embed edge_sound hp⟩

theorem path_stays_in {m : Nat} {actual : Fin m → Fin m → Prop}
    (carrier : Fin m → Prop)
    (closed : ∀ u v, carrier u → actual u v → carrier v)
    {u v : Fin m} {k : Nat} (hp : Path actual u v k) :
    carrier u → carrier v := by
  induction hp with
  | nil _ => exact fun h => h
  | cons he _ ih => exact fun h => ih (closed _ _ h he)

theorem covered_descendants_productive {n m : Nat}
    {edge : Fin n → Fin n → Prop} {terminal : Fin n → Prop}
    {rank : Fin n → Nat} {actual : Fin m → Fin m → Prop}
    {typed seeds : Fin m → Prop}
    (embed : Fin n → Fin m) (h : Witness edge terminal rank)
    (edge_sound : ∀ u v, edge u v → actual (embed u) (embed v))
    (terminal_sound : ∀ v, terminal v → typed (embed v))
    (seed_covered : ∀ s, seeds s → ∃ i, embed i = s)
    (closed : ∀ u v, (∃ i, embed i = u) → actual u v → ∃ i, embed i = v)
    {s v : Fin m} {k : Nat} (hs : seeds s) (hp : Path actual s v k) :
    ∃ i, embed i = v ∧ ∃ t, typed t ∧ Path actual v t (rank i) := by
  have member := path_stays_in (fun u => ∃ i, embed i = u) closed hp
    (seed_covered s hs)
  obtain ⟨i, hi⟩ := member
  obtain ⟨t, ht, hpath⟩ := selected_path_sound embed h edge_sound terminal_sound i
  exact ⟨i, hi, t, ht, hi ▸ hpath⟩

/- Concrete negative calibration: 0 selects terminal 1 but also reaches the
unlisted vertex 2, which has only a self-loop. All vertex types are finite. -/
def controlEdge (u v : Fin 3) : Prop :=
  (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 2)

def controlLocalEdge (u v : Fin 2) : Prop := u = 0 ∧ v = 1
def controlTerminal (v : Fin 2) : Prop := v = 1
def controlRank (v : Fin 2) : Nat := if v = 0 then 1 else 0
def controlEmbed (v : Fin 2) : Fin 3 := ⟨v.val, Nat.lt_trans v.isLt (by decide)⟩

theorem control_local_witness :
    Witness controlLocalEdge controlTerminal controlRank := by
  constructor
  · unfold controlRank controlTerminal
    decide
  · unfold controlRank controlLocalEdge
    decide

theorem control_edges_sound : ∀ u v, controlLocalEdge u v →
    controlEdge (controlEmbed u) (controlEmbed v) := by
  unfold controlLocalEdge controlEdge
  decide

theorem control_terminal_sound : ∀ v, controlTerminal v → controlEmbed v = 1 := by
  unfold controlTerminal
  decide

theorem control_local_selected_path :
    ∃ t, t = (1 : Fin 3) ∧
      Path controlEdge (controlEmbed (0 : Fin 2)) t (controlRank 0) := by
  exact selected_path_sound controlEmbed control_local_witness
    control_edges_sound control_terminal_sound 0

theorem control_unlisted_descendant : Path controlEdge 0 2 1 := by
  exact Path.cons (Or.inr (Or.inl ⟨rfl, rfl⟩)) (Path.nil 2)

theorem control_carrier_not_closed :
    ¬ (∀ u v, (∃ i, controlEmbed i = u) → controlEdge u v →
      ∃ i, controlEmbed i = v) := by
  unfold controlEdge
  decide

theorem control_trap_stays (v : Fin 3) (k : Nat)
    (hp : Path controlEdge 2 v k) : v = 2 := by
  have closed : ∀ u w : Fin 3, u = 2 → controlEdge u w → w = 2 := by
    unfold controlEdge
    decide
  exact path_stays_in (fun u => u = 2) closed hp rfl

theorem control_trap_has_no_terminal_path :
    ¬ ∃ k, Path controlEdge 2 1 k := by
  intro ⟨k, hp⟩
  have impossible : (1 : Fin 3) = 2 := control_trap_stays 1 k hp
  exact (by decide : (1 : Fin 3) ≠ 2) impossible

end PscVerif.SelectedRank
