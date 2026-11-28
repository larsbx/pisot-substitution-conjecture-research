import PscVerif.BetaMetallicUnique
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Normal form and cardinality of the unique metallic expansions

Companion to `PscVerif.BetaMetallicUnique`. For `β² = mβ + 1`, `m ≥ 1`, with
the full alphabet `{0, …, m}`:

* `endpointsInitial_iff`: the unique streams are exactly `0^∞`, `m^∞`, and
  `a^r w` with `a ∈ {0, m}`, `r ≥ 0` and every digit of `w` in `{1, …, m-1}`;
* `value_lt_one_iff`: a unique stream has value below `1` iff it never uses the
  digit `m`, so on `[0, 1)` the unique streams are `0^∞` and `0^r w`;
* `unique_one`: at `m = 1` the unique streams are exactly the two constants;
* `unique_two_countable`, `unique_two_infinite`: at `m = 2` they form a
  countably infinite set;
* `unique_not_countable`: at `m ≥ 3` they form an uncountable set.

Specializations of known theory; no novelty is claimed. Source decision:
`docs/beta-numeration-research-route-2026-11-27.md`.
-/

set_option autoImplicit false

namespace Psc.BetaMetallicUnique

variable {m : ℕ}

/-- A digit is an endpoint. -/
def IsEnd (a : Fin (m + 1)) : Prop := (a : ℕ) = 0 ∨ (a : ℕ) = m

/-- A digit is interior. -/
def IsInterior (a : Fin (m + 1)) : Prop := 0 < (a : ℕ) ∧ (a : ℕ) < m

theorem isEnd_or_isInterior (a : Fin (m + 1)) : IsEnd a ∨ IsInterior a := by
  have := a.2
  unfold IsEnd IsInterior
  omega

/-- The explicit normal form. -/
def NormalForm (d : ℕ → Fin (m + 1)) : Prop :=
  (∀ n, (d n : ℕ) = 0) ∨ (∀ n, (d n : ℕ) = m) ∨
    ∃ r : ℕ, ∃ a : Fin (m + 1), IsEnd a ∧ (∀ i < r, d i = a) ∧ ∀ i, r ≤ i → IsInterior (d i)

/-- In a stream with endpoint-initial digits, an endpoint digit equals every
earlier digit. -/
theorem EndpointsInitial.eq_of_end {d : ℕ → Fin (m + 1)} (_hm : 1 ≤ m) (S : EndpointsInitial d)
    {j : ℕ} (hj : IsEnd (d j)) : ∀ i ≤ j, d i = d j := by
  intro i hi
  induction j, hi using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    have hprev : IsEnd (d j) ∧ d j = d (j + 1) := by
      rcases hj with h | h
      · have := S.1 j h
        exact ⟨Or.inl this, Fin.ext (by omega)⟩
      · have := S.2 j h
        exact ⟨Or.inr this, Fin.ext (by omega)⟩
    rw [ih hprev.1, hprev.2]

theorem endpointsInitial_iff (hm : 1 ≤ m) (d : ℕ → Fin (m + 1)) :
    EndpointsInitial d ↔ NormalForm d := by
  constructor
  · intro S
    by_cases hint : ∃ i, IsInterior (d i)
    · classical
      set r := Nat.find hint
      have hr : IsInterior (d r) := Nat.find_spec hint
      right; right
      have hpost : ∀ i, r ≤ i → IsInterior (d i) := fun i hi => by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
        exact S.interior_from hr.1 hr.2 k
      rcases Nat.eq_zero_or_pos r with h0 | hpos
      · exact ⟨r, ⟨0, by omega⟩, Or.inl rfl, fun i hi => absurd hi (by omega), hpost⟩
      · have hend0 : IsEnd (d 0) := (isEnd_or_isInterior (d 0)).resolve_right
          (Nat.find_min hint hpos)
        refine ⟨r, d 0, hend0, fun i hi => ?_, hpost⟩
        have hend : IsEnd (d (r - 1)) := (isEnd_or_isInterior _).resolve_right
          (Nat.find_min hint (by omega))
        rw [S.eq_of_end hm hend i (by omega), S.eq_of_end hm hend 0 (by omega)]
    · simp only [not_exists] at hint
      have hend : ∀ i, IsEnd (d i) := fun i => (isEnd_or_isInterior _).resolve_right (hint i)
      have hc : ∀ i, d i = d 0 := fun i => (S.eq_of_end hm (hend i) 0 (Nat.zero_le _)).symm
      rcases hend 0 with h | h
      · exact Or.inl fun n => by rw [hc n]; exact h
      · exact Or.inr (Or.inl fun n => by rw [hc n]; exact h)
  · rintro (h | h | ⟨r, a, ha, hpre, hpost⟩)
    · exact ⟨fun n _ => h n, fun n hn => by have := h (n + 1); omega⟩
    · exact ⟨fun n hn => by have := h (n + 1); omega, fun n _ => h n⟩
    · refine ⟨fun n hn => ?_, fun n hn => ?_⟩
      · have hlt : n + 1 < r := by
          by_contra hge
          have := (hpost (n + 1) (by omega)).1
          omega
        rw [hpre n (by omega)]
        rw [hpre (n + 1) hlt] at hn
        exact hn
      · have hlt : n + 1 < r := by
          by_contra hge
          have := (hpost (n + 1) (by omega)).2
          omega
        rw [hpre n (by omega)]
        rw [hpre (n + 1) hlt] at hn
        exact hn

namespace Base

variable {B : Base m}

/-- A unique stream has value below `1` iff it never uses the digit `m`. -/
theorem value_lt_one_iff {d : ℕ → Fin (m + 1)} (h : B.IsUnique d) :
    B.value d < 1 ↔ ∀ n, (d n : ℕ) < m := by
  constructor
  · intro hlt n
    by_contra hn
    have hdn : (d n : ℕ) = m := le_antisymm (Nat.lt_succ_iff.mp (d n).2) (not_lt.mp hn)
    have S := h.endpointsInitial
    have h0 : (d 0 : ℕ) = m := by
      have := S.eq_of_end B.one_le (Or.inr hdn) 0 (Nat.zero_le _)
      rw [this]; exact hdn
    have hpos : ∀ k, 0 < (d (0 + k) : ℕ) := S.pos_from (by have := B.one_le; omega)
    have htail : B.r < B.value (tail d) := B.lt_value fun k => by simpa using hpos (k + 1)
    have step := B.value_eq_step d
    rw [h0] at step
    have hc := B.carry
    have : 1 < B.value d := by nlinarith [B.r_pos]
    linarith
  · intro hall
    exact B.value_lt_one hall

end Base

/-! ## Cardinalities -/

/-- The set of unique streams for a base. -/
def Base.uniqueSet (B : Base m) : Set (ℕ → Fin (m + 1)) := {d | B.IsUnique d}

theorem Base.mem_uniqueSet_iff (B : Base m) (d : ℕ → Fin (m + 1)) :
    d ∈ B.uniqueSet ↔ NormalForm d :=
  (Base.isUnique_iff d).trans (endpointsInitial_iff B.one_le d)

/-- At `m = 1` exactly the two constant streams are unique. -/
theorem unique_one (B : Base 1) :
    B.uniqueSet = {fun _ => 0, fun _ => 1} := by
  ext d
  rw [Base.mem_uniqueSet_iff, NormalForm]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h | ⟨r, a, -, -, hpost⟩)
    · exact Or.inl (funext fun n => Fin.ext (h n))
    · exact Or.inr (funext fun n => Fin.ext (h n))
    · have := hpost r le_rfl
      unfold IsInterior at this
      omega
  · rintro (rfl | rfl)
    · exact Or.inl fun _ => rfl
    · exact Or.inr (Or.inl fun _ => rfl)

/-- The stream `a^r 1^∞` over `{0, 1, 2}`. -/
def prefixOne (a : Fin 3) (r : ℕ) : ℕ → Fin 3 := fun i => if i < r then a else 1

theorem unique_two_subset (B : Base 2) :
    B.uniqueSet ⊆ {fun _ => 0, fun _ => 2} ∪
      Set.range (fun x : Bool × ℕ => prefixOne (if x.1 then 2 else 0) x.2) := by
  intro d hd
  rw [Base.mem_uniqueSet_iff, NormalForm] at hd
  rcases hd with h | h | ⟨r, a, ha, hpre, hpost⟩
  · exact Or.inl (Or.inl (funext fun n => Fin.ext (h n)))
  · exact Or.inl (Or.inr (funext fun n => Fin.ext (h n)))
  · refine Or.inr ⟨((a : ℕ) = 2, r), funext fun i => ?_⟩
    show (if i < r then (if decide ((a : ℕ) = 2) = true then (2 : Fin 3) else 0) else 1) = d i
    by_cases hi : i < r
    · rw [hpre i hi]
      simp only [hi, ite_true]
      rcases ha with h0 | h2
      · have h2' : ¬ (a : ℕ) = 2 := by omega
        simp only [h2', decide_false, Bool.false_eq_true, ite_false]
        exact Fin.ext (by simp [h0])
      · simp only [h2, decide_true, ite_true]
        exact Fin.ext (by simp [h2])
    · simp only [hi, ite_false]
      have := hpost i (by omega)
      unfold IsInterior at this
      exact Fin.ext (by simp; omega)

/-- At `m = 2` the unique streams form a countable set. -/
theorem unique_two_countable (B : Base 2) : B.uniqueSet.Countable :=
  ((Set.toFinite _).countable.union (Set.countable_range _)).mono (unique_two_subset B)

/-- At `m = 2` the unique streams form an infinite set: `0^r 1^∞`, `r ≥ 0`. -/
theorem unique_two_infinite (B : Base 2) : B.uniqueSet.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := prefixOne 0) ?_ ?_
  · intro r s h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := congrFun h r
      simp [prefixOne, hlt] at this
    · have := congrFun h s
      simp [prefixOne, hlt] at this
  · intro r
    rw [Base.mem_uniqueSet_iff]
    refine Or.inr (Or.inr ⟨r, 0, Or.inl rfl, fun i hi => by simp [prefixOne, hi],
      fun i hi => ?_⟩)
    simp [prefixOne, not_lt.mpr hi, IsInterior]

theorem not_countable_bool_seq : ¬ Countable (ℕ → Bool) := by
  intro h
  have : Cardinal.mk (ℕ → Bool) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.mpr h
  rw [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_id,
    Cardinal.lift_id] at this
  exact absurd this (not_le.mpr (by simpa using Cardinal.cantor Cardinal.aleph0))

/-- At `m ≥ 3` the unique streams form an uncountable set: every stream over
`{1, 2}` is unique. -/
theorem unique_not_countable (hm : 3 ≤ m) (B : Base m) : ¬ B.uniqueSet.Countable := by
  intro hc
  let g : (ℕ → Bool) → (ℕ → Fin (m + 1)) :=
    fun b i => if b i then ⟨2, by omega⟩ else ⟨1, by omega⟩
  have hmem : ∀ b, g b ∈ B.uniqueSet := fun b => by
    rw [Base.mem_uniqueSet_iff]
    refine Or.inr (Or.inr ⟨0, 0, Or.inl rfl, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun i _ => ?_⟩)
    unfold IsInterior
    simp only [g]
    split <;> simp <;> omega
  have hinj : Function.Injective fun b => (⟨g b, hmem b⟩ : B.uniqueSet) := by
    intro b b' h
    funext i
    have := congrArg (fun d : B.uniqueSet => ((d.1 i : Fin (m + 1)) : ℕ)) h
    simp only [g] at this
    cases hb : b i <;> cases hb' : b' i <;> simp_all
  have : Countable B.uniqueSet := hc.to_subtype
  exact not_countable_bool_seq hinj.countable

end Psc.BetaMetallicUnique
