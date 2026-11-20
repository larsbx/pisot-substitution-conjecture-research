import PscVerif.C4ParameterFamilyWords
import PscVerif.Termination
import PscVerif.FastForwardCarrier

/-! Bind the symbolic word rows to the repository's literal `ChildNC` relation. -/

namespace Psc.ParameterFamilyCarrier

open Psc.Reduction Psc.Descendants Psc.FastForwardCarrier
open Psc.ParameterFamilyWords (ones)
open Psc.ParameterFamilyRows (state baseState baseRow children substitution swapIndex swapIndex_lt
  swap_state base_row_lt base_exit representative_row_tracks)
open Psc.Binomial (subst)

private def aligned (n : Nat) : Nat → Pair
  | 2 => ([0, 1, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2], [1, 1, 1] ++ ones n ++ [1, 1, 2, 0, 0, 1])
  | 4 => ([0, 1, 1, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2], [1, 1, 1, 1] ++ ones n ++ [1, 2, 0, 0, 1, 1])
  | 5 => ([0, 1, 1, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2, 0], [1, 1, 1, 1] ++ ones n ++ [1, 2, 0, 0, 1, 0, 1])
  | 6 => ([0, 1, 1, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2], [1, 1, 1, 1] ++ ones n ++ [1, 2, 0, 1, 1, 1, 1] ++ ones n ++ [1, 2, 0, 0, 1, 1])
  | 7 => ([0, 1, 1, 1, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1] ++ ones n ++ [2, 0, 1, 1, 1, 1, 1] ++ ones n ++ [2, 0, 0, 1, 1, 1])
  | 8 => ([0, 1, 1, 1, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2, 0], [1, 1, 1, 1, 1] ++ ones n ++ [2, 0, 1, 1, 1, 1, 1] ++ ones n ++ [2, 0, 0, 1, 1, 0, 1])
  | 9 => ([0, 1, 1, 1, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2, 1, 0], [1, 1, 1, 1, 1] ++ ones n ++ [2, 0, 1, 1, 1, 1, 1] ++ ones n ++ [2, 0, 0, 1, 1, 0, 1, 1])
  | 13 => ([1, 1, 2, 0, 1, 1] ++ ones n ++ [1, 1, 1, 2, 0, 0], [2, 0, 0, 1, 1, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2])
  | 14 => ([1, 1, 2, 0, 1, 1, 1] ++ ones n ++ [1, 1, 2, 0, 0, 1], [2, 0, 0, 1, 1, 1, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2])
  | 15 => ([1, 1, 2, 0, 1, 1] ++ ones n ++ [1, 1, 1, 2, 0, 1, 1] ++ ones n ++ [1, 1, 1, 2, 0, 0], [2, 0, 0, 1, 1, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2])
  | 16 => ([1, 1, 2, 0, 1, 1, 1] ++ ones n ++ [1, 1, 2, 0, 1, 1, 1] ++ ones n ++ [1, 1, 2, 0, 0, 1], [2, 0, 0, 1, 1, 1, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2])
  | 17 => ([1, 1, 2, 0, 1, 1, 1] ++ ones n ++ [1, 1, 2, 0, 1, 1, 1, 1] ++ ones n ++ [1, 2, 0, 0, 1, 1], [2, 0, 0, 1, 1, 1, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2, 1, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2])
  | 18 => ([1, 1, 2, 0, 1, 1] ++ ones n ++ [1, 1, 1, 2, 0, 1, 1] ++ ones n ++ [1, 1, 1, 2, 0, 1, 1] ++ ones n ++ [1, 1, 1, 2, 0, 0], [2, 0, 0, 1, 1, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2])
  | 19 => ([1, 1, 2, 0, 1, 1, 1] ++ ones n ++ [1, 1, 2, 0, 1, 1, 1] ++ ones n ++ [1, 1, 2, 0, 1, 1, 1] ++ ones n ++ [1, 1, 2, 0, 0, 1], [2, 0, 0, 1, 1, 1, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2])
  | 20 => ([1, 1, 2, 0, 1, 1, 1] ++ ones n ++ [1, 1, 2, 0, 1, 1, 1] ++ ones n ++ [1, 1, 2, 0, 1, 1, 1, 1] ++ ones n ++ [1, 2, 0, 0, 1, 0, 1], [2, 0, 0, 1, 1, 1, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2, 1, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2, 0])
  | 21 => ([1, 1, 2, 0, 1, 1, 1] ++ ones n ++ [1, 1, 2, 0, 1, 1, 1] ++ ones n ++ [1, 1, 2, 0, 1, 1, 1, 1] ++ ones n ++ [1, 2, 0, 0, 1, 1], [2, 0, 0, 1, 1, 1, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2, 1, 0] ++ ones n ++ [1, 1, 1, 1, 1, 2])
  | i => baseState n i
private theorem ones_slide (n : Nat) (w : Word) :
    (1 : Fin 3) :: (ones n ++ w) = ones n ++ 1 :: w := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (List.cons 1) ih

private theorem ones_offset (n m : Nat) : ones (n + m) = ones n ++ ones m :=
  List.replicate_add n m 1

set_option linter.unusedSimpArgs false in
private theorem baseState_eq_aligned (n : Nat) (i : Fin 25) :
    baseState n i.val = aligned n i.val := by
  fin_cases i <;>
    simp only [baseState, aligned, ones_offset, List.append_assoc,
      List.cons_append, List.nil_append, ones_slide] <;> rfl

private theorem scan_ones (d : Counter) (h : d ≠ Counter.zero)
    (n : Nat) (u v : Word) :
    scan d (ones n ++ u) (ones n ++ v) = scan d u v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hd : d.step 1 1 = d := by
      cases d
      simp [Counter.step]
    change scan d (1 :: (ones n ++ u)) (1 :: (ones n ++ v)) = scan d u v
    simp [scan, hd, h, ih]

private theorem scan_pos_ones (n : Nat) (u v : Word) :
    scan ⟨2, -2, 0⟩ (ones n ++ u) (ones n ++ v) = scan ⟨2, -2, 0⟩ u v :=
  scan_ones _ (by decide) n u v

private theorem scan_neg_ones (n : Nat) (u v : Word) :
    scan ⟨-2, 2, 0⟩ (ones n ++ u) (ones n ++ v) = scan ⟨-2, 2, 0⟩ u v :=
  scan_ones _ (by decide) n u v

set_option linter.unusedSimpArgs false in
private theorem aligned_block (n : Nat) (i : Fin 25) :
    IsBlock (aligned n i.val) := by
  apply isBlockCheck_sound
  fin_cases i <;>
    simp only [aligned, baseState, isBlockCheck, Prod.fst, Prod.snd, List.cons_append,
      List.nil_append, List.cons_ne_nil, not_false_eq_true, decide_true, Bool.true_and] <;>
    simp (config := {decide := true}) [scan, Counter.zero, Counter.step, scan_pos_ones, scan_neg_ones]

private theorem state_block (n i : Nat) (hi : i < 50) : IsBlock (state n i) := by
  unfold state
  split <;> rename_i h
  · exact (baseState_eq_aligned n ⟨i, h⟩).symm ▸ aligned_block n ⟨i, h⟩
  · have ht : i - 25 < 25 := by omega
    have hb : IsBlock (baseState n (i - 25)) :=
      (baseState_eq_aligned n ⟨_, ht⟩).symm ▸ aligned_block n ⟨_, ht⟩
    obtain ⟨hn, hbal, hirr⟩ := hb
    refine ⟨?_, fun c => (hbal c).symm, ?_⟩
    · intro hz
      change (baseState n (i - 25)).2 = [] at hz
      apply hn
      apply List.length_eq_zero_iff.mp
      rw [Psc.Binomial.Equiv1.length_eq hbal, hz]
      rfl
    · intro j hj hjl he
      change j < (baseState n (i - 25)).2.length at hjl
      exact hirr j hj ((Psc.Binomial.Equiv1.length_eq hbal).symm ▸ hjl) (fun c => (he c).symm)

private theorem base_row_red (n : Nat) (i : Fin 25)
    (h : (baseState n i.val).1 ≠ (baseState n i.val).2) :
    (baseRow n i.val).map (state n) =
      red (subst (substitution (n + 5)) (baseState n i.val).1)
        (subst (substitution (n + 5)) (baseState n i.val).2) := by
  have hs : (state n i.val).1 ≠ (state n i.val).2 := by
    simpa only [state, ite_eq_left i.isLt] using h
  have hstate : state n i.val = baseState n i.val := ite_eq_left i.isLt
  obtain ⟨hu, hv⟩ := representative_row_tracks n i.val i.isLt hs
  rw [hstate] at hu hv
  simp only [children, ite_eq_left i.isLt] at hu hv
  exact red_unique _ (fun T hT => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hT
    exact state_block n j (base_row_lt n i.val j i.isLt hj)) hu hv

/-- The whole ordered row is the actual reduction, with repetitions. -/
theorem children_eq_red (n i : Nat) (hi : i < 50) (h : (state n i).1 ≠ (state n i).2) :
    children n i =
      red (subst (substitution (n + 5)) (state n i).1)
        (subst (substitution (n + 5)) (state n i).2) := by
  by_cases hb : i < 25
  · simpa only [children, state, ite_eq_left hb] using
      base_row_red n ⟨i, hb⟩ (by simpa only [state, ite_eq_left hb] using h)
  · have hj : i - 25 < 25 := by omega
    simp only [state, ite_eq_right hb, Prod.swap, Prod.fst, Prod.snd] at h
    rw [children, ite_eq_right hb, show state n i = (baseState n (i - 25)).swap from ite_eq_right hb]
    simp only [Prod.swap, Prod.fst, Prod.snd]
    rw [red_swap, ← base_row_red n ⟨i - 25, hj⟩ (Ne.symm h)]
    simp only [List.map_map]
    apply List.map_congr_left
    intro j hm
    exact swap_state n j (base_row_lt n (i - 25) j hj hm)

/-- Every actual ordered child remains inside the literal carrier. -/
theorem closed (n i : Nat) (hi : i < 50) {T : Pair}
    (h : ChildNC (substitution (n + 5)) (state n i) T) :
    ∃ j : Fin 50, T = state n j.val := by
  have hc := h.2
  change T ∈ red (subst (substitution (n + 5)) (state n i).1)
    (subst (substitution (n + 5)) (state n i).2) at hc
  rw [← children_eq_red n i hi h.1] at hc
  obtain ⟨j, hj, he⟩ := List.mem_map.mp hc
  by_cases hb : i < 25
  · simp only [ite_eq_left hb] at hj
    exact ⟨⟨j, base_row_lt n i j hb hj⟩, he.symm⟩
  · simp only [ite_eq_right hb] at hj
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
    exact ⟨⟨_, swapIndex_lt k (base_row_lt n (i - 25) k (by omega) hk)⟩, he.symm⟩

private theorem reached_in_carrier (n : Nat) {T : Pair}
    (h : Relation.ReflTransGen (ChildNC (substitution (n + 5))) ([0, 1], [1, 0]) T) :
    T ∈ Set.range (fun i : Fin 50 => state n i.val) := by
  induction h with
  | refl => exact ⟨1, rfl⟩
  | tail _ edge ih =>
    obtain ⟨i, rfl⟩ := ih
    obtain ⟨j, he⟩ := closed n i.val i.isLt edge
    exact ⟨j, he.symm⟩

/-- The represented words are finite for every parameter. -/
theorem finite_reachable (n : Nat) :
    {T | Relation.ReflTransGen (ChildNC (substitution (n + 5))) ([0, 1], [1, 0]) T}.Finite :=
  (Set.finite_range (fun i : Fin 50 => state n i.val)).subset fun _ => reached_in_carrier n


/-- Every noncoincident state in the symbolic carrier has an immediate diagonal child. -/
theorem coincidence_child (n i : Nat) (hi : i < 50)
    (hne : (state n i).1 ≠ (state n i).2) :
    ∃ T, ChildNC (substitution (n + 5)) (state n i) T ∧ T.1 = T.2 := by
  have hr := children_eq_red n i hi hne
  by_cases h : i < 25
  · have hn : (baseState n i).1 ≠ (baseState n i).2 := by
      simpa only [state, ite_eq_left h] using hne
    obtain ⟨j, hj, hd⟩ := base_exit n i h hn
    refine ⟨state n j, ⟨hne, ?_⟩, hd⟩
    change state n j ∈ red _ _
    rw [← hr]
    exact List.mem_map.mpr ⟨j, by simpa only [ite_eq_left h] using hj, rfl⟩
  · have hj : i - 25 < 25 := by omega
    have hn : (baseState n (i - 25)).1 ≠ (baseState n (i - 25)).2 := by
      exact Ne.symm (by simpa only [state, ite_eq_right h, Prod.swap, Prod.fst, Prod.snd] using hne)
    obtain ⟨j, hjm, hd⟩ := base_exit n (i - 25) hj hn
    refine ⟨state n (swapIndex j), ⟨hne, ?_⟩, ?_⟩
    · change state n (swapIndex j) ∈ red _ _
      rw [← hr]
      apply List.mem_map.mpr
      refine ⟨swapIndex j, ?_, rfl⟩
      simp only [ite_eq_right h]
      exact List.mem_map.mpr ⟨j, hjm, rfl⟩
    · rw [swap_state n j (base_row_lt n (i - 25) j hj hjm)]
      exact hd.symm

theorem reached_coincidence_child (n : Nat) {T : Pair}
    (h : Relation.ReflTransGen (ChildNC (substitution (n + 5))) ([0,1], [1,0]) T)
    (hne : T.1 ≠ T.2) : ∃ U, ChildNC (substitution (n + 5)) T U ∧ U.1 = U.2 := by
  obtain ⟨i, rfl⟩ := reached_in_carrier n h
  exact coincidence_child n i.val i.isLt hne

/-- Finiteness and the checked one-step coincidence exits, expressed in the
literal reachability relation. -/
theorem finite_and_productive (n : Nat) :
    {T | Relation.ReflTransGen (ChildNC (substitution (n + 5))) ([0, 1], [1, 0]) T}.Finite ∧
      ∀ T, Relation.ReflTransGen (ChildNC (substitution (n + 5))) ([0, 1], [1, 0]) T →
        ∃ U, Relation.ReflTransGen (ChildNC (substitution (n + 5))) T U ∧ U.1 = U.2 := by
  refine ⟨finite_reachable n, ?_⟩
  intro T hT
  by_cases h : T.1 = T.2
  · exact ⟨T, .refl, h⟩
  · obtain ⟨U, hTU, hU⟩ := reached_coincidence_child n hT h
    exact ⟨U, Relation.ReflTransGen.single hTU, hU⟩


end Psc.ParameterFamilyCarrier

/-! Literal boundary carriers and kernel-checked productivity ranks. -/

namespace Psc.ParameterFamilyBoundary

open Psc.Binomial Psc.Reduction Psc.Descendants Psc.FastForwardCarrier

open Psc.ParameterFamilyRows (substitution)

private structure LiteralData where
  words : Array (String × String)
  rows : Array (List Nat)
  ranks : Array Nat
  exits : Array Nat
  seed : Nat

private def state (d : LiteralData) (i : Nat) : Pair :=
  let (u, v) := d.words[i]!
  (word u, word v)

private def row (d : LiteralData) (i : Nat) : List Nat := d.rows[i]!
private def rank (d : LiteralData) (i : Nat) : Nat := d.ranks[i]!
private def exit (d : LiteralData) (i : Nat) : Nat := d.exits[i]!

private def rowCheck (d : LiteralData) (k i : Nat) : Bool :=
  let p := state d i
  isBlockCheck p &&
  if p.1 = p.2 then true else
    let r := row d i
    let children := r.map (state d)
    r.all (fun j => decide (j < d.words.size)) &&
    (((children.map Prod.fst).flatten == subst (substitution k) p.1) &&
      ((children.map Prod.snd).flatten == subst (substitution k) p.2)) &&
    (r.contains (exit d i) && decide (rank d (exit d i) < rank d i)) &&
    ((k == 2) || ((state d (exit d i)).1 == (state d (exit d i)).2))

private def checkRange (d : LiteralData) (k start count : Nat) : Bool :=
  Nat.allLTTR count (fun i _ => rowCheck d k (start + i))

private theorem joinRanges {d : LiteralData} {k start left right : Nat}
    (h₁ : checkRange d k start left = true)
    (h₂ : checkRange d k (start + left) right = true) :
    checkRange d k start (left + right) = true := by
  simp only [checkRange, Nat.allLTTR_eq_true] at *
  intro i hi
  by_cases h : i < left
  · exact h₁ i h
  · have hsub : i - left < right := by omega
    simpa only [show start + left + (i - left) = start + i by omega] using h₂ (i - left) hsub

private theorem checked_range {d : LiteralData} {k count : Nat}
    (n : count = d.words.size) (h : checkRange d k 0 count = true) :
    ∀ i < d.words.size, rowCheck d k i = true := by
  simp only [checkRange, Nat.allLTTR_eq_true, Nat.zero_add] at h
  simpa only [n] using h

private theorem checked_row {d : LiteralData} {k : Nat}
    (checks : ∀ i < d.words.size, rowCheck d k i = true)
    {i : Nat} (hi : i < d.words.size) (hne : (state d i).1 ≠ (state d i).2) :
    ((row d i).map (state d) =
      red (subst (substitution k) (state d i).1) (subst (substitution k) (state d i).2)) ∧
    (∀ j ∈ row d i, j < d.words.size) ∧
    (exit d i ∈ row d i ∧ rank d (exit d i) < rank d i) ∧
    (k = 2 ∨ (state d (exit d i)).1 = (state d (exit d i)).2) := by
  have h := checks i hi
  simp only [rowCheck, ite_eq_right hne, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    beq_iff_eq, List.contains_iff_mem, Bool.or_eq_true] at h
  obtain ⟨_, ⟨⟨hj, ht, hb⟩, he, hr⟩, hdiag⟩ := h
  refine ⟨red_unique _ ?_ ht hb, hj, ⟨he, hr⟩, hdiag⟩
  intro T hT
  obtain ⟨j, hm, rfl⟩ := List.mem_map.mp hT
  apply isBlockCheck_sound
  exact (Bool.and_eq_true_iff.mp (checks j (hj j hm))).1

private theorem checked_child {d : LiteralData} {k i : Nat}
    (checks : ∀ j < d.words.size, rowCheck d k j = true)
    (hi : i < d.words.size) {T : Pair} (edge : ChildNC (substitution k) (state d i) T) :
    ∃ j < d.words.size, state d j = T := by
  obtain ⟨hr, hj, _⟩ := checked_row checks hi edge.1
  have hm := edge.2
  change T ∈ red (subst (substitution k) (state d i).1)
    (subst (substitution k) (state d i).2) at hm
  rw [← hr] at hm
  obtain ⟨j, hjmem, hT⟩ := List.mem_map.mp hm
  exact ⟨j, hj j hjmem, hT⟩

private theorem checked_reachable {d : LiteralData} {k : Nat}
    (checks : ∀ j < d.words.size, rowCheck d k j = true)
    (hs : d.seed < d.words.size) (hseed : state d d.seed = ([0, 1], [1, 0]))
    {T : Pair} (hT : Relation.ReflTransGen (ChildNC (substitution k)) ([0, 1], [1, 0]) T) :
    ∃ j < d.words.size, state d j = T := by
  induction hT with
  | refl => exact ⟨d.seed, hs, hseed⟩
  | tail _ edge ih =>
    obtain ⟨i, hi, rfl⟩ := ih
    exact checked_child checks hi edge

private theorem checked_productive {d : LiteralData} {k : Nat}
    (checks : ∀ j < d.words.size, rowCheck d k j = true)
    (i : Nat) (hi : i < d.words.size) :
    ∃ U, Relation.ReflTransGen (ChildNC (substitution k)) (state d i) U ∧ U.1 = U.2 := by
  by_cases h : (state d i).1 = (state d i).2
  · exact ⟨state d i, .refl, h⟩
  · obtain ⟨hr, hj, ⟨he, _⟩, _⟩ := checked_row checks hi h
    obtain ⟨U, hpath, hU⟩ := checked_productive checks (exit d i) (hj _ he)
    have edge : ChildNC (substitution k) (state d i) (state d (exit d i)) := by
      refine ⟨h, ?_⟩
      change state d (exit d i) ∈ red _ _
      rw [← hr]
      exact List.mem_map.mpr ⟨_, he, rfl⟩
    exact ⟨U, (Relation.ReflTransGen.single edge).trans hpath, hU⟩
termination_by rank d i
decreasing_by exact (checked_row checks hi h).2.2.1.2

private theorem checked_termination {d : LiteralData} {k : Nat}
    (checks : ∀ j < d.words.size, rowCheck d k j = true)
    (hs : d.seed < d.words.size) (hseed : state d d.seed = ([0, 1], [1, 0])) :
    {T | Relation.ReflTransGen (ChildNC (substitution k)) ([0, 1], [1, 0]) T}.Finite ∧
      ∀ T, Relation.ReflTransGen (ChildNC (substitution k)) ([0, 1], [1, 0]) T →
        ∃ U, Relation.ReflTransGen (ChildNC (substitution k)) T U ∧ U.1 = U.2 := by
  constructor
  · apply (Set.finite_range (fun j : Fin d.words.size => state d j.val)).subset
    intro T hT
    obtain ⟨j, hj, he⟩ := checked_reachable checks hs hseed hT
    exact ⟨⟨j, hj⟩, he⟩
  · intro T hT
    obtain ⟨j, hj, rfl⟩ := checked_reachable checks hs hseed hT
    exact checked_productive checks j hj

private def data2 : LiteralData where
  words := #[
    ("0", "0"), ("001011210112", "110112011200"), ("001101120112", "110112011200"),
    ("0011101120112", "1101120112001"), ("00111011201120112", "10112101120112001"), ("0011101120112101120", "1011210112011200101"),
    ("0011101120112101120112", "1011201121011201120011"), ("00111011201121011201120011011201120011101120112101120", "11101120112011210112011200110112011200110112011200101"), ("00111011201121011201120011011201120011101121011201120", "11101120112011210112011200110112011200110112011200101"),
    ("00111011210112", "11011201120011"), ("01", "10"), ("010112", "112001"),
    ("010112", "200111"), ("01011210", "20011011"), ("01011210112", "11201120011"),
    ("010112101120", "112011200101"), ("010112101120112", "121011201120011"), ("011", "110"),
    ("0110112", "1120011"), ("01101120", "11200101"), ("01101120", "20011011"),
    ("01101120112", "11201120011"), ("011011201120", "112011200101"), ("011011201120011101120112011210", "121011201120011011201120011011"),
    ("0110112011200111011201120112101120", "1210112011200110112011200101121011"), ("011101120", "112001011"), ("011101120", "112001101"),
    ("011101120112", "112011200111"), ("0111011201120", "1120112001101"), ("01110112011210", "11201120011011"),
    ("0111011210", "1120011011"), ("01110112101120", "11200101121011"), ("01110112101120", "11201120011011"),
    ("01110112101120", "11201120011101"), ("0112011200111011201121", "1110112011210112011200"), ("01120112001110112011210112", "11101120112011210112011200"),
    ("01120112001110112101120112", "11101120112011210112011200"), ("1", "1"), ("10", "01"),
    ("1011201121011201120011", "0011101120112101120112"), ("10112101120112001", "00111011201120112"), ("1011210112011200101", "0011101120112101120"),
    ("110", "011"), ("110112011200", "001011210112"), ("110112011200", "001101120112"),
    ("1101120112001", "0011101120112"), ("11011201120011", "00111011210112"), ("11101120112011210112011200", "01120112001110112011210112"),
    ("11101120112011210112011200", "01120112001110112101120112"), ("11101120112011210112011200110112011200110112011200101", "00111011201121011201120011011201120011101120112101120"), ("11101120112011210112011200110112011200110112011200101", "00111011201121011201120011011201120011101121011201120"),
    ("1110112011210112011200", "0112011200111011201121"), ("1120", "2011"), ("1120", "2101"),
    ("11200", "20011"), ("112001", "010112"), ("1120010", "2001011"),
    ("11200101", "01101120"), ("112001011", "011101120"), ("11200101121011", "01110112101120"),
    ("1120011", "0110112"), ("112001101", "011101120"), ("1120011011", "0111011210"),
    ("112001101120", "200101121011"), ("112011200", "200101121"), ("112011200", "200110112"),
    ("1120112001", "2001110112"), ("112011200101", "010112101120"), ("112011200101", "011011201120"),
    ("11201120011", "01011210112"), ("11201120011", "01101120112"), ("1120112001101", "0111011201120"),
    ("11201120011011", "01110112011210"), ("11201120011011", "01110112101120"), ("112011200111", "011101120112"),
    ("11201120011101", "01110112101120"), ("11210", "21011"), ("112101120", "201121011"),
    ("12", "21"), ("120", "201"), ("12011210112011200", "20010112101120112"),
    ("12011210112011200101", "20011101120112101120"), ("12011210112011200101", "20011101121011201120"), ("12011210112011200101121011201120011", "20011011201120011101120112011210112"),
    ("12011210112011200101121011201120011", "20011011201120011101120112101120112"), ("1201121011201120011", "2001110112011210112"), ("1201121011201120011", "2001110112101120112"),
    ("120112101120112001101120112001", "200110112011200111011201120112"), ("12011210112011200110112011200101", "20011011201120011101120112101120"), ("1201121011201120011011201120011", "2001101120112001110112011210112"),
    ("1210", "2011"), ("1210112011200", "2001011210112"), ("1210112011200", "2001101120112"),
    ("12101120112001", "20011101120112"), ("121011201120011", "010112101120112"), ("121011201120011", "200111011210112"),
    ("1210112011200110112011200101121011", "0110112011200111011201120112101120"), ("121011201120011011201120011011", "011011201120011101120112011210"), ("2001011", "1120010"),
    ("200101121", "112011200"), ("200101121011", "112001101120"), ("2001011210112", "1210112011200"),
    ("20010112101120112", "12011210112011200"), ("20011", "11200"), ("20011011", "01011210"),
    ("20011011", "01101120"), ("200110112", "112011200"), ("2001101120112", "1210112011200"),
    ("200110112011200111011201120112", "120112101120112001101120112001"), ("20011011201120011101120112011210112", "12011210112011200101121011201120011"), ("2001101120112001110112011210112", "1201121011201120011011201120011"),
    ("20011011201120011101120112101120", "12011210112011200110112011200101"), ("20011011201120011101120112101120112", "12011210112011200101121011201120011"), ("200111", "010112"),
    ("2001110112", "1120112001"), ("20011101120112", "12101120112001"), ("2001110112011210112", "1201121011201120011"),
    ("20011101120112101120", "12011210112011200101"), ("200111011210112", "121011201120011"), ("2001110112101120112", "1201121011201120011"),
    ("20011101121011201120", "12011210112011200101"), ("201", "120"), ("2011", "1120"),
    ("2011", "1210"), ("201121011", "112101120"), ("21", "12"),
    ("2101", "1120"), ("21011", "11210")
  ]
  rows := #[
    [], [42, 77, 52, 13, 52, 54, 37], [42, 52, 76, 52, 54, 42, 52, 54, 37],
    [42, 52, 53, 37, 90, 65, 42, 66], [42, 53, 37, 79, 37, 91, 42, 65, 42, 66], [42, 53, 37, 79, 37, 91, 42, 65, 38, 37, 95],
    [42, 53, 37, 79, 37, 92, 43, 38, 37, 92, 45], [42, 52, 52, 76, 52, 54, 42, 52, 54, 38, 37, 90, 64, 42, 52, 54, 51, 42, 52, 54, 47, 42, 65, 38, 37, 95], [42, 52, 52, 76, 52, 54, 42, 52, 54, 38, 37, 90, 64, 42, 52, 54, 51, 42, 52, 54, 47, 38, 37, 92, 46],
    [42, 52, 53, 37, 90, 65, 38, 37, 93], [38, 37, 78], [38, 37, 90, 66],
    [40], [41, 37, 125], [38, 37, 90, 65, 38, 37, 93],
    [38, 37, 90, 65, 38, 37, 95], [38, 37, 91, 38, 37, 92, 45], [38, 37, 79, 37, 78],
    [38, 37, 79, 37, 93], [38, 37, 79, 37, 95], [39],
    [38, 37, 79, 37, 92, 45], [38, 37, 79, 37, 92, 46], [38, 37, 80, 44, 49, 37, 125],
    [38, 37, 80, 44, 50, 94], [38, 37, 79, 37, 86], [38, 37, 79, 37, 85],
    [38, 37, 79, 37, 87], [38, 37, 79, 37, 89], [38, 37, 79, 37, 88, 37, 125],
    [38, 37, 79, 37, 81, 37, 125], [38, 37, 79, 37, 82, 94], [38, 37, 79, 37, 84],
    [38, 37, 79, 37, 83], [38, 37, 79, 37, 79, 24, 52, 20, 52, 12], [38, 37, 79, 37, 79, 23, 52, 63, 52, 13, 52, 54, 37],
    [38, 37, 79, 37, 79, 23, 52, 56, 76, 52, 54, 42, 52, 54, 37], [], [10, 37, 125],
    [17, 126, 37, 121, 37, 107, 1, 10, 37, 107, 3], [17, 126, 37, 121, 37, 101, 17, 106, 17, 114], [17, 126, 37, 121, 37, 101, 17, 106, 10, 37, 118],
    [10, 37, 121, 37, 125], [17, 124, 122, 104, 122, 103, 37], [17, 122, 127, 122, 103, 17, 122, 103, 37],
    [17, 122, 126, 37, 123, 106, 17, 114], [17, 122, 126, 37, 123, 106, 10, 37, 115], [10, 37, 121, 37, 121, 97, 122, 100, 122, 104, 122, 103, 37],
    [10, 37, 121, 37, 121, 97, 122, 98, 127, 122, 103, 17, 122, 103, 37], [17, 122, 122, 127, 122, 103, 17, 122, 103, 10, 37, 123, 99, 17, 122, 103, 34, 17, 122, 103, 35, 17, 106, 10, 37, 118], [17, 122, 122, 127, 122, 103, 17, 122, 103, 10, 37, 123, 99, 17, 122, 103, 34, 17, 122, 103, 35, 10, 37, 107, 9],
    [10, 37, 121, 37, 121, 96, 122, 105, 122, 113], [0, 70], [0, 69],
    [0, 74], [10, 37, 123, 114], [0, 75, 37, 125],
    [10, 37, 121, 37, 118], [10, 37, 121, 37, 119], [10, 37, 121, 37, 120, 16],
    [10, 37, 121, 37, 115], [10, 37, 121, 37, 116], [10, 37, 121, 37, 117, 37, 78],
    [0, 75, 37, 121, 94], [0, 73, 122, 113], [0, 72, 122, 103, 37],
    [0, 71, 37, 123, 114], [10, 37, 123, 106, 10, 37, 118], [10, 37, 121, 37, 107, 9],
    [10, 37, 123, 106, 10, 37, 115], [10, 37, 121, 37, 107, 3], [10, 37, 121, 37, 110],
    [10, 37, 121, 37, 111, 37, 78], [10, 37, 121, 37, 112], [10, 37, 121, 37, 108],
    [10, 37, 121, 37, 109], [0, 67, 37, 125], [0, 68, 94],
    [0, 55], [0, 60], [0, 62, 122, 98, 127, 122, 103, 17, 122, 103, 37],
    [0, 61, 37, 121, 37, 101, 17, 106, 10, 37, 118], [0, 61, 37, 121, 37, 101, 10, 37, 107, 9], [0, 61, 37, 123, 99, 17, 122, 103, 36, 1, 17, 106, 10, 37, 115],
    [0, 61, 37, 123, 99, 17, 122, 103, 36, 1, 10, 37, 107, 3], [0, 61, 37, 121, 37, 101, 17, 106, 10, 37, 115], [0, 61, 37, 121, 37, 101, 10, 37, 107, 3],
    [0, 61, 37, 123, 99, 17, 122, 103, 35, 17, 106, 17, 114], [0, 61, 37, 123, 99, 17, 122, 103, 35, 17, 106, 10, 37, 118], [0, 61, 37, 123, 99, 17, 122, 103, 35, 17, 106, 10, 37, 115],
    [0, 57, 37, 125], [0, 59, 122, 104, 122, 103, 37], [0, 58, 127, 122, 103, 17, 122, 103, 37],
    [0, 58, 126, 37, 123, 106, 17, 114], [10, 37, 101, 10, 37, 107, 3], [0, 58, 126, 37, 123, 106, 10, 37, 115],
    [10, 37, 102, 2, 8, 16], [10, 37, 102, 2, 7, 37, 78], [0, 33, 37, 78],
    [0, 32, 52, 12], [0, 33, 37, 79, 16], [0, 31, 52, 13, 52, 54, 37],
    [0, 30, 52, 56, 76, 52, 54, 42, 52, 54, 37], [0, 27], [5, 37, 78],
    [6], [0, 29, 52, 54, 37], [0, 25, 76, 52, 54, 42, 52, 54, 37],
    [0, 26, 37, 90, 64, 42, 52, 54, 47, 42, 65, 42, 66], [0, 26, 37, 90, 64, 42, 52, 54, 48, 43, 42, 65, 38, 37, 93], [0, 26, 37, 90, 64, 42, 52, 54, 47, 42, 65, 38, 37, 93],
    [0, 26, 37, 90, 64, 42, 52, 54, 47, 42, 65, 38, 37, 95], [0, 26, 37, 90, 64, 42, 52, 54, 48, 43, 38, 37, 92, 45], [4],
    [0, 28, 37, 90, 66], [0, 25, 53, 37, 90, 65, 42, 66], [0, 26, 37, 79, 37, 91, 42, 65, 38, 37, 93],
    [0, 26, 37, 79, 37, 91, 42, 65, 38, 37, 95], [0, 25, 53, 37, 90, 65, 38, 37, 93], [0, 26, 37, 79, 37, 91, 38, 37, 92, 45],
    [0, 26, 37, 79, 37, 91, 38, 37, 92, 46], [0, 18], [0, 21],
    [0, 19, 37, 78], [0, 22, 16], [0, 11],
    [0, 14], [0, 15, 37, 78]
  ]
  ranks := #[0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  exits := #[0, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 40, 37, 37, 37, 37, 37, 37, 37, 39, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 0, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 0, 0, 0, 37, 0, 37, 37, 37, 37, 37, 37, 0, 0, 0, 0, 37, 37, 37, 37, 37, 37, 37, 37, 37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37, 0, 37, 37, 0, 0, 0, 0, 0, 0, 37, 6, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  seed := 10

private def data3 : LiteralData where
  words := #[
    ("0", "0"), ("00111011120111201112", "11011120111201112001"), ("001110111201112101112", "110111201112011120011"),
    ("0011101112011121011120", "1101112011120111200101"), ("01", "10"), ("0101112", "1112001"),
    ("0101112101112", "1112011120011"), ("01011121011120", "11120111200101"), ("011", "110"),
    ("01101112", "11120011"), ("011011120", "111200101"), ("0110111201112", "1112011120011"),
    ("0111011120", "1112001011"), ("01110111201112", "11120111200111"), ("011101112011120", "111201112001101"),
    ("0111011120111210", "1112011120011011"), ("1", "1"), ("10", "01"),
    ("110", "011"), ("11011120111201112001", "00111011120111201112"), ("1101112011120111200101", "0011101112011121011120"),
    ("110111201112011120011", "001110111201112101112"), ("1112001", "0101112"), ("111200101", "011011120"),
    ("1112001011", "0111011120"), ("11120011", "01101112"), ("11120111200101", "01011121011120"),
    ("1112011120011", "0101112101112"), ("1112011120011", "0110111201112"), ("111201112001101", "011101112011120"),
    ("1112011120011011", "0111011120111210"), ("11120111200111", "01110111201112"), ("1120", "2011"),
    ("1120", "2101"), ("11200", "20011"), ("1120111200", "2001101112"),
    ("11201112001", "20011101112"), ("112011120111200", "200110111201112"), ("1120111201112001", "2001110111201112"),
    ("11201112011120011", "20011101112101112"), ("11210", "21011"), ("12", "21"),
    ("120", "201"), ("1210", "2011"), ("12101112011120111200", "20011011120111201112"),
    ("1210111201112011120011", "2001110111210111201112"), ("20011", "11200"), ("2001101112", "1120111200"),
    ("200110111201112", "112011120111200"), ("20011011120111201112", "12101112011120111200"), ("20011101112", "11201112001"),
    ("2001110111201112", "1120111201112001"), ("20011101112101112", "11201112011120011"), ("2001110111210111201112", "1210111201112011120011"),
    ("201", "120"), ("2011", "1120"), ("2011", "1210"),
    ("21", "12"), ("2101", "1120"), ("21011", "11210")
  ]
  rows := #[
    [], [18, 16, 32, 16, 33, 16, 16, 43, 16, 32, 16, 35, 18, 16, 32, 16, 35, 18, 16, 32, 16, 36], [18, 16, 32, 16, 33, 16, 16, 43, 16, 32, 16, 35, 18, 16, 32, 16, 35, 17, 16, 16, 43, 16, 38],
    [18, 16, 32, 16, 33, 16, 16, 43, 16, 32, 16, 35, 18, 16, 32, 16, 35, 17, 16, 16, 43, 16, 39], [17, 16, 16, 41], [17, 16, 16, 43, 16, 32, 16, 36],
    [17, 16, 16, 43, 16, 32, 16, 35, 17, 16, 16, 43, 16, 38], [17, 16, 16, 43, 16, 32, 16, 35, 17, 16, 16, 43, 16, 39], [17, 16, 16, 42, 16, 16, 41],
    [17, 16, 16, 42, 16, 16, 43, 16, 38], [17, 16, 16, 42, 16, 16, 43, 16, 39], [17, 16, 16, 42, 16, 16, 43, 16, 37, 18, 16, 38],
    [17, 16, 16, 42, 16, 16, 42, 16, 16, 45], [17, 16, 16, 42, 16, 16, 42, 16, 16, 44, 19], [17, 16, 16, 42, 16, 16, 42, 16, 16, 44, 21],
    [17, 16, 16, 42, 16, 16, 42, 16, 16, 44, 20, 16, 16, 57], [], [4, 16, 16, 57],
    [4, 16, 16, 54, 16, 16, 57], [8, 16, 55, 16, 58, 16, 16, 56, 16, 55, 16, 47, 8, 16, 55, 16, 47, 8, 16, 55, 16, 50], [8, 16, 55, 16, 58, 16, 16, 56, 16, 55, 16, 47, 8, 16, 55, 16, 47, 4, 16, 16, 56, 16, 52],
    [8, 16, 55, 16, 58, 16, 16, 56, 16, 55, 16, 47, 8, 16, 55, 16, 47, 4, 16, 16, 56, 16, 51], [4, 16, 16, 56, 16, 55, 16, 50], [4, 16, 16, 54, 16, 16, 56, 16, 52],
    [4, 16, 16, 54, 16, 16, 54, 16, 16, 53], [4, 16, 16, 54, 16, 16, 56, 16, 51], [4, 16, 16, 56, 16, 55, 16, 47, 4, 16, 16, 56, 16, 52],
    [4, 16, 16, 56, 16, 55, 16, 47, 4, 16, 16, 56, 16, 51], [4, 16, 16, 54, 16, 16, 56, 16, 48, 8, 16, 51], [4, 16, 16, 54, 16, 16, 54, 16, 16, 49, 2],
    [4, 16, 16, 54, 16, 16, 54, 16, 16, 49, 3, 16, 16, 41], [4, 16, 16, 54, 16, 16, 54, 16, 16, 49, 1], [0, 28],
    [0, 27], [0, 31], [0, 30, 16, 55, 16, 55, 16, 46, 16],
    [0, 29, 16, 16, 56, 16, 55, 16, 50], [0, 30, 16, 55, 16, 55, 16, 46, 8, 16, 55, 16, 55, 16, 46, 16], [0, 29, 16, 16, 56, 16, 55, 16, 47, 8, 16, 55, 16, 50],
    [0, 29, 16, 16, 56, 16, 55, 16, 47, 4, 16, 16, 56, 16, 51], [0, 26, 16, 16, 57], [0, 22],
    [0, 25], [0, 23, 16, 16, 57], [0, 24, 16, 59, 16, 55, 16, 55, 16, 46, 8, 16, 55, 16, 55, 16, 46, 8, 16, 55, 16, 55, 16, 46, 16],
    [0, 24, 16, 58, 16, 16, 56, 16, 55, 16, 47, 4, 16, 16, 56, 16, 48, 8, 16, 51], [0, 13], [0, 15, 16, 32, 16, 32, 16, 34, 16],
    [0, 15, 16, 32, 16, 32, 16, 34, 18, 16, 32, 16, 32, 16, 34, 16], [0, 12, 16, 40, 16, 32, 16, 32, 16, 34, 18, 16, 32, 16, 32, 16, 34, 18, 16, 32, 16, 32, 16, 34, 16], [0, 14, 16, 16, 43, 16, 32, 16, 36],
    [0, 14, 16, 16, 43, 16, 32, 16, 35, 18, 16, 32, 16, 36], [0, 14, 16, 16, 43, 16, 32, 16, 35, 17, 16, 16, 43, 16, 38], [0, 12, 16, 33, 16, 16, 43, 16, 32, 16, 35, 17, 16, 16, 43, 16, 37, 18, 16, 38],
    [0, 9], [0, 11], [0, 10, 16, 16, 41],
    [0, 5], [0, 6], [0, 7, 16, 16, 41]
  ]
  ranks := #[0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  exits := #[0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  seed := 4

private def data4 : LiteralData where
  words := #[
    ("0", "0"), ("01", "10"), ("01011112", "11112001"),
    ("011", "110"), ("011011112", "111120011"), ("0110111120", "1111200101"),
    ("011011112011112", "111120111120011"), ("0111011112011112", "1111201111200111"), ("01110111120111120", "11112011112001101"),
    ("011101111201111210", "111120111120011011"), ("1", "1"), ("10", "01"),
    ("110", "011"), ("11112001", "01011112"), ("1111200101", "0110111120"),
    ("111120011", "011011112"), ("111120111120011", "011011112011112"), ("11112011112001101", "01110111120111120"),
    ("111120111120011011", "011101111201111210"), ("1111201111200111", "0111011112011112"), ("1120", "2011"),
    ("11200", "20011"), ("11201111200", "20011011112"), ("112011112001", "200111011112"),
    ("11201111201111200", "20011011112011112"), ("112011112011112001", "200111011112011112"), ("1120111120111120011", "2001110111121011112"),
    ("11201111201111201111200", "20011011112011112011112"), ("112011112011112011112001", "200111011112011112011112"), ("11201111201111201111200101", "20011101111201111210111120"),
    ("1120111120111120111120011", "2001110111120111121011112"), ("12", "21"), ("120", "201"),
    ("1210", "2011"), ("20011", "11200"), ("20011011112", "11201111200"),
    ("20011011112011112", "11201111201111200"), ("20011011112011112011112", "11201111201111201111200"), ("200111011112", "112011112001"),
    ("200111011112011112", "112011112011112001"), ("200111011112011112011112", "112011112011112011112001"), ("2001110111120111121011112", "1120111120111120111120011"),
    ("20011101111201111210111120", "11201111201111201111200101"), ("2001110111121011112", "1120111120111120011"), ("201", "120"),
    ("2011", "1120"), ("2011", "1210"), ("21", "12")
  ]
  rows := #[
    [], [11, 10, 10, 10, 31], [11, 10, 10, 10, 33, 10, 10, 20, 10, 10, 20, 10, 10, 23],
    [11, 10, 10, 10, 32, 10, 10, 10, 31], [11, 10, 10, 10, 32, 10, 10, 10, 33, 10, 10, 20, 10, 10, 25], [11, 10, 10, 10, 32, 10, 10, 10, 33, 10, 10, 20, 10, 10, 26],
    [11, 10, 10, 10, 32, 10, 10, 10, 33, 10, 10, 20, 10, 10, 24, 12, 10, 10, 20, 10, 10, 25], [11, 10, 10, 10, 32, 10, 10, 10, 32, 10, 10, 10, 33, 10, 10, 27, 12, 10, 10, 28], [11, 10, 10, 10, 32, 10, 10, 10, 32, 10, 10, 10, 33, 10, 10, 27, 12, 10, 10, 30],
    [11, 10, 10, 10, 32, 10, 10, 10, 32, 10, 10, 10, 33, 10, 10, 27, 12, 10, 10, 29, 10, 10, 10, 47], [], [1, 10, 10, 10, 47],
    [1, 10, 10, 10, 44, 10, 10, 10, 47], [1, 10, 10, 10, 46, 10, 10, 45, 10, 10, 45, 10, 10, 38], [1, 10, 10, 10, 44, 10, 10, 10, 46, 10, 10, 45, 10, 10, 43],
    [1, 10, 10, 10, 44, 10, 10, 10, 46, 10, 10, 45, 10, 10, 39], [1, 10, 10, 10, 44, 10, 10, 10, 46, 10, 10, 45, 10, 10, 36, 3, 10, 10, 45, 10, 10, 39], [1, 10, 10, 10, 44, 10, 10, 10, 44, 10, 10, 10, 46, 10, 10, 37, 3, 10, 10, 41],
    [1, 10, 10, 10, 44, 10, 10, 10, 44, 10, 10, 10, 46, 10, 10, 37, 3, 10, 10, 42, 10, 10, 10, 31], [1, 10, 10, 10, 44, 10, 10, 10, 44, 10, 10, 10, 46, 10, 10, 37, 3, 10, 10, 40], [0, 16],
    [0, 19], [0, 18, 10, 10, 45, 10, 10, 45, 10, 10, 45, 10, 10, 34, 10], [0, 17, 10, 10, 10, 46, 10, 10, 45, 10, 10, 45, 10, 10, 38],
    [0, 18, 10, 10, 45, 10, 10, 45, 10, 10, 45, 10, 10, 34, 3, 10, 10, 45, 10, 10, 45, 10, 10, 45, 10, 10, 34, 10], [0, 17, 10, 10, 10, 46, 10, 10, 45, 10, 10, 45, 10, 10, 35, 3, 10, 10, 45, 10, 10, 45, 10, 10, 38], [0, 17, 10, 10, 10, 46, 10, 10, 45, 10, 10, 45, 10, 10, 35, 1, 10, 10, 10, 46, 10, 10, 45, 10, 10, 39],
    [0, 18, 10, 10, 45, 10, 10, 45, 10, 10, 45, 10, 10, 34, 3, 10, 10, 45, 10, 10, 45, 10, 10, 45, 10, 10, 34, 3, 10, 10, 45, 10, 10, 45, 10, 10, 45, 10, 10, 34, 10], [0, 17, 10, 10, 10, 46, 10, 10, 45, 10, 10, 45, 10, 10, 35, 3, 10, 10, 45, 10, 10, 45, 10, 10, 35, 3, 10, 10, 45, 10, 10, 45, 10, 10, 38], [0, 17, 10, 10, 10, 46, 10, 10, 45, 10, 10, 45, 10, 10, 35, 3, 10, 10, 45, 10, 10, 45, 10, 10, 35, 1, 10, 10, 10, 46, 10, 10, 45, 10, 10, 43],
    [0, 17, 10, 10, 10, 46, 10, 10, 45, 10, 10, 45, 10, 10, 35, 3, 10, 10, 45, 10, 10, 45, 10, 10, 35, 1, 10, 10, 10, 46, 10, 10, 45, 10, 10, 39], [0, 13], [0, 15],
    [0, 14, 10, 10, 10, 47], [0, 7], [0, 9, 10, 10, 20, 10, 10, 20, 10, 10, 20, 10, 10, 21, 10],
    [0, 9, 10, 10, 20, 10, 10, 20, 10, 10, 20, 10, 10, 21, 12, 10, 10, 20, 10, 10, 20, 10, 10, 20, 10, 10, 21, 10], [0, 9, 10, 10, 20, 10, 10, 20, 10, 10, 20, 10, 10, 21, 12, 10, 10, 20, 10, 10, 20, 10, 10, 20, 10, 10, 21, 12, 10, 10, 20, 10, 10, 20, 10, 10, 20, 10, 10, 21, 10], [0, 8, 10, 10, 10, 33, 10, 10, 20, 10, 10, 20, 10, 10, 23],
    [0, 8, 10, 10, 10, 33, 10, 10, 20, 10, 10, 20, 10, 10, 22, 12, 10, 10, 20, 10, 10, 20, 10, 10, 23], [0, 8, 10, 10, 10, 33, 10, 10, 20, 10, 10, 20, 10, 10, 22, 12, 10, 10, 20, 10, 10, 20, 10, 10, 22, 12, 10, 10, 20, 10, 10, 20, 10, 10, 23], [0, 8, 10, 10, 10, 33, 10, 10, 20, 10, 10, 20, 10, 10, 22, 12, 10, 10, 20, 10, 10, 20, 10, 10, 22, 11, 10, 10, 10, 33, 10, 10, 20, 10, 10, 25],
    [0, 8, 10, 10, 10, 33, 10, 10, 20, 10, 10, 20, 10, 10, 22, 12, 10, 10, 20, 10, 10, 20, 10, 10, 22, 11, 10, 10, 10, 33, 10, 10, 20, 10, 10, 26], [0, 8, 10, 10, 10, 33, 10, 10, 20, 10, 10, 20, 10, 10, 22, 11, 10, 10, 10, 33, 10, 10, 20, 10, 10, 25], [0, 4],
    [0, 6], [0, 5, 10, 10, 10, 31], [0, 2]
  ]
  ranks := #[0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  exits := #[0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  seed := 1


set_option maxRecDepth 8192
set_option maxHeartbeats 0

private theorem range2_0 : checkRange data2 2 0 8 = true := by decide +kernel
private theorem range2_8 : checkRange data2 2 8 8 = true := by decide +kernel
private theorem range2_16 : checkRange data2 2 16 8 = true := by decide +kernel
private theorem range2_24 : checkRange data2 2 24 8 = true := by decide +kernel
private theorem range2_32 : checkRange data2 2 32 8 = true := by decide +kernel
private theorem range2_40 : checkRange data2 2 40 8 = true := by decide +kernel
private theorem range2_48 : checkRange data2 2 48 8 = true := by decide +kernel
private theorem range2_56 : checkRange data2 2 56 8 = true := by decide +kernel
private theorem range2_64 : checkRange data2 2 64 8 = true := by decide +kernel
private theorem range2_72 : checkRange data2 2 72 8 = true := by decide +kernel
private theorem range2_80 : checkRange data2 2 80 8 = true := by decide +kernel
private theorem range2_88 : checkRange data2 2 88 8 = true := by decide +kernel
private theorem range2_96 : checkRange data2 2 96 8 = true := by decide +kernel
private theorem range2_104 : checkRange data2 2 104 8 = true := by decide +kernel
private theorem range2_112 : checkRange data2 2 112 8 = true := by decide +kernel
private theorem range2_120 : checkRange data2 2 120 8 = true := by decide +kernel

private theorem checks2 : ∀ i < data2.words.size, rowCheck data2 2 i = true :=
  checked_range (count := 128) rfl (joinRanges range2_0 (joinRanges range2_8 (joinRanges range2_16 (joinRanges range2_24 (joinRanges range2_32 (joinRanges range2_40 (joinRanges range2_48 (joinRanges range2_56 (joinRanges range2_64 (joinRanges range2_72 (joinRanges range2_80 (joinRanges range2_88 (joinRanges range2_96 (joinRanges range2_104 (joinRanges range2_112 range2_120)))))))))))))))

theorem finite_and_productive_2 :
    {T | Relation.ReflTransGen (ChildNC (substitution 2)) ([0, 1], [1, 0]) T}.Finite ∧
      ∀ T, Relation.ReflTransGen (ChildNC (substitution 2)) ([0, 1], [1, 0]) T →
        ∃ U, Relation.ReflTransGen (ChildNC (substitution 2)) T U ∧ U.1 = U.2 :=
  checked_termination checks2 (by decide +kernel) (by decide +kernel)


set_option maxRecDepth 8192
set_option maxHeartbeats 0

private theorem range3_0 : checkRange data3 3 0 8 = true := by decide +kernel
private theorem range3_8 : checkRange data3 3 8 8 = true := by decide +kernel
private theorem range3_16 : checkRange data3 3 16 8 = true := by decide +kernel
private theorem range3_24 : checkRange data3 3 24 8 = true := by decide +kernel
private theorem range3_32 : checkRange data3 3 32 8 = true := by decide +kernel
private theorem range3_40 : checkRange data3 3 40 8 = true := by decide +kernel
private theorem range3_48 : checkRange data3 3 48 8 = true := by decide +kernel
private theorem range3_56 : checkRange data3 3 56 4 = true := by decide +kernel

private theorem checks3 : ∀ i < data3.words.size, rowCheck data3 3 i = true :=
  checked_range (count := 60) rfl (joinRanges range3_0 (joinRanges range3_8 (joinRanges range3_16 (joinRanges range3_24 (joinRanges range3_32 (joinRanges range3_40 (joinRanges range3_48 range3_56)))))))

theorem finite_and_productive_3 :
    {T | Relation.ReflTransGen (ChildNC (substitution 3)) ([0, 1], [1, 0]) T}.Finite ∧
      ∀ T, Relation.ReflTransGen (ChildNC (substitution 3)) ([0, 1], [1, 0]) T →
        ∃ U, Relation.ReflTransGen (ChildNC (substitution 3)) T U ∧ U.1 = U.2 :=
  checked_termination checks3 (by decide +kernel) (by decide +kernel)

theorem reached_coincidence_child_3 {T : Pair}
    (hT : Relation.ReflTransGen (ChildNC (substitution 3)) ([0, 1], [1, 0]) T)
    (hne : T.1 ≠ T.2) : ∃ U, ChildNC (substitution 3) T U ∧ U.1 = U.2 := by
  obtain ⟨i, hi, rfl⟩ := checked_reachable checks3 (by decide +kernel)
    (by decide +kernel) hT
  obtain ⟨hr, _, ⟨he, _⟩, hd⟩ := checked_row checks3 hi hne
  refine ⟨state data3 (exit data3 i), ⟨hne, ?_⟩, hd.resolve_left (by decide)⟩
  change state data3 (exit data3 i) ∈ red _ _
  rw [← hr]
  exact List.mem_map.mpr ⟨_, he, rfl⟩


set_option maxRecDepth 8192
set_option maxHeartbeats 0

private theorem range4_0 : checkRange data4 4 0 8 = true := by decide +kernel
private theorem range4_8 : checkRange data4 4 8 8 = true := by decide +kernel
private theorem range4_16 : checkRange data4 4 16 8 = true := by decide +kernel
private theorem range4_24 : checkRange data4 4 24 8 = true := by decide +kernel
private theorem range4_32 : checkRange data4 4 32 8 = true := by decide +kernel
private theorem range4_40 : checkRange data4 4 40 8 = true := by decide +kernel

private theorem checks4 : ∀ i < data4.words.size, rowCheck data4 4 i = true :=
  checked_range (count := 48) rfl (joinRanges range4_0 (joinRanges range4_8 (joinRanges range4_16 (joinRanges range4_24 (joinRanges range4_32 range4_40)))))

theorem finite_and_productive_4 :
    {T | Relation.ReflTransGen (ChildNC (substitution 4)) ([0, 1], [1, 0]) T}.Finite ∧
      ∀ T, Relation.ReflTransGen (ChildNC (substitution 4)) ([0, 1], [1, 0]) T →
        ∃ U, Relation.ReflTransGen (ChildNC (substitution 4)) T U ∧ U.1 = U.2 :=
  checked_termination checks4 (by decide +kernel) (by decide +kernel)

theorem reached_coincidence_child_4 {T : Pair}
    (hT : Relation.ReflTransGen (ChildNC (substitution 4)) ([0, 1], [1, 0]) T)
    (hne : T.1 ≠ T.2) : ∃ U, ChildNC (substitution 4) T U ∧ U.1 = U.2 := by
  obtain ⟨i, hi, rfl⟩ := checked_reachable checks4 (by decide +kernel)
    (by decide +kernel) hT
  obtain ⟨hr, _, ⟨he, _⟩, hd⟩ := checked_row checks4 hi hne
  refine ⟨state data4 (exit data4 i), ⟨hne, ?_⟩, hd.resolve_left (by decide)⟩
  change state data4 (exit data4 i) ∈ red _ _
  rw [← hr]
  exact List.mem_map.mpr ⟨_, he, rfl⟩

end Psc.ParameterFamilyBoundary

/-! Assemble the generic and boundary proofs over one literal substitution. -/

namespace Psc.ParameterFamily

open Psc.Descendants Psc.FastForwardCarrier
open Psc.ParameterFamilyRows (substitution)

/-- Finite actual ordered reachability and productivity at every reached state. -/
theorem finite_and_productive (k : Nat) (hk : 2 ≤ k) :
    {T | Relation.ReflTransGen (ChildNC (substitution k)) ([0, 1], [1, 0]) T}.Finite ∧
      ∀ T, Relation.ReflTransGen (ChildNC (substitution k)) ([0, 1], [1, 0]) T →
        ∃ U, Relation.ReflTransGen (ChildNC (substitution k)) T U ∧ U.1 = U.2 := by
  by_cases h : 5 ≤ k
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 5 := ⟨k - 5, by omega⟩
    exact Psc.ParameterFamilyCarrier.finite_and_productive n
  have hs : k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hs with rfl | rfl | rfl
  · exact Psc.ParameterFamilyBoundary.finite_and_productive_2
  · exact Psc.ParameterFamilyBoundary.finite_and_productive_3
  · exact Psc.ParameterFamilyBoundary.finite_and_productive_4

/-- At every parameter k ≥ 3 every reached noncoincident state has a
coincidence among its immediate actual children. -/
theorem coincidence_child (k : Nat) (hk : 3 ≤ k) {T : Pair}
    (hT : Relation.ReflTransGen (ChildNC (substitution k)) ([0, 1], [1, 0]) T)
    (hne : T.1 ≠ T.2) : ∃ U, ChildNC (substitution k) T U ∧ U.1 = U.2 := by
  by_cases h : 5 ≤ k
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 5 := ⟨k - 5, by omega⟩
    exact Psc.ParameterFamilyCarrier.reached_coincidence_child n hT hne
  have hs : k = 3 ∨ k = 4 := by omega
  rcases hs with rfl | rfl
  · exact Psc.ParameterFamilyBoundary.reached_coincidence_child_3 hT hne
  · exact Psc.ParameterFamilyBoundary.reached_coincidence_child_4 hT hne

/-- The family satisfies the repository's existing balanced-pair termination predicate. -/
theorem terminates_with_coincidence (k : Nat) (hk : 2 ≤ k) :
    Psc.StrictSystem.TerminatesWithCoincidence (substitution k) ([0, 1], [1, 0]) :=
  finite_and_productive k hk

end Psc.ParameterFamily

#print axioms Psc.ParameterFamily.terminates_with_coincidence
#print axioms Psc.ParameterFamilyCarrier.children_eq_red
#print axioms Psc.ParameterFamily.finite_and_productive
#print axioms Psc.ParameterFamily.coincidence_child
