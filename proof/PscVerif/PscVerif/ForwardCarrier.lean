import PscVerif.Descendants

/-! Finite forward carriers from the canonical ordered BPA export. -/

namespace Psc.ForwardCarrier

open Psc.Binomial Psc.Reduction Psc.Descendants

abbrev Word := List (Fin 3)
abbrev Pair := Word × Word

/-- The native writer emits only digits 0–2. The checker reasons about
the decoded words themselves and independently compares the literal images. -/
def decodePair (top bottom : String) : Pair :=
  (top.toList.map (fun c => Fin.ofNat 3 (c.toNat - '0'.toNat)),
   bottom.toList.map (fun c => Fin.ofNat 3 (c.toNat - '0'.toNat)))

structure Row where
  orbit : Nat
  reversed : Bool
  source : Pair
  children : List Pair

structure Certificate where
  images : List Word
  roots : List Pair
  rows : List Row

/-- Check the end is balanced and every interior position is unbalanced.
The vector records top minus bottom letter counts. -/
def scan (x y z : Int) : Word → Word → Bool
  | a :: u, b :: v =>
    let x' := x + (if a = 0 then 1 else 0) - (if b = 0 then 1 else 0)
    let y' := y + (if a = 1 then 1 else 0) - (if b = 1 then 1 else 0)
    let z' := z + (if a = 2 then 1 else 0) - (if b = 2 then 1 else 0)
    if u.isEmpty && v.isEmpty then decide (x' = 0 ∧ y' = 0 ∧ z' = 0)
    else (!(decide (x' = 0 ∧ y' = 0 ∧ z' = 0))) && scan x' y' z' u v
  | _, _ => false

def delta (u v : Word) (a : Fin 3) : Int := (u.count a : Int) - v.count a

theorem delta_append (u v : Word) (a b c : Fin 3) :
    delta (u ++ [a]) (v ++ [b]) c =
      delta u v c + (if a = c then 1 else 0) - (if b = c then 1 else 0) := by
  unfold delta
  rw [List.count_append, List.count_append]
  by_cases ha : a = c <;> by_cases hb : b = c <;>
    simp [ha, hb, eq_comm] <;> omega

theorem equiv_of_delta (u v : Word) (h : delta u v 0 = 0 ∧ delta u v 1 = 0 ∧ delta u v 2 = 0) :
    Equiv1 u v := by
  intro a
  fin_cases a
  · have h0 := h.1
    unfold delta at h0
    omega
  · have h1 := h.2.1
    unfold delta at h1
    omega
  · have h2 := h.2.2
    unfold delta at h2
    omega

theorem scan_sound (u v pu pv : Word) (hp : pu.length = pv.length)
    (h : scan (delta pu pv 0) (delta pu pv 1) (delta pu pv 2) u v = true) :
    Equiv1 (pu ++ u) (pv ++ v) ∧
      ∀ k, pu.length < k → k < (pu ++ u).length →
        ¬ Equiv1 ((pu ++ u).take k) ((pv ++ v).take k) := by
  induction u generalizing v pu pv with
  | nil => cases v <;> simp [scan] at h
  | cons a u ih =>
    cases v with
    | nil => simp [scan] at h
    | cons b v =>
      simp only [scan, ← delta_append] at h
      split at h
      next hend =>
        have hempty : u = [] ∧ v = [] := by simpa using hend
        obtain ⟨rfl, rfl⟩ := hempty
        exact ⟨equiv_of_delta _ _ (of_decide_eq_true h), fun k hk hk' => by
          simp at hk'
          omega⟩
      next hmore =>
        obtain ⟨hne, hscan⟩ := (Bool.and_eq_true _ _).mp h
        obtain ⟨hbal, hirr⟩ := ih v (pu ++ [a]) (pv ++ [b]) (by simp [hp]) hscan
        rw [List.append_assoc, List.append_assoc] at hbal hirr
        refine ⟨hbal, fun k hk hk' he => ?_⟩
        by_cases hcut : k = pu.length + 1
        · subst k
          have hu : pu.length + 1 = (pu ++ [a]).length := by simp
          have hv : pv.length + 1 = (pv ++ [b]).length := by simp
          have he' : Equiv1 (pu ++ [a]) (pv ++ [b]) := by
            have ht := List.take_left' (l₂ := u) hu.symm
            have hb := List.take_left' (l₂ := v)
              (hv.symm.trans (congrArg (· + 1) hp.symm))
            simp only [List.append_assoc, List.cons_append, List.nil_append] at ht hb
            rw [ht, hb] at he
            exact he
          have hz : delta (pu ++ [a]) (pv ++ [b]) 0 = 0 ∧
              delta (pu ++ [a]) (pv ++ [b]) 1 = 0 ∧
              delta (pu ++ [a]) (pv ++ [b]) 2 = 0 :=
            ⟨by have h0 := he' 0; unfold delta; omega,
              by have h1 := he' 1; unfold delta; omega,
              by have h2 := he' 2; unfold delta; omega⟩
          have hd : decide (delta (pu ++ [a]) (pv ++ [b]) 0 = 0 ∧
              delta (pu ++ [a]) (pv ++ [b]) 1 = 0 ∧
              delta (pu ++ [a]) (pv ++ [b]) 2 = 0) = true := decide_eq_true hz
          rw [hd] at hne
          contradiction
        · exact hirr k (by simp; omega) hk' he

theorem scan_block (T : Pair) (h : scan 0 0 0 T.1 T.2 = true) : IsBlock T := by
  obtain ⟨u, v⟩ := T
  have hn : u ≠ [] := by
    rintro rfl
    cases v <;> simp [scan] at h
  have hs : scan (delta [] [] 0) (delta [] [] 1) (delta [] [] 2) u v = true := h
  have hs' := scan_sound u v [] [] rfl hs
  exact ⟨hn, by simpa using hs'⟩

/-- Check exact coverage of the ordered factorization via uniqueness, avoiding
quadratic prefix permutations on the long named blocks. -/
def rowCheck (s : Fin 3 → Word) (carrier : List Pair) (r : Row) : Bool :=
  if r.source.1 = r.source.2 then r.children.isEmpty
  else
    (r.children.map Prod.fst).flatten == subst s r.source.1 &&
    (r.children.map Prod.snd).flatten == subst s r.source.2 &&
    r.children.all (fun T => scan 0 0 0 T.1 T.2 && carrier.contains T)

theorem rowCheck_closed {s : Fin 3 → Word} {carrier : List Pair} {r : Row}
    (h : rowCheck s carrier r = true) (hne : r.source.1 ≠ r.source.2)
    {U : Pair} (hU : Child s r.source U) : U ∈ carrier := by
  simp only [rowCheck, if_neg hne, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨ht, hb⟩, hc⟩ := h
  have hr := red_unique r.children (fun T hT => scan_block T (((Bool.and_eq_true _ _).mp (hc T hT)).1)) ht hb
  change U ∈ red (subst s r.source.1) (subst s r.source.2) at hU
  rw [← hr] at hU
  exact List.contains_iff_mem.mp ((Bool.and_eq_true _ _).mp (hc U hU)).2

/-- The exporter emits each normalized row followed by its swap, with a single
row for a coincidence. Verify that orientation metadata matches the words. -/
def orientations : Nat → List Row → Bool
  | _, [] => true
  | id, r :: rs =>
    (r.orbit == id && !r.reversed) &&
      if r.source.1 == r.source.2 then orientations (id + 1) rs
      else r.source.1.lex r.source.2 && match rs with
        | [] => false
        | t :: ts =>
          (t.orbit == id && t.reversed && t.source == r.source.swap) &&
            orientations (id + 1) ts

def orderedSeeds : List Pair :=
  [([0, 1], [1, 0]), ([1, 0], [0, 1]), ([0, 2], [2, 0]), ([2, 0], [0, 2]),
    ([1, 2], [2, 1]), ([2, 1], [1, 2])]

theorem orderedSeeds_cover (a b : Fin 3) (h : a ≠ b) : ([a, b], [b, a]) ∈ orderedSeeds := by
  fin_cases a <;> fin_cases b <;> simp_all [orderedSeeds]

def check (s : Fin 3 → Word) (c : Certificate) : Bool :=
  let carrier := c.rows.map Row.source
  c.images == [s 0, s 1, s 2] &&
    c.roots == orderedSeeds &&
    c.roots.all carrier.contains &&
    orientations 0 c.rows &&
    c.rows.all (rowCheck s carrier)

theorem finite_of_check {s : Fin 3 → Word} {c : Certificate} (h : check s c = true) :
    (bpaStatesNC s).Finite := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨_, hroots⟩, hseed⟩, _⟩, hrows⟩ := h
  apply (List.finite_toSet (c.rows.map Row.source)).subset
  apply bpaStatesNC_subset s
  · intro T hT
    obtain ⟨a, b, hab, rfl⟩ := mem_seeds.mp hT
    have hmem : ([a, b], [b, a]) ∈ c.roots := hroots.symm ▸ orderedSeeds_cover a b hab
    have hm := hseed _ hmem
    exact List.contains_iff_mem.mp hm
  · intro T hT hne U hU
    change T ∈ c.rows.map Row.source at hT
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hT
    exact rowCheck_closed (hrows r hr) hne hU

theorem finite_from_seed_of_check {s : Fin 3 → Word} {c : Certificate}
    (h : check s c = true) {T : Pair} (hT : T ∈ (seeds : Finset Pair)) :
    {U | Relation.ReflTransGen (ChildNC s) T U}.Finite :=
  (finite_of_check h).subset fun _ hU => ⟨T, hT, hU⟩

end Psc.ForwardCarrier

namespace Psc.ForwardCarrier

private def sampleSource : Fin 3 → Word := ![[0], [1], [2]]

private def sampleRows : List Row :=
  orderedSeeds.zipIdx |>.map fun (T, i) => ⟨i / 2, i % 2 == 1, T, [T]⟩

private def sample : Certificate := ⟨[[0], [1], [2]], orderedSeeds, sampleRows⟩

example : check sampleSource sample = true := by decide +kernel

example : check sampleSource {sample with rows := (sampleRows.modify 0
    (fun r => {r with children := []}))} = false := by decide +kernel

example : check sampleSource {sample with rows := (sampleRows.modify 1
    (fun r => {r with reversed := false}))} = false := by decide +kernel

example : check sampleSource {sample with rows := (sampleRows.modify 0
    (fun r => {r with children := r.children.map Prod.swap}))} = false := by decide +kernel

example : check sampleSource {sample with images := [[0], [2], [1]]} = false := by decide +kernel

example : check sampleSource {sample with roots := sample.roots.drop 1} = false := by decide +kernel

end Psc.ForwardCarrier
