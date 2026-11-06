import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-! Exact source-word coincidence, independent of overlap certificates.
No geometric, Pisot, or finite-census hypothesis is used. -/
namespace TwoTail502
inductive Letter | z | o | t deriving DecidableEq, Repr
open Letter
abbrev Word := List Letter
abbrev Substitution := Letter → Word
def parikh (w : Word) : Letter → ℕ := fun c => w.count c
def Balanced (u v : Word) : Prop := parikh u = parikh v
def inflate (σ : Substitution) (w : Word) : Word := w.flatMap σ
def iterate (σ : Substitution) : ℕ → Word → Word
  | 0, w => w
  | n+1, w => inflate σ (iterate σ n w)
def power (w : Word) : ℕ → Word
  | 0 => []
  | n+1 => w ++ power w n

@[simp] theorem inflate_nil (σ : Substitution) : inflate σ [] = [] := rfl
@[simp] theorem inflate_cons (σ : Substitution) (c : Letter) (w : Word) :
    inflate σ (c :: w) = σ c ++ inflate σ w := rfl
@[simp] theorem inflate_append (σ : Substitution) (u v : Word) :
    inflate σ (u ++ v) = inflate σ u ++ inflate σ v := by
  exact List.flatMap_append
@[simp] theorem inflate_single (σ : Substitution) (c : Letter) :
    inflate σ [c] = σ c := by simp
@[simp] theorem power_zero (w : Word) : power w 0 = [] := rfl
theorem power_succ (w : Word) (n : ℕ) : power w (n+1) = w ++ power w n := rfl
@[simp] theorem power_one (w : Word) : power w 1 = w := by simp [power]
@[simp] theorem inflate_power (σ : Substitution) (w : Word) (n : ℕ) :
    inflate σ (power w n) = power (inflate σ w) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [power_succ, inflate_append, ih]
@[simp] theorem iterate_nil (σ : Substitution) (n : ℕ) : iterate σ n [] = [] := by
  induction n <;> simp_all [iterate]
@[simp] theorem iterate_append (σ : Substitution) (n : ℕ) (u v : Word) :
    iterate σ n (u ++ v) = iterate σ n u ++ iterate σ n v := by
  induction n <;> simp_all [iterate]
theorem iterate_commute (σ : Substitution) (n : ℕ) (w : Word) :
    iterate σ n (inflate σ w) = inflate σ (iterate σ n w) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterate, ih]
theorem iterate_add (σ : Substitution) (n k : ℕ) (w : Word) :
    iterate σ (n+k) w = iterate σ k (iterate σ n w) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change inflate σ (iterate σ (n+k) w) = inflate σ (iterate σ k (iterate σ n w))
    rw [ih]
theorem iterate_substitute (σ : Substitution) (n : ℕ) (w : Word) :
    iterate σ n w = w.flatMap (fun c => iterate σ n [c]) := by
  induction w with
  | nil => simp
  | cons c w ih =>
    simpa only [List.flatMap_cons, ← ih, List.cons_append, List.nil_append] using iterate_append σ n [c] w
@[simp] theorem iterate_power (σ : Substitution) (n : ℕ) (w : Word) (k : ℕ) :
    iterate σ n (power w k) = power (iterate σ n w) k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [power_succ, iterate_append, ih]

@[simp] theorem iterate_two_letters (σ : Substitution) (n : ℕ) (c d : Letter) :
    iterate σ n [c,d] = iterate σ n [c] ++ iterate σ n [d] := by
  simpa only [List.cons_append,List.nil_append] using iterate_append σ n [c] [d]
@[simp] theorem iterate_three_letters (σ : Substitution) (n : ℕ) (c d e : Letter) :
    iterate σ n [c,d,e] = iterate σ n [c] ++ iterate σ n [d] ++ iterate σ n [e] := by
  simpa only [List.cons_append,List.nil_append,iterate_two_letters,List.append_assoc] using
    iterate_append σ n [c] [d,e]

theorem balanced_iff_perm (u v : Word) : Balanced u v ↔ u.Perm v := by
  simp only [Balanced, parikh, funext_iff, List.perm_iff_count]
theorem balanced_iff_counts (u v : Word) :
    Balanced u v ↔ u.count z = v.count z ∧ u.count o = v.count o ∧ u.count t = v.count t := by
  constructor
  · intro h; exact ⟨congrFun h z,congrFun h o,congrFun h t⟩
  · rintro ⟨hz,ho,ht⟩
    funext c; cases c
    · exact hz
    · exact ho
    · exact ht
instance (u v : Word) : Decidable (Balanced u v) :=
  decidable_of_iff _ (balanced_iff_counts u v).symm

theorem balanced_inflate (σ : Substitution) {u v : Word} (h : Balanced u v) :
    Balanced (inflate σ u) (inflate σ v) := by
  exact (balanced_iff_perm _ _).2 (((balanced_iff_perm _ _).1 h).flatMap_right σ)
theorem balanced_iterate (σ : Substitution) (n : ℕ) {u v : Word}
    (h : Balanced u v) : Balanced (iterate σ n u) (iterate σ n v) := by
  induction n with
  | zero => exact h
  | succ n ih => exact balanced_inflate σ ih
theorem balanced_length {u v : Word} (h : Balanced u v) : u.length = v.length :=
  ((balanced_iff_perm _ _).1 h).length_eq

/- Prefix certificates expose the actual finite words and common following letter.
The empty prefix is allowed, as in the standard strong-coincidence definition. -/
def Witness (u v : Word) : Prop :=
  ∃ p q : Word, ∃ c : Letter,
    Balanced p q ∧ (p ++ [c]).IsPrefix u ∧ (q ++ [c]).IsPrefix v
def SourceWitness (σ : Substitution) (n : ℕ) (i j : Letter) : Prop :=
  Witness (iterate σ n [i]) (iterate σ n [j])
def Nonerasing (σ : Substitution) : Prop := ∀ c, σ c ≠ []
def PairwiseAt (σ : Substitution) (n : ℕ) : Prop := ∀ i j, SourceWitness σ n i j
/- A balanced prefix, a singleton diagonal, and a balanced suffix form a genuine
balanced partition. Refining either surrounding piece cannot split the singleton. -/
def DiagonalFactor (u v : Word) : Prop :=
  ∃ p q : Word, ∃ c : Letter, ∃ r s : Word,
    u = p ++ [c] ++ r ∧ v = q ++ [c] ++ s ∧ Balanced p q ∧ Balanced r s

theorem prefix_inflate (σ : Substitution) {u v : Word} (h : u.IsPrefix v) :
    (inflate σ u).IsPrefix (inflate σ v) := by
  rcases h with ⟨r, hr⟩
  exact ⟨inflate σ r, by simpa only [← inflate_append] using congrArg (inflate σ) hr⟩
theorem prefix_extend {u v : Word} (h : u.IsPrefix v) (r : Word) :
    u.IsPrefix (v ++ r) := h.trans (List.prefix_append _ _)
theorem witness_extend {u v : Word} (h : Witness u v) (r s : Word) :
    Witness (u ++ r) (v ++ s) := by
  rcases h with ⟨p,q,c,hb,hp,hq⟩
  exact ⟨p,q,c,hb,prefix_extend hp r,prefix_extend hq s⟩
theorem witness_symm {u v : Word} (h : Witness u v) : Witness v u := by
  rcases h with ⟨p,q,c,hb,hp,hq⟩
  exact ⟨q,p,c,hb.symm,hq,hp⟩
theorem witness_refl {u : Word} (h : u ≠ []) : Witness u u := by
  cases u with
  | nil => contradiction
  | cons c r => exact ⟨[],[],c,rfl,⟨r,rfl⟩,⟨r,rfl⟩⟩
theorem witness_inflate (σ : Substitution) (hne : Nonerasing σ)
    {u v : Word} (h : Witness u v) : Witness (inflate σ u) (inflate σ v) := by
  rcases h with ⟨p,q,c,hb,hp,hq⟩
  obtain ⟨d,r,hd⟩ : ∃ d r, σ c = d :: r := by
    cases hc : σ c with
    | nil => exact False.elim (hne c hc)
    | cons d r => exact ⟨d,r,rfl⟩
  have hh (w : Word) : (inflate σ w ++ [d]).IsPrefix (inflate σ (w ++ [c])) := by
    refine ⟨r, ?_⟩
    simp [hd, List.append_assoc]
  exact ⟨inflate σ p,inflate σ q,d,balanced_inflate σ hb,
    (hh p).trans (prefix_inflate σ hp),(hh q).trans (prefix_inflate σ hq)⟩
theorem witness_iterate (σ : Substitution) (hne : Nonerasing σ) (k : ℕ)
    {u v : Word} (h : Witness u v) : Witness (iterate σ k u) (iterate σ k v) := by
  induction k with
  | zero => exact h
  | succ k ih => exact witness_inflate σ hne ih
theorem source_propagate (σ : Substitution) (hne : Nonerasing σ)
    {n m : ℕ} {i j : Letter} (hnm : n ≤ m) (h : SourceWitness σ n i j) :
    SourceWitness σ m i j := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hnm
  simpa only [SourceWitness, iterate_add] using witness_iterate σ hne k h
theorem iterate_nonerasing (σ : Substitution) (hne : Nonerasing σ) (n : ℕ)
    {w : Word} (hw : w ≠ []) : iterate σ n w ≠ [] := by
  induction n with
  | zero => exact hw
  | succ n ih =>
    cases he : iterate σ n w with
    | nil => exact False.elim (ih he)
    | cons c r =>
      cases hs : σ c with
      | nil => exact False.elim (hne c hs)
      | cons d s => simp [iterate,he,inflate_cons,hs]

theorem witness_diagonal {u v : Word} (hb : Balanced u v) (h : Witness u v) :
    DiagonalFactor u v := by
  rcases h with ⟨p,q,c,hpq,⟨r,hr⟩,⟨s,hs⟩⟩
  refine ⟨p,q,c,r,s,hr.symm,hs.symm,hpq,?_⟩
  funext d
  have hb' := congrFun hb d
  have hpq' := congrFun hpq d
  simp only [Balanced, parikh] at hb' hpq' ⊢
  rw [← hr, ← hs] at hb'
  simp only [List.count_append] at hb'
  omega

theorem pairwise_diagonal_productivity (σ : Substitution) (n : ℕ)
    (hpairs : PairwiseAt σ n) {u v : Word} (hu : u ≠ []) (hv : v ≠ [])
    (hb : Balanced u v) : DiagonalFactor (iterate σ n u) (iterate σ n v) := by
  cases u with
  | nil => contradiction
  | cons i r =>
    cases v with
    | nil => contradiction
    | cons j s =>
      apply witness_diagonal (balanced_iterate σ n hb)
      simpa only [show i :: r = [i] ++ r from rfl,
        show j :: s = [j] ++ s from rfl, iterate_append] using
        witness_extend (hpairs i j) (iterate σ n r) (iterate σ n s)

#print axioms witness_inflate
#print axioms source_propagate
#print axioms pairwise_diagonal_productivity
end TwoTail502
