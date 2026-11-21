/-
# The legal hull is nonempty

Gap 5 of `docs/c4-tiling-hull-realization-2026-11-19.md`: `hull_nonempty_of_seed` needed a
legal growing seed, and only Thue--Morse was checked.  This module supplies the seed for every
`LengthSubst` on a finite nonempty alphabet with `1 < β`, so the hull is nonempty.  Neither
primitivity nor the Pisot property is used.

The seed is the classical one.  Some image has two letters `x y` (otherwise lengths would
grow by `β` along a cycle of single letters).  The pair map `(x, y) ↦ (last σ(x), first σ(y))`
on the finite set `α × α` is eventually periodic: for some `m` and `k > 0` the letters
`b = g_Rᵐ x`, `a = g_Lᵐ y` satisfy `g_Rᵏ b = b`, `g_Lᵏ a = a`.  The two-tile patch `b.a`
occurs in `σᵐ⁺¹(c)` and lies inside its own `k`-fold inflation.

See `docs/c4-hull-nonempty-stop-go-2026-11-21.md` for the source decision.
-/
import PscVerif.PeriodicPartnerSpectralCensus
import PscVerif.PeriodicPartnerSpectralModels

namespace Psc.PeriodicPartnerHull

open Function Set

namespace LengthSubst

variable {α : Type*} (S : LengthSubst α)

/-! ## Words under the substitution -/

/-- The substitution acting on words. -/
def subst (w : List α) : List α := w.flatMap S.σ

/-- The left endpoint map `g_L`: the first letter of each image. -/
def firstLetter (a : α) : α := (S.σ a).head (S.ne_nil a)

theorem subst_append (u v : List α) : S.subst (u ++ v) = S.subst u ++ S.subst v :=
  List.flatMap_append

theorem subst_iterate_append (u v : List α) (n : ℕ) :
    S.subst^[n] (u ++ v) = S.subst^[n] u ++ S.subst^[n] v := by
  induction n generalizing u v with
  | zero => rfl
  | succ n ih => simp only [iterate_succ_apply, S.subst_append, ih]

theorem sum_subst (w : List α) : ((S.subst w).map S.ℓ).sum = S.β * (w.map S.ℓ).sum := by
  induction w with
  | nil => simp [subst]
  | cons a w ih =>
    simp only [subst, List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, mul_add, S.eigen] at ih ⊢
    rw [ih]

theorem sum_subst_iterate (w : List α) (n : ℕ) :
    ((S.subst^[n] w).map S.ℓ).sum = S.β ^ n * (w.map S.ℓ).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ_apply', S.sum_subst, ih, pow_succ', mul_assoc]

theorem subst_iterate_head (c : α) (n : ℕ) :
    ∃ v, S.subst^[n] [c] = S.firstLetter^[n] c :: v := by
  induction n with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
    obtain ⟨v, hv⟩ := ih
    refine ⟨(S.σ (S.firstLetter^[n] c)).tail ++ S.subst v, ?_⟩
    rw [iterate_succ_apply', hv, iterate_succ_apply', ← List.singleton_append, S.subst_append]
    simp only [subst, List.flatMap_singleton, firstLetter]
    rw [← List.cons_append, List.cons_head_tail]

theorem subst_iterate_last (c : α) (n : ℕ) :
    ∃ u, S.subst^[n] [c] = u ++ [S.lastLetter^[n] c] := by
  induction n with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
    obtain ⟨u, hu⟩ := ih
    refine ⟨S.subst u ++ (S.σ (S.lastLetter^[n] c)).dropLast, ?_⟩
    rw [iterate_succ_apply', hu, iterate_succ_apply', S.subst_append]
    simp only [subst, List.flatMap_singleton, lastLetter]
    rw [List.append_assoc, List.dropLast_append_getLast]

/-! ## Placement of words and iterated inflation -/

theorem place_append (u v : List α) (x : ℝ) :
    S.place (u ++ v) x = S.place u x ++ S.place v (x + (u.map S.ℓ).sum) := by
  induction u generalizing x with
  | nil => simp [place]
  | cons a u ih => simp only [List.cons_append, place, ih, List.map_cons, List.sum_cons,
      add_assoc]

theorem inflate_place (w : List α) (x : ℝ) :
    S.inflate {q | q ∈ S.place w x} = {q | q ∈ S.place (S.subst w) (S.β * x)} := by
  induction w generalizing x with
  | nil => ext q; simp [inflate, place, subst]
  | cons a w ih =>
    ext q
    have hih := congrArg (q ∈ ·) (ih (x + S.ℓ a))
    simp only [inflate, Set.mem_ofPred_eq, eq_iff_iff] at hih
    have hsplit : S.subst (a :: w) = S.σ a ++ S.subst w := List.flatMap_cons
    simp only [inflate, Set.mem_ofPred_eq, place, List.mem_cons, exists_eq_or_imp, hsplit,
      S.place_append, List.mem_append, S.eigen]
    rw [hih]
    try rw [show S.β * x + S.β * S.ℓ a = S.β * (x + S.ℓ a) by ring]

theorem inflate_iterate_singleton (c : α) (x : ℝ) (n : ℕ) :
    S.inflate^[n] {(c, x)} = {q | q ∈ S.place (S.subst^[n] [c]) (S.β ^ n * x)} := by
  induction n with
  | zero => ext q; simp [place]
  | succ n ih =>
    rw [iterate_succ_apply', ih, S.inflate_place, ← iterate_succ_apply' S.subst, pow_succ',
      mul_assoc]

/-! ## A word with two letters -/

/-- With `1 < β` some image has at least two letters; otherwise lengths would multiply by
`β` around a cycle of the first-letter map. -/
theorem exists_two_letters [Finite α] [Nonempty α] (hβ : 1 < S.β) :
    ∃ c x y r, S.σ c = x :: y :: r := by
  by_contra hno
  push Not at hno
  have hsingle : ∀ c, S.σ c = [S.firstLetter c] := by
    intro c
    have h := List.cons_head_tail (S.ne_nil c)
    rcases htail : (S.σ c).tail with _ | ⟨y, r⟩
    · rw [htail] at h; exact h.symm
    · rw [htail] at h; exact absurd h.symm (hno c _ y r)
  have hlen : ∀ n c, S.ℓ (S.firstLetter^[n] c) = S.β ^ n * S.ℓ c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro c
      have he := S.eigen (S.firstLetter^[n] c)
      rw [hsingle] at he
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at he
      rw [iterate_succ_apply', he, ih, pow_succ', mul_assoc]
  obtain ⟨c₀⟩ := ‹Nonempty α›
  obtain ⟨i, j, hij, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => S.firstLetter^[n] c₀)
  have hi := hlen i c₀
  have hj := hlen j c₀
  rw [heq] at hi
  have hpow : S.β ^ i = S.β ^ j :=
    mul_right_cancel₀ (S.ℓ_pos c₀).ne' (hi.symm.trans hj)
  exact hij (pow_right_injective₀ (by linarith) hβ.ne' hpow)

end LengthSubst

/-- Every orbit of a self-map of a finite type reaches a periodic point. -/
theorem exists_periodic_iterate {β : Type*} [Finite β] (F : β → β) (p : β) :
    ∃ m k, 0 < k ∧ F^[k] (F^[m] p) = F^[m] p := by
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => F^[n] p)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact ⟨i, j - i, Nat.sub_pos_of_lt hlt, by
      rw [← iterate_add_apply, Nat.sub_add_cancel hlt.le]; exact h.symm⟩
  · exact ⟨j, i - j, Nat.sub_pos_of_lt hlt, by
      rw [← iterate_add_apply, Nat.sub_add_cancel hlt.le]; exact h⟩

namespace LengthSubst

variable {α : Type*} (S : LengthSubst α)

/-- **The legal hull is nonempty** for every length substitution with `1 < β` on a finite
nonempty alphabet. -/
theorem hull_nonempty [Finite α] [Nonempty α] (hβ : 1 < S.β) : Nonempty S.Hull := by
  obtain ⟨c, x, y, r, hc⟩ := S.exists_two_letters hβ
  obtain ⟨m, k, hk, hper⟩ :=
    exists_periodic_iterate (Prod.map S.lastLetter S.firstLetter) (x, y)
  simp only [Prod.map_iterate, Prod.map_apply, Prod.mk.injEq] at hper
  set b := S.lastLetter^[m] x with hb
  set a := S.firstLetter^[m] y with ha
  obtain ⟨hbk, hak⟩ := hper
  have hℓa := S.ℓ_pos a
  have hℓb := S.ℓ_pos b
  refine S.hull_nonempty_of_seed hβ hk (P := {(b, -S.ℓ b), (a, 0)})
    (x := -S.ℓ b) (y := S.ℓ a) (by linarith) hℓa ?_ ?_ ?_
  · -- the seed tiles `[-ℓ b, ℓ a)`
    refine ⟨?_, fun z hz => ?_⟩
    · rintro p (rfl | rfl) z ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
    · by_cases hneg : z < 0
      · refine ⟨(b, -S.ℓ b), ⟨Or.inl rfl, hz.1, by simpa using hneg⟩, ?_⟩
        rintro p ⟨hp | hp, hzp⟩
        · exact hp
        · subst hp; exact absurd hzp.1 (by simpa using hneg)
      · refine ⟨(a, 0), ⟨Or.inr rfl, not_lt.mp hneg, by simpa using hz.2⟩, ?_⟩
        rintro p ⟨hp | hp, hzp⟩
        · subst hp; exact absurd hzp.2 (by simpa using hneg)
        · exact hp
  · -- the seed lies in its own `k`-fold inflation
    rintro p (rfl | rfl)
    · have hsub := S.inflate_iterate_mono
        (show ({(b, -S.ℓ b)} : Set (α × ℝ)) ⊆ {(b, -S.ℓ b), (a, 0)} by simp) k
      apply hsub
      rw [S.inflate_iterate_singleton]
      obtain ⟨u, hu⟩ := S.subst_iterate_last b k
      rw [hbk] at hu
      have hlast := S.place_last (w := S.subst^[k] [b]) (by simp [hu]) (S.β ^ k * -S.ℓ b)
      have hsum := S.sum_subst_iterate [b] k
      simp only [hu, List.getLast_append_singleton] at hlast hsum
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hsum
      rw [hsum] at hlast
      show _ ∈ S.place _ _
      rw [hu]
      convert hlast using 2
      ring
    · have hsub := S.inflate_iterate_mono
        (show ({(a, 0)} : Set (α × ℝ)) ⊆ {(b, -S.ℓ b), (a, 0)} by simp) k
      apply hsub
      rw [S.inflate_iterate_singleton]
      obtain ⟨v, hv⟩ := S.subst_iterate_head a k
      simp only [Set.mem_ofPred_eq, hv, hak, mul_zero, place, List.mem_cons, true_or]
  · -- the seed is a patch of the supertile `σᵐ⁺¹(c)`
    obtain ⟨u, hu⟩ := S.subst_iterate_last x m
    obtain ⟨v, hv⟩ := S.subst_iterate_head y m
    rw [← hb] at hu
    rw [← ha] at hv
    refine ⟨c, m + 1, (u.map S.ℓ).sum + S.ℓ b, ?_⟩
    have hword : S.subst^[m + 1] [c] = u ++ b :: a :: (v ++ S.subst^[m] r) := by
      rw [iterate_succ_apply]
      have h1 : S.subst [c] = [x] ++ ([y] ++ r) := by simp [subst, hc]
      rw [h1, S.subst_iterate_append, S.subst_iterate_append, hu, hv]
      simp
    have hmem : ∀ q, q ∈ S.place (S.subst^[m + 1] [c]) 0 → q ∈ S.supertile c (m + 1) := by
      intro q hq
      rw [supertile, S.inflate_iterate_singleton, mul_zero]
      exact hq
    rintro p (rfl | rfl) <;> apply hmem <;> rw [hword, S.place_append] <;>
      simp only [place, List.mem_append, List.mem_cons, zero_add] <;> right
    · left; ext <;> simp
    · right; left; simp

end LengthSubst

/-! ## The census class -/

open Psc.PeriodicPartnerSpectralCertificate

/-- Every PIP3 length substitution has a nonempty legal hull. -/
theorem PIP3.hull_nonempty {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {S : LengthSubst α} (h : PIP3 S) : Nonempty S.Hull :=
  S.hull_nonempty h.2.2.2.1

/-- Every member of the 4,554-specimen census underlies a PIP3 length substitution with
derived `PisotData` and a nonempty legal hull. -/
theorem census_hull_nonempty (σ : Fin 3 → List (Fin 3))
    (hlen : ∀ a, 1 ≤ (σ a).length ∧ (σ a).length ≤ 3)
    (hmem : (σ 0, σ 1, σ 2) ∈ Psc.PeriodicPartnerSpectralCensus.corpus) :
    ∃ S : LengthSubst (Fin 3), S.σ = σ ∧ PIP3 S ∧
      Nonempty (Psc.PeriodicPartnerRealization.PisotData S) ∧ Nonempty S.Hull := by
  obtain ⟨S, hσ, hP, hD⟩ := (Psc.PeriodicPartnerSpectralCensus.census σ hlen).2 hmem
  exact ⟨S, hσ, hP, hD, PIP3.hull_nonempty hP⟩

/-- The Tribonacci hull is nonempty. -/
theorem tribonacci_hull_nonempty : Nonempty Psc.PeriodicPartnerSpectralModels.tribonacci.Hull :=
  Psc.PeriodicPartnerSpectralModels.tribonacci.hull_nonempty
    Psc.PeriodicPartnerSpectralModels.one_lt_τ

end Psc.PeriodicPartnerHull
