import PscVerif.BetaFamilyXi

/-!
# Bounded factor complexity forces eventual periodicity

The direction of Morse–Hedlund used by Adamczewski–Bugeaud's dichotomy: if
every factor set of a one-sided sequence is finite with cardinality at most `C`,
the sequence is eventually periodic.

Taking length-`n` prefixes maps the factors of length `n + 1` onto those of
length `n`, so the counts are nondecreasing. Bounded counts are therefore equal
at some `n ≥ 1`, where the prefix map is injective: each length-`n` factor has a
unique right extension. The window `x_s … x_{s+n-1}` then determines the next
window, so pigeonhole on the finitely many windows makes the sequence
eventually periodic.

Applied to `ξ_{k,m}`, the complexity of `w + 1` is unbounded
(`xi_complexity_unbounded`). Together with the linear bound, this excludes both
alternatives of Adamczewski–Bugeaud Corollary 1 for an algebraic value. The
corollary itself is not formalized. Source decision:
`docs/beta-numeration-research-route-2026-11-27.md`.
-/

set_option autoImplicit false

namespace Psc.BetaFactorBounded

open Psc.BetaFamilyFixedWord (EventuallyPeriodic)
open Psc.BetaFamilyComplexity (factor factors)

variable {β : Type*}

theorem factor_take (x : ℕ → β) (s n : ℕ) : (factor x s (n + 1)).take n = factor x s n := by
  unfold factor
  rw [List.ofFn_succ', List.concat_eq_append, List.take_append_of_le_length (by simp),
    List.take_of_length_le (by simp)]
  rfl

theorem factor_drop (x : ℕ → β) (s n : ℕ) : (factor x s (n + 1)).drop 1 = factor x (s + 1) n := by
  unfold factor
  rw [List.ofFn_succ, List.drop_succ_cons, List.drop_zero]
  congr 1
  funext i
  congr 1
  simp only [Fin.val_succ]
  omega

theorem factor_head (x : ℕ → β) (s n : ℕ) : (factor x s (n + 1))[0]? = some (x s) := by
  simp [factor]

theorem factors_eq_image (x : ℕ → β) (n : ℕ) :
    factors x n = (fun u => List.take n u) '' factors x (n + 1) := by
  ext u
  simp only [factors, Set.mem_range, Set.mem_image, exists_exists_eq_and]
  constructor
  · rintro ⟨s, rfl⟩; exact ⟨s, factor_take x s n⟩
  · rintro ⟨s, rfl⟩; exact ⟨s, (factor_take x s n).symm⟩

/-- **Bounded complexity forces eventual periodicity.** -/
theorem eventuallyPeriodic_of_bounded (x : ℕ → β) {C : ℕ}
    (hC : ∀ n, (factors x n).Finite ∧ (factors x n).ncard ≤ C) : EventuallyPeriodic x := by
  set f : ℕ → ℕ := fun n => (factors x n).ncard
  have hmono : ∀ n, f n ≤ f (n + 1) := fun n => by
    show (factors x n).ncard ≤ (factors x (n + 1)).ncard
    rw [factors_eq_image x n]
    exact Set.ncard_image_le (hC (n + 1)).1
  -- Some `n ≥ 1` has `f n = f (n + 1)`.
  obtain ⟨n, hn1, heq⟩ : ∃ n, 1 ≤ n ∧ f (n + 1) = f n := by
    by_contra hno
    simp only [not_exists, not_and] at hno
    have grow : ∀ j, f 1 + j ≤ f (1 + j) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have h1 := hmono (1 + j)
        have h2 := hno (1 + j) (by omega)
        rw [show 1 + (j + 1) = 1 + j + 1 by ring]
        omega
    have := (grow (C + 1)).trans (hC (1 + (C + 1))).2
    omega
  -- The prefix map is injective on factors of length `n + 1`.
  have hinj : Set.InjOn (fun u => List.take n u) (factors x (n + 1)) := by
    rw [← Set.ncard_image_iff (hC (n + 1)).1, ← factors_eq_image]
    exact heq.symm
  -- Equal windows have equal successors.
  have hnext : ∀ s s', factor x s n = factor x s' n →
      factor x (s + 1) n = factor x (s' + 1) n := by
    intro s s' h
    have : factor x s (n + 1) = factor x s' (n + 1) :=
      hinj ⟨s, rfl⟩ ⟨s', rfl⟩ (by simp only [factor_take]; exact h)
    rw [← factor_drop, ← factor_drop, this]
  have hall : ∀ s s', factor x s n = factor x s' n →
      ∀ t, factor x (s + t) n = factor x (s' + t) n := by
    intro s s' h t
    induction t with
    | zero => simpa using h
    | succ t ih => simpa [add_assoc] using hnext _ _ ih
  -- Pigeonhole on the finitely many windows.
  have : Finite (factors x n) := (hC n).1.to_subtype
  obtain ⟨s₁, s₂, hne, hw⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun s => (⟨factor x s n, s, rfl⟩ : factors x n))
  have hw' : factor x s₁ n = factor x s₂ n := congrArg Subtype.val hw
  have per : ∀ {s s'}, factor x s n = factor x s' n → s < s' → EventuallyPeriodic x := by
    intro s s' h hlt
    refine ⟨s, s' - s, by omega, fun i hi => ?_⟩
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hi
    have hwin := hall s s' h t
    obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hn1
    rw [show 1 + n' = n' + 1 by ring] at hwin
    have := congrArg (fun l => l[0]?) hwin
    simp only [factor_head] at this
    rw [show s + t + (s' - s) = s' + t by omega]
    exact (Option.some.inj this).symm
  rcases lt_or_gt_of_ne hne with h | h
  · exact per hw' h
  · exact per hw'.symm h

/-- The complexity of the digit stream of `ξ_{k,m}` is unbounded. -/
theorem xi_complexity_unbounded (k m : ℕ) (hk : 1 ≤ k) (hm : 3 ≤ m) :
    ¬ ∃ C, ∀ n, (factors (Psc.BetaFamilyFixedWord.shifted k m hm) n).Finite ∧
      (factors (Psc.BetaFamilyFixedWord.shifted k m hm) n).ncard ≤ C := by
  rintro ⟨C, hC⟩
  exact Psc.BetaFamilyFixedWord.shifted_not_eventuallyPeriodic k m hk hm
    (eventuallyPeriodic_of_bounded _ hC)

end Psc.BetaFactorBounded
