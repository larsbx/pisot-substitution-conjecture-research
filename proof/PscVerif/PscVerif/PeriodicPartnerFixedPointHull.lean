/-
The finite seed count for the existing legal hull.
The geometric classification of fixed tilings by their origin seeds is the
explicit equivalence supplied to the final two theorems.
-/
import PscVerif.PeriodicPartnerEvenTails
import PscVerif.PeriodicPartnerFixedPointParity
import PscVerif.PeriodicPartnerMarkerParity

namespace Psc.PeriodicPartnerFixedPointHull

open Function Polynomial Psc.PeriodicPartnerHull Psc.PeriodicPartnerFixedPointParity

variable {α : Type*} (S : LengthSubst α)

/-- The first-letter endpoint map of the same substitution as the hull. -/
def firstLetter (a : α) : α := (S.σ a).head (S.ne_nil a)

theorem first_iterWord (n : ℕ) (a : α) :
    (S.iterWord n a).head? = some ((firstLetter S)^[n] a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [LengthSubst.iterWord, iterate_succ_apply', ← LengthSubst.iterWord]
    rw [PeriodicPartnerMarkerParity.head_flatMap S.σ (firstLetter S)
      (fun b => List.head?_eq_some_head (S.ne_nil b)), ih, iterate_succ_apply']
    rfl

theorem last_iterWord (n : ℕ) (a : α) :
    (S.iterWord n a).getLast? = some (S.lastLetter^[n] a) := by
  have last_flatMap (w : List α) :
      (w.flatMap S.σ).getLast? = w.getLast?.map S.lastLetter := by
    rw [← List.head?_reverse, List.reverse_flatMap,
      PeriodicPartnerMarkerParity.head_flatMap _ S.lastLetter]
    · rw [List.head?_reverse]
    · intro b
      change ((S.σ b).reverse).head? = _
      rw [List.head?_reverse]
      exact List.getLast?_eq_some_getLast (S.ne_nil b)
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [LengthSubst.iterWord, iterate_succ_apply', ← LengthSubst.iterWord]
    rw [last_flatMap, ih, iterate_succ_apply']
    rfl

/-- A positive inflation power cannot send a positive-length tile to itself
as a one-letter word. Other one-letter images are allowed. -/
theorem iterWord_ne_singleton_self (hβ : 1 < S.β) {n : ℕ} (hn : 0 < n) (a : α) :
    S.iterWord n a ≠ [a] := by
  intro h
  have hlen := (S.pow n).eigen a
  change ((S.iterWord n a).map S.ℓ).sum = S.β ^ n * S.ℓ a at hlen
  rw [h] at hlen
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hlen
  have hlt := mul_lt_mul_of_pos_right (one_lt_pow₀ hβ hn.ne') (S.ℓ_pos a)
  rw [one_mul, ← hlen] at hlt
  exact lt_irrefl _ hlt

private theorem count_partition [DecidableEq α] (w : List α) (a : α) (hw : w ≠ [a]) :
    (w.tail.dropLast).count a + (if w.head? = some a then 1 else 0) +
      (if w.getLast? = some a then 1 else 0) = w.count a := by
  cases w with
  | nil => simp
  | cons b tail =>
    by_cases ht : tail = []
    · subst tail
      have hba : b ≠ a := fun h => hw (h ▸ rfl)
      simp [hba]
    · have htail : tail.count a = tail.dropLast.count a +
          (if tail.getLast ht = a then 1 else 0) := by
        conv_lhs => rw [← List.dropLast_append_getLast ht]
        by_cases he : tail.getLast ht = a <;> simp [List.count_append, he]
      rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), List.getLast_cons ht]
      simp only [List.tail_cons, List.head?_cons, Option.some.injEq, List.count_cons, beq_iff_eq]
      rw [htail]
      omega

section FiniteAlphabet

variable [Fintype α]

/-- A legal seam is a pair of abutting tiles in one supertile of the original
substitution. The real coordinate is the position of their common cut. -/
noncomputable def legalSeams : Finset (α × α) := by
  classical
  exact Finset.univ.filter fun ba => ∃ (c : α) (m : ℕ) (x : ℝ),
    (ba.1, x - S.ℓ ba.1) ∈ S.supertile c m ∧ (ba.2, x) ∈ S.supertile c m

/-- An actual vertex at the origin of a legal tiling gives a legal seam in
the same substitution used for the finite count. -/
theorem mem_legalSeams_of_origin {T : S.Hull} {b a : α}
    (hb : (b, -S.ℓ b) ∈ T.1) (ha : (a, 0) ∈ T.1) :
    (b, a) ∈ legalSeams S := by
  classical
  obtain ⟨c, m, t, h⟩ := T.2.2 (S.ℓ b + 1)
  have hleft : (S.supp (b, -S.ℓ b) ∩ Set.Ioo (-(S.ℓ b + 1)) (S.ℓ b + 1)).Nonempty := by
    refine ⟨-S.ℓ b, ⟨le_rfl, ?_⟩, ?_, ?_⟩ <;> linarith [S.ℓ_pos b]
  have hright : (S.supp (a, 0) ∩ Set.Ioo (-(S.ℓ b + 1)) (S.ℓ b + 1)).Nonempty := by
    refine ⟨0, ⟨le_rfl, ?_⟩, ?_, ?_⟩ <;> linarith [S.ℓ_pos b, S.ℓ_pos a]
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, m, t, ?_, ?_⟩
  · simpa [sub_eq_add_neg, add_comm] using h _ hb hleft
  · simpa using h _ ha hright

variable [DecidableEq α]

/-- A seed is either an ordinal among the interior occurrences of its
own letter, or a legal seam fixed by both endpoint maps at the given power. -/
noncomputable def FixedSeed (n : ℕ) :=
  (Σ a : α, Fin (((S.iterWord n a).tail.dropLast).count a)) ⊕
    ↥(fixedSeams S.lastLetter (firstLetter S) (legalSeams S) n)

noncomputable instance (n : ℕ) : Fintype (FixedSeed S n) := by
  unfold FixedSeed
  infer_instance

/-- The finite word identity in Lemma N, in additive form to avoid
subtraction of natural numbers. The trace uses the existing incidence powers. -/
theorem fixedSeed_card (hβ : 1 < S.β) {n : ℕ} (hn : 0 < n) :
    Fintype.card (FixedSeed S n) + (fixedLetters (firstLetter S) n).card +
      (fixedLetters S.lastLetter n).card =
      (S.incidence ^ n).trace +
        (fixedSeams S.lastLetter (firstLetter S) (legalSeams S) n).card := by
  have hcard : Fintype.card (FixedSeed S n) =
      (∑ a, ((S.iterWord n a).tail.dropLast).count a) +
        (fixedSeams S.lastLetter (firstLetter S) (legalSeams S) n).card := by
    unfold FixedSeed
    simp
  have hsum := Finset.sum_congr rfl fun a (_ : a ∈ (Finset.univ : Finset α)) =>
    count_partition (S.iterWord n a) a (iterWord_ne_singleton_self S hβ hn a)
  simp only [first_iterWord, last_iterWord, Option.some.injEq, Finset.sum_add_distrib,
    PeriodicPartnerEvenTails.count_iterWord] at hsum
  have fixedCard (g : α → α) :
      (fixedLetters g n).card = ∑ a, if g^[n] a = a then 1 else 0 := by
    simp only [fixedLetters, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [hcard, fixedCard, Matrix.trace, Matrix.diag]
  omega

variable [Nonempty α]

/-- To transfer the word count to this hull one must classify all its
fixed tilings, at the same power, by the finite types above. -/
theorem hull_count_of_classification (hβ : 1 < S.β) {n : ℕ} (hn : 0 < n)
    (classify : ↥(fixedPoints ((LengthSubst.inflateH (S := S))^[n])) ≃ FixedSeed S n) :
    Nat.card (fixedPoints ((LengthSubst.inflateH (S := S))^[n])) +
      (fixedLetters (firstLetter S) n).card + (fixedLetters S.lastLetter n).card =
      (S.incidence ^ n).trace +
        (fixedSeams S.lastLetter (firstLetter S) (legalSeams S) n).card := by
  rw [Nat.card_congr classify, Nat.card_eq_fintype_card]
  exact fixedSeed_card S hβ hn

end FiniteAlphabet

/-- The parity conclusion on the original ternary hull, conditional on the
origin-seed classification, complete periodic range and commuting free twin.
The determinant and characteristic polynomial use integer incidence. -/
theorem hull_parity_of_classification (S : LengthSubst (Fin 3))
    (hβ : 1 < S.β)
    (classify : ∀ n : ℕ, 0 < n →
      ↥(fixedPoints ((LengthSubst.inflateH (S := S))^[n])) ≃ FixedSeed S n)
    (hleft : (periodicLetters S.lastLetter).card = 2)
    (hright : (periodicLetters (firstLetter S)).card = 2)
    (hcomplete : (periodicLetters S.lastLetter ×ˢ periodicLetters (firstLetter S)) ⊆ legalSeams S)
    (twin : S.Hull → S.Hull)
    (hcomm : Function.Commute (LengthSubst.inflateH (S := S)) twin)
    (hinv : Involutive twin) (hfree : ∀ x, twin x ≠ x) :
    let M := S.incidence.map (Nat.castRingHom ℤ)
    (∀ n : ℕ, 0 < n → Even ((S.incidence ^ n).trace)) ∧ Even M.det ∧
      (M.charpoly.map (Int.castRingHom F₂) = X ^ 3 ∨
        M.charpoly.map (Int.castRingHom F₂) = X * (X + 1) ^ 2) := by
  intro M
  let A := S.incidence.map (Nat.castRingHom F₂)
  have htr (n : ℕ) (hn : 0 < n) : Even ((S.incidence ^ n).trace) := by
    let e := classify n hn
    have := Finite.of_equiv (FixedSeed S n) e.symm
    exact (even_count_iff_even_trace S.lastLetter (firstLetter S) (legalSeams S)
      hleft hright hcomplete hn (hull_count_of_classification S hβ hn e)).mp
      (even_card_fixedPoints _ twin (hcomm.iterate_left n) hinv hfree)
  have hz (n : ℕ) (hn : 0 < n) : (A ^ n).trace = 0 := by
    have hm : (S.incidence ^ n).map (Nat.castRingHom F₂) = A ^ n :=
      map_pow (Nat.castRingHom F₂).mapMatrix S.incidence n
    rw [← hm, ← AddMonoidHom.map_trace (Nat.castRingHom F₂)]
    exact ZMod.natCast_eq_zero_iff_even.mpr (htr n hn)
  obtain ⟨ht, hd⟩ := (all_power_traces_zero_iff A).mp hz
  have hm : M.map (Int.castRingHom F₂) = A := by
    ext i j
    simp [M, A]
  have hdet : Even M.det := ZMod.intCast_eq_zero_iff_even.mp (by
    change (Int.castRingHom F₂) M.det = 0
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hm, hd])
  refine ⟨htr, hdet, ?_⟩
  rw [← Matrix.charpoly_map, hm]
  exact charpoly_cases_of_trace_det A ht hd

end Psc.PeriodicPartnerFixedPointHull
