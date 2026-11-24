/-
# Quantitative central-tail and literal cycle-exit bounds

The finite pair count retains both integral initial coordinates.  A repeated
pair is found among the first K+1 pairs, rather than supplied at an unknown
index.  Existing periodic classification then gives a constant transformed
tail before K.  This does not identify a full packet until one further step.

Pre-code contract: docs/bh-class-a-plus-upper-recurrence-stop-go-2026-11-15.md.
-/
import PscVerif.ClassAPlusUpperRecurrence
import PscVerif.ClassAPlusUpperCycleCompletion

namespace Psc.ClassAPlusUpperCentralBound

open Psc.ClassAPlusUpperRecurrence Psc.ClassAPlusUpperCycles
open Psc.ClassAPlusUpperCycleCompletion

/-- The number of possible ordered integral pairs in the proved forward box. -/
def pairCount (n : ℕ) (a b : ℤ) : ℕ :=
  (2 * (initialBound n a b).toNat + 1)^2

/-- A repeated pair starts strictly before the finite pair count. -/
theorem bounded_periodic_tail (n J : ℕ) (β : ℝ) (hp : Family n J β)
    (u : ℕ → ℤ)
    (hrec : ∀ k, Nearest (A β) (C n β) (u k) (u (k+1)) (u (k+2))) :
    ∃ N T : ℕ, N < pairCount n (u 0) (u 1) ∧ 0 < T ∧
      ∀ m, u (N+(m+T)) = u (N+m) := by
  classical
  let B := initialBound n (u 0) (u 1)
  let K := pairCount n (u 0) (u 1)
  have hB : 0 ≤ B := by dsimp [B, initialBound]; positivity
  let S : Finset ℤ := Finset.Icc (-B) B
  have hbound := family_forward_bound n J β hp u hrec
  have hmem : ∀ k, u k ∈ S := fun k => Finset.mem_Icc.mpr (abs_le.mp (hbound k))
  have hcardS : S.card = 2*B.toNat+1 := by
    rw [show S = Finset.Icc (-B) B from rfl, Int.card_Icc]
    omega
  let pairs : Fin (K+1) → ({z : ℤ // z ∈ S} × {z : ℤ // z ∈ S}) :=
    fun k => (⟨u k, hmem k⟩, ⟨u (k+1), hmem (k+1)⟩)
  have hcard : Fintype.card ({z : ℤ // z ∈ S} × {z : ℤ // z ∈ S}) <
      Fintype.card (Fin (K+1)) := by
    simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, hcardS]
    change (2*B.toNat+1)*(2*B.toNat+1) < (2*B.toNat+1)^2+1
    nlinarith
  obtain ⟨i, j, hij, hpairs⟩ := Fintype.exists_ne_map_eq_of_card_lt pairs hcard
  have hfirst : u i = u j := congrArg (fun z => z.1.val) hpairs
  have hsecond : u (i+1) = u (j+1) := congrArg (fun z => z.2.val) hpairs
  have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  have hc : ∀ k, ClassACentralRecurrence.Nearest (-(A β)/2) (-(C n β))
      (u k) (u (k+1)) (u (k+2)) :=
    fun k => (ClassAPlusConstantRecurrence.nearest_central_iff _ _ _ _ _).1 (hrec k)
  have build : ∀ i j : ℕ, i < j → j ≤ K → u i = u j → u (i+1) = u (j+1) →
      ∃ N T : ℕ, N < K ∧ 0 < T ∧ ∀ m, u (N+(m+T)) = u (N+m) := by
    intro i j hlt hjK hi hj
    refine ⟨i, j-i, by omega, by omega, ?_⟩
    intro m
    have hh := (ClassACentralRecurrence.repeated_pair_tail u hc hi hj m).1.symm
    simpa only [show i+(m+(j-i)) = j+m by omega] using hh
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact build i j hlt (by have := j.isLt; omega) hfirst hsecond
  · exact build j i hlt (by have := i.isLt; omega) hfirst.symm hsecond.symm

/-- Classification starts at the bounded repeated pair, including the high-J
branch; no later, unbounded tail index is substituted. -/
theorem bounded_constant_tail (n J : ℕ) (β : ℝ) (hp : Family n J β)
    (u : ℕ → ℤ)
    (hrec : ∀ k, Nearest (A β) (C n β) (u k) (u (k+1)) (u (k+2))) :
    ∃ N : ℕ, ∃ H : ℤ, N < pairCount n (u 0) (u 1) ∧
      |V n β*(H : ℝ)| < 1/2 ∧ ∀ m, u (N+m) = H := by
  obtain ⟨N, T, hN, hT, hperiod⟩ := bounded_periodic_tail n J β hp u hrec
  let v : ℕ → ℤ := fun m => u (N+m)
  have hvp : Function.Periodic v T := hperiod
  have hvr : ∀ m, Nearest (A β) (C n β) (v m) (v (m+1)) (v (m+2)) := by
    intro m
    simpa only [v, Nat.add_assoc] using hrec (N+m)
  have classified : ∃ H : ℤ, |V n β*(H : ℝ)| < 1/2 ∧ ∀ m, v m = H := by
    by_cases hJ : 5 ≤ J
    · exact ClassAPlusConstantRecurrence.nat_periodic_classification
        ⟨hp.A_pos.le, lt_trans hp.A_lt_quarter (by norm_num), hp.C_pos,
          (hp.high_contraction hJ).1⟩ v T hT hvp hvr
    · exact energy_periodic_constant (A β) (C n β) hp.A_pos.le
        (hp.low_shear (by omega)).2.le v T hT hvp hvr
  obtain ⟨H, hamp, hconst⟩ := classified
  exact ⟨N, H, hN, hamp, hconst⟩

/-- Quantitative original-coordinate tail; full packet reconstruction still
uses the existing one-step delay theorem. -/
theorem bounded_alternating_tail (n J : ℕ) (β : ℝ) (hp : Family n J β)
    (u : ℕ → ℤ)
    (hrec : ∀ k, OriginalNearest (A β) (C n β) (u k) (u (k+1)) (u (k+2))) :
    ∃ N : ℕ, ∃ H : ℤ, N < pairCount n (u 0) (u 1) ∧ 0 ≤ H ∧
      V n β*(H : ℝ) < 1/2 ∧ (∀ m, |u (N+m)| = H) ∧
      (∀ m, u (N+m+1) = -u (N+m)) := by
  obtain ⟨N, H, hN, hamp, hconst⟩ := bounded_constant_tail n J β hp (twist u)
    (twist_recurrence (A β) (C n β) u hrec)
  refine ⟨N, |H|, ?_, abs_nonneg H, ?_, ?_, ?_⟩
  · simpa only [pairCount, initialBound, twist_abs] using hN
  · simpa only [Int.cast_abs, abs_mul, abs_of_pos hp.V_pos] using hamp
  · intro m
    have hh := congrArg (fun z : ℤ => |z|) (hconst m)
    simpa only [twist_abs] using hh
  · intro m
    apply (twist_next_eq_iff u (N+m)).1
    rw [show N+m+1 = N+(m+1) by omega, hconst (m+1), hconst m]

/-- Literal height recursion has at most two edges per height plus one. -/
theorem all_indices_length_le (n J H : ℕ) :
    (allIndices n J H).length ≤ 2*H+1 := by
  induction H with
  | zero => simp [allIndices]
  | succ H ih =>
    change (if 3 ≤ J*(H+1) then decrementIndices J (H+1) ++ allIndices n J H
      else if J=1 then baseOneIndices n (H+1) else baseTwoIndices n).length ≤ 2*(H+1)+1
    split_ifs with hlarge hj
    · simp only [List.length_append, decrementIndices, List.length_cons, List.length_nil]
      omega
    · simp only [baseOneIndices, List.length_cons, List.length_nil]
      omega
    · simp only [baseTwoIndices, List.length_cons, List.length_nil]
      omega

/-- Reversal exchanges full tracks and does not add an edge. -/
theorem signed_indices_length_le (reversed : Bool) (n J H : ℕ) :
    (allSignedIndices reversed n J H).length ≤ 2*H+1 := by
  cases reversed <;> simpa [allSignedIndices] using all_indices_length_le n J H

end Psc.ClassAPlusUpperCentralBound
