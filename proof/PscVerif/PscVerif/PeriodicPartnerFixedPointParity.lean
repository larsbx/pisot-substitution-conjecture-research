/-
Finite implications of the fixed-point parity argument in PR #636.
The twin action, the source of the eventual-range hypotheses and the signed
cohomology factor identity enter as explicit inputs.
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Psc.PeriodicPartnerFixedPointParity

open Function Polynomial

/-! ## Fixed-point and endpoint counts -/

/-- A commuting free involution pairs the fixed points of a map, provided the
fixed-point type is finite. The ambient type can be infinite. -/
theorem even_card_fixedPoints {X : Type*} (f twin : X → X) [Finite (fixedPoints f)]
    (hcomm : Function.Commute f twin) (hinv : Involutive twin) (hfree : ∀ x, twin x ≠ x) :
    Even (Nat.card (fixedPoints f)) := by
  classical
  let := Fintype.ofFinite (fixedPoints f)
  let move (x : fixedPoints f) : fixedPoints f :=
    ⟨twin x, (hcomm x).trans (congrArg twin x.property)⟩
  have hmove : Involutive move := fun x => Subtype.ext (hinv x)
  let perm : Equiv.Perm (fixedPoints f) := hmove.toPerm move
  have hsq : perm ^ 2 = 1 := by
    apply Equiv.ext
    intro x
    exact hmove x
  have hsupport : perm.support = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    exact Equiv.Perm.mem_support.mpr fun h => hfree x (congrArg Subtype.val h)
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ← hsupport, even_iff_two_dvd]
  exact Equiv.Perm.two_dvd_card_support hsq

section Endpoints

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Endpoint letters fixed by an iterate of an endpoint map. -/
def fixedLetters (g : α → α) (n : ℕ) : Finset α :=
  Finset.univ.filter fun a => g^[n] a = a

/-- The factorial bound includes each cycle of a finite endpoint map. -/
def periodicLetters (g : α → α) : Finset α :=
  fixedLetters g (Fintype.card α).factorial

@[simp] theorem mem_fixedLetters {g : α → α} {n : ℕ} {a : α} :
    a ∈ fixedLetters g n ↔ g^[n] a = a := by
  simp [fixedLetters]

@[simp] theorem mem_periodicLetters {g : α → α} {a : α} :
    a ∈ periodicLetters g ↔ a ∈ periodicPts g := by
  rw [periodicLetters, mem_fixedLetters, mem_periodicPts_iff_isPeriodicPt_factorial_card]
  rfl

private theorem fixed_subset_periodic (g : α → α) {n : ℕ} (hn : 0 < n) :
    fixedLetters g n ⊆ periodicLetters g :=
  fun _ ha => mem_periodicLetters.mpr (mk_mem_periodicPts hn (mem_fixedLetters.mp ha))

/-- An iterate restricts to a permutation on two periodic letters. Its fixed
letters number zero or two. The positive-power restriction excludes transient
letters that would also be fixed by the zeroth iterate. -/
theorem fixedLetters_card_zero_or_two (g : α → α) {n : ℕ} (hn : 0 < n)
    (hcard : (periodicLetters g).card = 2) :
    (fixedLetters g n).card = 0 ∨ (fixedLetters g n).card = 2 := by
  obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp hcard
  have hmaps := (bijOn_periodicPts g).mapsTo.iterate n
  have hinj := (bijOn_periodicPts g).injOn.iterate (bijOn_periodicPts g).mapsTo n
  have fixes_other {x y : α} (hxy : x ≠ y) (h : periodicLetters g = {x, y})
      (hx : g^[n] x = x) : g^[n] y = y := by
    have hxP : x ∈ periodicPts g := mem_periodicLetters.mp (by simp [h])
    have hyP : y ∈ periodicPts g := mem_periodicLetters.mp (by simp [h])
    have hm := mem_periodicLetters.mpr (hmaps hyP)
    rw [h, Finset.mem_insert, Finset.mem_singleton] at hm
    exact hm.resolve_left fun he => hxy (hinj hxP hyP (hx.trans he.symm))
  by_cases ha : g^[n] a = a
  · right
    suffices hf : fixedLetters g n = periodicLetters g by rwa [hf]
    apply Finset.Subset.antisymm (fixed_subset_periodic g hn)
    intro x hx
    rw [hpair, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_fixedLetters.mpr ha
    · exact mem_fixedLetters.mpr (fixes_other hab hpair ha)
  · left
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxP := fixed_subset_periodic g hn hx
    rw [hpair, Finset.mem_insert, Finset.mem_singleton] at hxP
    rcases hxP with rfl | rfl
    · exact ha (mem_fixedLetters.mp hx)
    · exact ha (fixes_other hab.symm (by rw [hpair, Finset.pair_comm]) (mem_fixedLetters.mp hx))

/-- Legal seams fixed by the last-letter and first-letter endpoint maps. The
left letter comes from the last-letter map. -/
def fixedSeams (last first : α → α) (legal : Finset (α × α)) (n : ℕ) :=
  legal.filter fun ba => last^[n] ba.1 = ba.1 ∧ first^[n] ba.2 = ba.2

/-- For a complete eventual range, the fixed seam count is the product of
the two endpoint fixed counts. -/
theorem fixedSeams_card_of_complete (last first : α → α) (legal : Finset (α × α))
    (hcomplete : (periodicLetters last ×ˢ periodicLetters first) ⊆ legal)
    {n : ℕ} (hn : 0 < n) :
    (fixedSeams last first legal n).card =
      (fixedLetters last n).card * (fixedLetters first n).card := by
  suffices h : fixedSeams last first legal n = fixedLetters last n ×ˢ fixedLetters first n by
    rw [h, Finset.card_product]
  ext ba
  simp only [fixedSeams, Finset.mem_filter, Finset.mem_product, mem_fixedLetters]
  exact ⟨And.right, fun h => ⟨hcomplete (Finset.mem_product.mpr
    ⟨mem_periodicLetters.mpr (mk_mem_periodicPts hn h.1),
      mem_periodicLetters.mpr (mk_mem_periodicPts hn h.2)⟩), h⟩⟩

/-- The rearranged counting identity transfers evenness in either direction
when both endpoint maps have two periodic letters and all four seams are legal. -/
theorem even_count_iff_even_trace (last first : α → α) (legal : Finset (α × α))
    (hleft : (periodicLetters last).card = 2) (hright : (periodicLetters first).card = 2)
    (hcomplete : (periodicLetters last ×ˢ periodicLetters first) ⊆ legal)
    {n count trace : ℕ} (hn : 0 < n)
    (hcount : count + (fixedLetters first n).card + (fixedLetters last n).card =
      trace + (fixedSeams last first legal n).card) :
    Even count ↔ Even trace := by
  rw [fixedSeams_card_of_complete last first legal hcomplete hn] at hcount
  rcases fixedLetters_card_zero_or_two first hn hright with hf | hf <;>
    rcases fixedLetters_card_zero_or_two last hn hleft with hl | hl <;>
    rw [hf, hl] at hcount <;>
    rw [Nat.even_iff, Nat.even_iff] <;> omega

end Endpoints

/-- The eventual edges are the legal words with both endpoints periodic.
Here the count of vertices is the sum of the sizes of the two endpoint sets. -/
def eventualEdges (last first : Fin 3 → Fin 3) (legal : Finset (Fin 3 × Fin 3)) :=
  (periodicLetters last ×ˢ periodicLetters first) ∩ legal

private theorem periodicLetters_nonempty : ∀ g : Fin 3 → Fin 3,
    0 < (periodicLetters g).card := by decide

private theorem periodicLetters_card_le_two {g : Fin 3 → Fin 3} (hg : ¬Injective g) :
    (periodicLetters g).card ≤ 2 := by
  have hne : periodicLetters g ≠ Finset.univ := by
    intro h
    apply hg
    rw [injective_iff_periodicPts_eq_univ, Set.eq_univ_iff_forall]
    intro a
    exact mem_periodicLetters.mp (by simp [h])
  have h := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hne⟩)
  simpa [Nat.lt_succ_iff] using h

/-- The finite graph step in Theorem R. The two implications are the inputs
from Theorem E. The edge lower bound comes from positive cycle rank in the
connected eventual range. -/
theorem complete_range_of_edge_bound (last first : Fin 3 → Fin 3)
    (legal : Finset (Fin 3 × Fin 3))
    (heLast : Injective last → (periodicLetters last).card ≤ 1)
    (heFirst : Injective first → (periodicLetters first).card ≤ 1)
    (hedges : (periodicLetters last).card + (periodicLetters first).card ≤
      (eventualEdges last first legal).card) :
    ¬Injective last ∧ ¬Injective first ∧ (periodicLetters last).card = 2 ∧
      (periodicLetters first).card = 2 ∧ (periodicLetters last ×ˢ periodicLetters first) ⊆ legal := by
  have hupper : (eventualEdges last first legal).card ≤
      (periodicLetters last).card * (periodicLetters first).card := by
    rw [← Finset.card_product]
    exact Finset.card_le_card Finset.inter_subset_left
  have hlpos := periodicLetters_nonempty last
  have hfpos := periodicLetters_nonempty first
  have hlower : 2 ≤ (periodicLetters last).card := by
    by_contra! h
    have he : (periodicLetters last).card = 1 := by omega
    simp [he] at hupper
    omega
  have hflower : 2 ≤ (periodicLetters first).card := by
    by_contra! h
    have he : (periodicLetters first).card = 1 := by omega
    simp [he] at hupper
    omega
  have hlast : ¬Injective last := fun h => by have := heLast h; omega
  have hfirst : ¬Injective first := fun h => by have := heFirst h; omega
  have hl := Nat.le_antisymm (periodicLetters_card_le_two hlast) hlower
  have hf := Nat.le_antisymm (periodicLetters_card_le_two hfirst) hflower
  refine ⟨hlast, hfirst, hl, hf, ?_⟩
  have heq : eventualEdges last first legal = periodicLetters last ×ˢ periodicLetters first := by
    refine Finset.eq_of_subset_of_card_le Finset.inter_subset_left ?_
    rw [Finset.card_product, hl, hf]
    rw [hl, hf] at hedges
    exact hedges
  rw [← heq]
  exact Finset.inter_subset_right

/-! ## Cubic Newton identities and reduction modulo two -/

section Cubic

variable {R : Type*} [CommRing R]

/-- The sum of the principal two-by-two minors. -/
def secondCoeff (A : Matrix (Fin 3) (Fin 3) R) : R :=
  (A 0 0 * A 1 1 - A 0 1 * A 1 0) +
  (A 0 0 * A 2 2 - A 0 2 * A 2 0) +
  (A 1 1 * A 2 2 - A 1 2 * A 2 1)

/-- The coefficient convention is `χ = X³ - e₁ X² + e₂ X - e₃`. -/
theorem charpoly_cubic (A : Matrix (Fin 3) (Fin 3) R) :
    A.charpoly = X ^ 3 - C A.trace * X ^ 2 + C (secondCoeff A) * X - C A.det := by
  rw [Matrix.charpoly, Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.det_fin_three]
  simp only [secondCoeff, Matrix.charmatrix_apply_eq,
    Matrix.charmatrix_apply_ne A 0 1 (by decide),
    Matrix.charmatrix_apply_ne A 0 2 (by decide),
    Matrix.charmatrix_apply_ne A 1 0 (by decide),
    Matrix.charmatrix_apply_ne A 1 2 (by decide),
    Matrix.charmatrix_apply_ne A 2 0 (by decide),
    Matrix.charmatrix_apply_ne A 2 1 (by decide), map_sub, map_add, map_mul]
  ring

/-- Newton's identities through order three, over a commutative ring. -/
theorem newton_two_three (A : Matrix (Fin 3) (Fin 3) R) :
    (A ^ 2).trace = A.trace ^ 2 - 2 * secondCoeff A ∧
    (A ^ 3).trace = A.trace ^ 3 - 3 * A.trace * secondCoeff A + 3 * A.det := by
  constructor
  · rw [pow_two]
    simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three, secondCoeff]
    ring
  · rw [pow_succ A 2, pow_two A]
    simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three, secondCoeff,
      Matrix.det_fin_three]
    ring

end Cubic

abbrev F₂ := ZMod 2

/-- The third trace detects the determinant when the first trace is zero. -/
theorem det_zero_of_first_third (A : Matrix (Fin 3) (Fin 3) F₂)
    (hs : A.trace = 0) (hthird : (A ^ 3).trace = 0) : A.det = 0 := by
  have hthree : (3 : F₂) = 1 := by decide
  have hd := (newton_two_three A).2
  rw [hthird, hs, hthree] at hd
  simpa using hd.symm

/-- Over `𝔽₂`, traces at powers one and three determine whether all positive
power traces vanish. The equivalent condition is zero trace and determinant. -/
theorem all_power_traces_zero_iff (A : Matrix (Fin 3) (Fin 3) F₂) :
    (∀ n : ℕ, 0 < n → (A ^ n).trace = 0) ↔ A.trace = 0 ∧ A.det = 0 := by
  have htwo : (2 : F₂) = 0 := by decide
  constructor
  · intro h
    have hs : A.trace = 0 := by simpa using h 1 (by decide)
    exact ⟨hs, det_zero_of_first_third A hs (h 3 (by decide))⟩
  · rintro ⟨hs, hd⟩
    have hpoly : A.charpoly = X ^ 3 + C (secondCoeff A) * X := by
      simp [charpoly_cubic, hs, hd]
    have hcube : A ^ 3 = secondCoeff A • A := by
      have h := Matrix.aeval_self_charpoly A
      rw [hpoly] at h
      simp only [map_add, map_pow, aeval_X, map_mul, aeval_C, ← Algebra.smul_def] at h
      have hchar (x : F₂) : -x = x := by decide +revert
      calc
        A ^ 3 = -(secondCoeff A • A) := eq_neg_of_add_eq_zero_left h
        _ = secondCoeff A • A := by rw [← neg_smul, hchar]
    have hfirst : ∀ n : ℕ, (A ^ (n + 1)).trace = 0 := by
      intro n
      induction n using Nat.twoStepInduction with
      | zero => simpa using hs
      | one => simpa [hs, htwo] using (newton_two_three A).1
      | more n ih _ =>
        rw [show n + 2 + 1 = 3 + n by omega, pow_add, hcube, Matrix.smul_mul, ← pow_succ',
          Matrix.trace_smul, ih, smul_zero]
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact hfirst k

/-- The parity conditions allow precisely the following two polynomial forms. -/
theorem charpoly_cases_of_trace_det (A : Matrix (Fin 3) (Fin 3) F₂)
    (ht : A.trace = 0) (hd : A.det = 0) :
    A.charpoly = X ^ 3 ∨ A.charpoly = X * (X + 1) ^ 2 := by
  rw [charpoly_cubic]
  simp only [ht, hd, map_zero, zero_mul, sub_zero]
  have cases₂ (c : F₂) : c = 0 ∨ c = 1 := by decide +revert
  rcases cases₂ (secondCoeff A) with he | he
  · exact Or.inl (by simp [he])
  · right
    have htwo : (2 : F₂[X]) = 0 := by
      rw [← map_ofNat C, show (2 : F₂) = 0 by decide, map_zero]
    rw [he, map_one, one_mul]
    linear_combination -X ^ 2 * htwo

/-- The second stage of PR #636 after the signed factor identity and degrees
have been supplied for a power. Nilpotence descends to the original matrix. -/
theorem cube_zero_of_signed_factors (A : Matrix (Fin 3) (Fin 3) F₂)
    (h r q : F₂[X]) (n j : ℕ)
    (hmonic : h.Monic) (hr : r.Monic) (hq : q.Monic)
    (hrdeg : r.natDegree = 1) (hqdeg : q.natDegree = 0)
    (hfactor : (A ^ n).charpoly = X ^ j * h) (hsign : h * r = (X + 1) * q) :
    A.charpoly = X ^ 3 ∧ A ^ 3 = 0 := by
  have hqone := hq.natDegree_eq_zero.mp hqdeg
  have hd := congrArg natDegree hsign
  rw [hqone, mul_one, natDegree_mul hmonic.ne_zero hr.ne_zero, hrdeg,
    ← C_1, natDegree_X_add_C] at hd
  have hhone := hmonic.natDegree_eq_zero.mp (by omega : h.natDegree = 0)
  rw [hhone, mul_one] at hfactor
  have hj := congrArg natDegree hfactor
  simp only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, natDegree_X_pow] at hj
  rw [← hj] at hfactor
  have hpow : (A ^ n) ^ 3 = 0 := by
    simpa only [hfactor, map_pow, aeval_X] using Matrix.aeval_self_charpoly (A ^ n)
  have hnil : IsNilpotent A := ⟨n * 3, by rwa [pow_mul]⟩
  have horiginal : A.charpoly = X ^ 3 := by
    simpa only [Fintype.card_fin] using
      sub_eq_zero.mp (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hnil).eq_zero
  exact ⟨horiginal, by
    simpa only [horiginal, map_pow, aeval_X] using Matrix.aeval_self_charpoly A⟩

/-! ## Boundary controls -/

private def swapsTwo : Fin 3 → Fin 3 := ![1, 0, 0]
private def fixesTwo : Fin 3 → Fin 3 := ![0, 1, 0]

-- The transient third letter is fixed only by the zeroth iterate.
example : (fixedLetters swapsTwo 0).card = 3 ∧ (fixedLetters swapsTwo 1).card = 0 ∧
    (fixedLetters swapsTwo 2).card = 2 := by decide

-- An incomplete eventual range can have an odd fixed seam count.
example : (fixedLetters fixesTwo 1).card = 2 ∧
    (fixedSeams fixesTwo fixesTwo {(0, 0), (0, 1), (1, 1)} 1).card = 3 := by decide

-- The exact incidence of 1/1222/2011 on the alphabet 0,1,2.
private def oddDet : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 1; 1, 1, 2; 0, 3, 1]

example : oddDet.trace = 2 ∧ (oddDet ^ 2).trace = 14 ∧ (oddDet ^ 3).trace = 47 ∧
    oddDet.det = 3 := by decide

-- The non-nilpotent residue is compatible with zero trace at every power.
private def secondResidue : Matrix (Fin 3) (Fin 3) F₂ := !![1, 0, 0; 0, 1, 0; 0, 0, 0]

example : (∀ n : ℕ, 0 < n → (secondResidue ^ n).trace = 0) ∧ secondResidue ^ 3 ≠ 0 := by
  refine ⟨(all_power_traces_zero_iff secondResidue).mpr ⟨by decide, by decide⟩, ?_⟩
  intro h
  have h00 := congrFun (congrFun h 0) 0
  exact (by decide : (secondResidue ^ 3) 0 0 ≠ 0) h00

end Psc.PeriodicPartnerFixedPointParity
