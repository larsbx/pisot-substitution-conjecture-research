/-
# Literal one-level density and the finite center-count obstruction

These theorems bind the three literal words, their actual letter counts,
and the numerical boundary allowance used by the lower minus-Class-A proof.
The packing lemma concerns finite separated points in actual short intervals.
Applying these estimates to every inflated common interval still requires
the explicit word/interval decomposition and center-assignment interfaces.

Pre-code gate: `docs/bh-class-a-literal-lean-stop-go-2026-11-14.md`.
-/
import PscVerif.ClassAMinusLiteralArithmetic

namespace Psc.ClassAMinusDensity

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn Psc.ClassAZeroDefectEscape Matrix
open scoped BigOperators

/-- Counts of the original literal images in coordinate order `(x,c,y)`.
The natural subtraction in the y-image is retained exactly. -/
theorem literal_counts (n d : ℕ) :
    (∀ b, (sigma n d 0).count b = ![2, 0, n+d] b) ∧
    (∀ b, (sigma n d 1).count b = ![1, 1, n] b) ∧
    (∀ b, (sigma n d 2).count b = ![1, 1, n-1] b) := by
  constructor
  · intro b
    fin_cases b <;> simp [sigma, first, last, runLength, List.count_replicate]
  constructor
  · intro b
    fin_cases b <;> simp [sigma, first, last, runLength, List.count_replicate]
  · intro b
    fin_cases b <;> simp [sigma, first, last, runLength, List.count_replicate]

theorem literal_lengths (n d : ℕ) :
    (sigma n d 0).length = n+d+2 ∧
    (sigma n d 1).length = n+2 ∧
    (sigma n d 2).length = (n-1)+2 := by
  simp [sigma, first, last, runLength]

theorem literal_block_size_bound (n d : ℕ) (hd : d+1 ≤ n) (a : Fin 3) :
    (sigma n d a).length ≤ n+d+2 ∧ n+d+2 ≤ 2*n+1 := by
  fin_cases a <;> simp [sigma, first, last, runLength] <;> omega

/-- Literal physical lengths use actual counts, independently of any
asserted spectral identification. -/
theorem literal_physical_lengths (n d : ℕ) (ℓ : Fin 3 → ℝ) (hy : ℓ 2 = 1) :
    physicalLength ℓ (sigma n d 0) = 2*ℓ 0+(n:ℝ)+d ∧
    physicalLength ℓ (sigma n d 1) = ℓ 0+ℓ 1+n ∧
    physicalLength ℓ (sigma n d 2) = ℓ 0+ℓ 1+(n-1:ℕ) := by
  simp [physicalLength, dotProduct, Fin.sum_univ_succ, sigma, first, last,
    runLength, List.count_replicate, hy]
  constructor
  · ring
  constructor <;> ring

/-- One-level density estimates, expressed against actual word lengths.
All geometric inputs remain explicit until the literal-root wrapper is used. -/
theorem one_level_density (n d : ℕ) (hn : 1 ≤ n)
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hβ : (n:ℝ)+1 < β)
    (hy : ℓ 2 = 1) (hc : ℓ 1 = 1+1/β)
    (hxlo : 1 < ℓ 0) (hxhi : ℓ 0 < 2)
    (hscale : ∀ a, physicalLength ℓ (sigma n d a) = β*ℓ a)
    (a : Fin 3) :
    (((n:ℝ)-1)/β)*physicalLength ℓ (sigma n d a) ≤
        ((sigma n d a).count 2 : ℝ) ∧
    ((sigma n d a).count 0 : ℝ) ≤
        (2/(β*ℓ 0))*physicalLength ℓ (sigma n d a) ∧
    ((sigma n d a).count 1 : ℝ) ≤
        (1/β)*physicalLength ℓ (sigma n d a) := by
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hβpos : 0 < β := by linarith
  have hβne : β ≠ 0 := ne_of_gt hβpos
  have hxpos : 0 < ℓ 0 := by linarith
  have hxne : ℓ 0 ≠ 0 := ne_of_gt hxpos
  have hcpos : 1 < ℓ 1 := by
    have : 0 < 1/β := one_div_pos.mpr hβpos
    rw [hc]
    linarith
  have hyfactor : ∀ a, (((n:ℝ)-1)/β)*physicalLength ℓ (sigma n d a) =
      ((n:ℝ)-1)*ℓ a := by
    intro a
    rw [hscale]
    field_simp
  have hxfactor : ∀ a, (2/(β*ℓ 0))*physicalLength ℓ (sigma n d a) =
      (2*ℓ a)/ℓ 0 := by
    intro a
    rw [hscale]
    field_simp
  have hcfactor : ∀ a, (1/β)*physicalLength ℓ (sigma n d a) = ℓ a := by
    intro a
    rw [hscale]
    field_simp
  rw [hyfactor, hxfactor, hcfactor]
  have hcounts := literal_counts n d
  have hlens := literal_physical_lengths n d ℓ hy
  fin_cases a
  · norm_num [sigma, first, last, runLength, List.count_replicate]
    have hlength := hscale 0
    rw [hlens.1] at hlength
    constructor
    · nlinarith [mul_pos (show 0 < β-((n:ℝ)+1) by linarith) hxpos]
    constructor
    · exact (le_div_iff₀ hxpos).2 (by ring_nf; rfl)
    · exact hxpos.le
  · norm_num [sigma, first, last, runLength, List.count_replicate]
    constructor
    · rw [hc, mul_add, mul_one]
      have hfrac : ((n:ℝ)-1)/β < 1 := (div_lt_one hβpos).2 (by linarith)
      have heq : ((n:ℝ)-1)*(1/β) = ((n:ℝ)-1)/β := by ring
      rw [heq]
      linarith
    constructor
    · apply (le_div_iff₀ hxpos).2
      nlinarith
    · exact hcpos.le
  · norm_num [sigma, first, last, runLength, List.count_replicate, hy]
    constructor
    · rw [Nat.cast_sub hn]
      norm_num
    · apply (le_div_iff₀ hxpos).2
      linarith

/-- The one-level estimates sum over any actual finite list of image
blocks; no frequency or convergence hypothesis is supplied. -/
theorem density_flatMap (n d : ℕ) (ℓ : Fin 3 → ℝ) (Y X C : ℝ)
    (hblock : ∀ a,
      Y*physicalLength ℓ (sigma n d a) ≤ ((sigma n d a).count 2 : ℝ) ∧
      ((sigma n d a).count 0 : ℝ) ≤ X*physicalLength ℓ (sigma n d a) ∧
      ((sigma n d a).count 1 : ℝ) ≤ C*physicalLength ℓ (sigma n d a))
    (w : List (Fin 3)) :
    Y*physicalLength ℓ (w.flatMap (sigma n d)) ≤
        ((w.flatMap (sigma n d)).count 2 : ℝ) ∧
    ((w.flatMap (sigma n d)).count 0 : ℝ) ≤
        X*physicalLength ℓ (w.flatMap (sigma n d)) ∧
    ((w.flatMap (sigma n d)).count 1 : ℝ) ≤
        C*physicalLength ℓ (w.flatMap (sigma n d)) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.flatMap_cons, physicalLength_append, List.count_append,
      Nat.cast_add, mul_add]
    exact ⟨add_le_add (hblock a).1 ih.1,
      add_le_add (hblock a).2.1 ih.2.1,
      add_le_add (hblock a).2.2 ih.2.2⟩

/-- The strict numerical reserve used in the lower chamber. -/
theorem density_reserve (n : ℕ) (hn : 6 ≤ n) (β Lx : ℝ)
    (hβpos : 0 < β) (hβhi : β < n+2)
    (hx : 1+5/((n:ℝ)+1) < Lx) :
    1/12 < (((n:ℝ)-3)-4/Lx)/β := by
  have hnR : 6 ≤ (n:ℝ) := by exact_mod_cast hn
  have hnp : 0 < (n:ℝ)+1 := by linarith
  have hx1 : 1 < Lx := by
    have : 0 < (5:ℝ)/((n:ℝ)+1) := div_pos (by norm_num) hnp
    linarith
  have hxpos : 0 < Lx := by linarith
  apply (lt_div_iff₀ hβpos).2
  by_cases h6 : n = 6
  · subst n
    norm_num at hx hβhi ⊢
    have hf : 4/Lx < 7/3 := (div_lt_iff₀ hxpos).2 (by nlinarith)
    linarith
  by_cases h7 : n = 7
  · subst n
    norm_num at hx hβhi ⊢
    have hf : 4/Lx < 5/2 := (div_lt_iff₀ hxpos).2 (by nlinarith)
    linarith
  · have hn8 : 8 ≤ n := by omega
    have hn8R : 8 ≤ (n:ℝ) := by exact_mod_cast hn8
    have hf : 4/Lx < 4 := (div_lt_iff₀ hxpos).2 (by linarith)
    linarith

/-- Boundary truncation loses at most two full-block lengths below,
and two block letter budgets above. These are implications from the
explicit finite decomposition data, not assumed all-source density. -/
theorem boundary_count_bounds (Y X C J L B W : ℝ)
    (hY : 0 ≤ Y) (hY1 : Y ≤ 1) (hX : 0 ≤ X) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (hcover : J-2*B ≤ L) (hinside : L ≤ J)
    (fy fx fc ny nx nc : ℕ)
    (hy : Y*L ≤ fy) (hx : (fx:ℝ) ≤ X*L) (hc : (fc:ℝ) ≤ C*L)
    (hb_y : fy ≤ ny) (hb_x : (nx:ℝ) ≤ fx+2*W) (hb_c : (nc:ℝ) ≤ fc+2*W) :
    Y*J-2*B ≤ ny ∧ (nx:ℝ) ≤ X*J+2*W ∧ (nc:ℝ) ≤ C*J+2*W := by
  have hyy : (fy:ℝ) ≤ ny := by exact_mod_cast hb_y
  constructor
  · nlinarith [mul_nonneg hY (show 0 ≤ L-(J-2*B) by linarith),
      mul_nonneg (show 0 ≤ 1-Y by linarith) hB]
  constructor
  · nlinarith [mul_nonneg hX (sub_nonneg.mpr hinside)]
  · nlinarith [mul_nonneg hC (sub_nonneg.mpr hinside)]

/-- A short closed tile contains at most two distinct centers separated
by unit distance. The strict length bound is essential. -/
theorem short_interval_packing {α : Type*} (s : Finset α) (pos : α → ℝ)
    (lo len : ℝ) (hlen : len < 2)
    (hinside : ∀ a ∈ s, lo ≤ pos a ∧ pos a ≤ lo+len)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → 1 ≤ |pos a-pos b|) :
    s.card ≤ 2 := by
  by_contra hcard
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ :=
    Finset.two_lt_card_iff.mp (show 2 < s.card by omega)
  have ha' := hinside a ha
  have hb' := hinside b hb
  have hc' := hinside c hc
  rcases le_abs.mp (hsep a ha b hb hab) with hab' | hab' <;>
    rcases le_abs.mp (hsep a ha c hc hac) with hac' | hac' <;>
      rcases le_abs.mp (hsep b hb c hc hbc) with hbc' | hbc' <;> linarith

/-- Sum the proved two-center capacity over an actual finite assignment.
The assignment retains the original center and tile identities. -/
theorem finite_center_packing {α κ : Type*} [DecidableEq κ]
    (centers : Finset α) (tiles : Finset κ) (assign : α → κ)
    (pos : α → ℝ) (left len : κ → ℝ)
    (hassign : ∀ a ∈ centers, assign a ∈ tiles)
    (hlen : ∀ t ∈ tiles, len t < 2)
    (hinside : ∀ a ∈ centers,
      left (assign a) ≤ pos a ∧ pos a ≤ left (assign a)+len (assign a))
    (hsep : ∀ a ∈ centers, ∀ b ∈ centers, a ≠ b → 1 ≤ |pos a-pos b|) :
    centers.card ≤ 2*tiles.card := by
  classical
  have hfiber : ∀ t ∈ tiles, (centers.filter (fun a => assign a=t)).card ≤ 2 := by
    intro t ht
    apply short_interval_packing _ pos (left t) (len t) (hlen t ht)
    · intro a ha
      obtain ⟨ha, he⟩ := Finset.mem_filter.mp ha
      simpa only [he] using hinside a ha
    · intro a ha b hb hab
      exact hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
  rw [Finset.card_eq_sum_card_fiberwise hassign]
  calc
    ∑ t ∈ tiles, (centers.filter (fun a => assign a=t)).card ≤ ∑ _t ∈ tiles, 2 :=
      Finset.sum_le_sum hfiber
    _ = 2*tiles.card := by simp [Nat.mul_comm]

/-- At most two boundary tiles give precisely the additive four in the
finite center-count inequality. -/
theorem center_packing_with_boundaries {α κ : Type*} [DecidableEq κ]
    (centers : Finset α) (tiles : Finset κ) (assign : α → κ)
    (pos : α → ℝ) (left len : κ → ℝ) (nx nc : ℕ)
    (htiles : tiles.card ≤ nx+nc+2)
    (hassign : ∀ a ∈ centers, assign a ∈ tiles)
    (hlen : ∀ t ∈ tiles, len t < 2)
    (hinside : ∀ a ∈ centers,
      left (assign a) ≤ pos a ∧ pos a ≤ left (assign a)+len (assign a))
    (hsep : ∀ a ∈ centers, ∀ b ∈ centers, a ≠ b → 1 ≤ |pos a-pos b|) :
    centers.card ≤ 2*nx+2*nc+4 := by
  have hp := finite_center_packing centers tiles assign pos left len hassign hlen hinside hsep
  omega

/-- The center-packing upper bound is incompatible with the three lower
chamber density estimates once the original common interval reaches the
stated threshold. The proof quantifies over actual finite counts, and
does not assume any recurrence or finite overlap carrier. -/
theorem center_count_contradiction (n : ℕ) (Y X C J B W : ℝ)
    (hgap : 1/12 < Y-2*X-2*C) (hJ : 240*((n:ℝ)+1) ≤ J)
    (hB : B < 2*((n:ℝ)+2)) (hW : W ≤ 2*(n:ℝ)+1)
    (ny nx nc : ℕ)
    (hy : Y*J-2*B ≤ ny) (hx : (nx:ℝ) ≤ X*J+2*W)
    (hc : (nc:ℝ) ≤ C*J+2*W)
    (hpack : ny ≤ 2*nx+2*nc+4) : False := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hJpos : 0 < J := by nlinarith
  have hpackR : (ny:ℝ) ≤ 2*(nx:ℝ)+2*(nc:ℝ)+4 := by exact_mod_cast hpack
  have hprod := mul_pos (show 0 < Y-2*X-2*C-1/12 by linarith) hJpos
  nlinarith

open Psc.ClassAMinusLiteralArithmetic

/-- Every one-level bound is discharged by the literal lower-chamber
cubic data. Perron identification is not an extra unnamed premise. -/
theorem literal_one_level_density (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (a : Fin 3) :
    (((n:ℝ)-1)/β)*physicalLength (lengths n β) (sigma n d a) ≤
        ((sigma n d a).count 2 : ℝ) ∧
    ((sigma n d a).count 0 : ℝ) ≤
        (2/(β*lengths n β 0))*physicalLength (lengths n β) (sigma n d a) ∧
    ((sigma n d a).count 1 : ℝ) ≤
        (1/β)*physicalLength (lengths n β) (sigma n d a) := by
  have hb := literal_lengths_bounds n d hd hn β hroot
  exact one_level_density n d (by omega) (lengths n β) β hroot.lower
    hb.2.2.2.1 rfl (hb.1.trans hb.2.1) hb.2.2.1
    (literal_length_scaling n d hd hn β hroot) a

/-- The literal density reserve, with all coefficient inequalities proved
from the displayed cubic and lower-chamber parameters. -/
theorem literal_density_reserve (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) :
    1/12 < ((n:ℝ)-1)/β-2*(2/(β*lengths n β 0))-2*(1/β) := by
  have hβ : β ≠ 0 := ne_of_gt (root_pos hroot)
  have hx : lengths n β 0 ≠ 0 := ne_of_gt (literal_lengths_pos n d hd hn β hroot 0)
  have heq : ((n:ℝ)-1)/β-2*(2/(β*lengths n β 0))-2*(1/β) =
      (((n:ℝ)-3)-4/(lengths n β 0))/β := by
    field_simp
    ring
  rw [heq]
  exact density_reserve n (lower_chamber_n n d hd hn) β (lengths n β 0)
    (root_pos hroot) hroot.upper (literal_x_length_lower n d hd hn β hroot)

/-- Exact lower-chamber specialization of the finite packing
contradiction. The supplied count inequalities are the explicit remaining
interface for decomposing the actual common interval into image blocks. -/
theorem literal_center_count_contradiction (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (J : ℝ)
    (hJ : 240*((n:ℝ)+1) ≤ J) (ny nx nc : ℕ)
    (hy : (((n:ℝ)-1)/β)*J-2*(β*lengths n β 0) ≤ ny)
    (hx : (nx:ℝ) ≤ (2/(β*lengths n β 0))*J+2*(n+d+2:ℕ))
    (hc : (nc:ℝ) ≤ (1/β)*J+2*(n+d+2:ℕ))
    (hpack : ny ≤ 2*nx+2*nc+4) : False := by
  have hb := literal_lengths_bounds n d hd hn β hroot
  have hB : β*lengths n β 0 < 2*((n:ℝ)+2) := by
    calc
      β*lengths n β 0 < β*2 := mul_lt_mul_of_pos_left hb.2.2.1 (root_pos hroot)
      _ < 2*((n:ℝ)+2) := by nlinarith [hroot.upper]
  have hW : ((n+d+2:ℕ):ℝ) ≤ 2*(n:ℝ)+1 := by
    exact_mod_cast (literal_block_size_bound n d hn 0).2
  exact center_count_contradiction n (((n:ℝ)-1)/β) (2/(β*lengths n β 0)) (1/β)
    J (β*lengths n β 0) (n+d+2:ℕ) (literal_density_reserve n d hd hn β hroot)
    hJ hB hW ny nx nc hy hx hc hpack

/-- Every positive original overlap length eventually exceeds the
sufficient count threshold under expansion. The generation depends on
that length; there is no uniform source-independent depth claim. -/
theorem density_threshold_exists (n : ℕ) (β ell : ℝ)
    (hβ : 1 < β) (hell : 0 < ell) :
    ∃ m : ℕ, 1 ≤ m ∧ 240*((n:ℝ)+1) ≤ β^m*ell := by
  obtain ⟨k, _, hk⟩ := exists_nat_pow_near
    (x := max 1 (240*((n:ℝ)+1)/ell)) (y := β) (le_max_left _ _) hβ
  refine ⟨k+1, by omega, ?_⟩
  have ht : 240*((n:ℝ)+1)/ell < β^(k+1) :=
    lt_of_le_of_lt (le_max_right _ _) hk
  exact ((div_lt_iff₀ hell).mp ht).le

/-- Equality of the short-interval bound is unsafe: three separated
centers fit in a closed interval of length exactly two. -/
theorem length_two_packing_control :
    (0:ℝ) ∈ Set.Icc 0 2 ∧ 1 ∈ Set.Icc (0:ℝ) 2 ∧ 2 ∈ Set.Icc (0:ℝ) 2 ∧
    1 ≤ |(0:ℝ)-1| ∧ 1 ≤ |(0:ℝ)-2| ∧ 1 ≤ |(1:ℝ)-2| := by
  norm_num

end Psc.ClassAMinusDensity
