import PscVerif.PhysicalMass
import Mathlib.Data.Fintype.Card

/-!
# Literal occurrence counts and the physical mass interface

The indices in each row are occurrence identities.  Two indices with the
same target contribute twice.  A selected subfamily has a deficit equal to
the masses of exactly the omitted occurrences, provided the complete row
has the stated subdivision identity.

For a finite ordered multigraph and a supplied quotient, uniform forward
and incoming degrees on quotient fibers imply the weighted transpose
correspondence by double counting.  Uniformity, completeness of the edge
inventory, and geometric meaning are not manufactured by these lemmas.

The pre-code decision is `docs/c4-overlap-mass-literature-2026-11-10.md`.
The weighted matrix algebra is reused from `PhysicalMass`.
-/

namespace PscVerif.OccurrenceMassCounts

open scoped BigOperators

section Rows

variable {ι κ : Type*}

/-- Count occurrences in one row, retaining repeated equal target labels. -/
noncomputable def rowCount (target : κ → ι) (retained : Finset κ) (j : ι) : ℕ := by
  classical
  exact (retained.filter (fun e => target e = j)).card

/-- Grouping over a supplied finite label support, with omitted labels
visible as zero indicator terms.  The target type need not be finite. -/
theorem sum_rowCount_on [DecidableEq ι] (target : κ → ι) (retained : Finset κ)
    (labels : Finset ι) (h : ι → ℝ) :
    (∑ j ∈ labels, (rowCount target retained j : ℝ) * h j) =
      ∑ e ∈ retained, if target e ∈ labels then h (target e) else 0 := by
  convert (Finset.sum_fiberwise_eq_sum_filter' retained labels target h) using 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_const, nsmul_eq_mul]
    apply congrArg (fun n : ℕ => (n : ℝ) * h j)
    unfold rowCount
    apply congrArg Finset.card
    ext e
    simp only [Finset.mem_filter]
  · exact (Finset.sum_filter _ _).symm

/-- A finite support retaining every nonzero mass preserves the whole
occurrence sum even when zero-mass labels lie outside that support. -/
theorem sum_rowCount_on_of_zero_outside [DecidableEq ι]
    (target : κ → ι) (retained : Finset κ) (labels : Finset ι) (h : ι → ℝ)
    (outside : ∀ e ∈ retained, target e ∉ labels → h (target e) = 0) :
    (∑ j ∈ labels, (rowCount target retained j : ℝ) * h j) =
      ∑ e ∈ retained, h (target e) := by
  rw [sum_rowCount_on]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hin : target e ∈ labels
  · simp [hin]
  · simp [hin, outside e he hin]

/-- Grouping by the target label preserves every occurrence summand. -/
theorem sum_rowCount [Fintype ι] (target : κ → ι) (retained : Finset κ)
    (h : ι → ℝ) :
    (∑ j, (rowCount target retained j : ℝ) * h j) =
      ∑ e ∈ retained, h (target e) := by
  classical
  simpa only [rowCount, Finset.sum_const, nsmul_eq_mul] using
    (Finset.sum_fiberwise' retained target h)

end Rows

section RowFamilies

variable {ι : Type*} [Fintype ι] {κ : ι → Type*}

/-- Row-parent to column-child forward counts, with real coefficients for
the existing mass consumer.  `retained` is a set of occurrence identities. -/
noncomputable def matrixCount (target : (i : ι) → κ i → ι)
    (retained : (i : ι) → Finset (κ i)) : ι → ι → ℝ :=
  fun i j => (rowCount (target i) (retained i) j : ℝ)

omit [Fintype ι] in
theorem matrixCount_nonneg (target : (i : ι) → κ i → ι)
    (retained : (i : ι) → Finset (κ i)) (i j : ι) :
    0 ≤ matrixCount target retained i j := Nat.cast_nonneg _

theorem action_matrixCount (target : (i : ι) → κ i → ι)
    (retained : (i : ι) → Finset (κ i)) (h : ι → ℝ) (i : ι) :
    PhysicalMass.action (matrixCount target retained) h i =
      ∑ e ∈ retained i, h (target i e) :=
  sum_rowCount (target i) (retained i) h

/-- The omitted family is a difference of occurrence sets, not a difference
of target-label supports.  Zero-mass occurrences contribute zero. -/
noncomputable def omittedMass (target : (i : ι) → κ i → ι)
    (all retained : (i : ι) → Finset (κ i)) (h : ι → ℝ) (i : ι) : ℝ := by
  classical
  exact ∑ e ∈ all i \ retained i, h (target i e)

omit [Fintype ι] in
theorem omittedMass_nonneg (target : (i : ι) → κ i → ι)
    (all retained : (i : ι) → Finset (κ i)) (h : ι → ℝ)
    (hh : ∀ j, 0 ≤ h j) (i : ι) :
    0 ≤ omittedMass target all retained h i := by
  classical
  exact Finset.sum_nonneg (fun e _ => hh (target i e))

theorem retained_add_omitted (target : (i : ι) → κ i → ι)
    (all retained : (i : ι) → Finset (κ i)) (h : ι → ℝ)
    (subset : ∀ i, retained i ⊆ all i) (i : ι) :
    PhysicalMass.action (matrixCount target retained) h i +
      omittedMass target all retained h i = ∑ e ∈ all i, h (target i e) := by
  classical
  rw [action_matrixCount, omittedMass, add_comm]
  exact Finset.sum_sdiff (subset i)

/-- A deficit is exactly the omitted occurrence mass, conditional on the
complete subdivision identity.  No geometric exclusion is asserted. -/
theorem deficit_eq_omitted (target : (i : ι) → κ i → ι)
    (all retained : (i : ι) → Finset (κ i)) (h : ι → ℝ) (β : ℝ)
    (subset : ∀ i, retained i ⊆ all i)
    (complete : ∀ i, (∑ e ∈ all i, h (target i e)) = β * h i) (i : ι) :
    β * h i - PhysicalMass.action (matrixCount target retained) h i =
      omittedMass target all retained h i := by
  have split := retained_add_omitted target all retained h subset i
  rw [complete i] at split
  linarith

theorem forward_budget (target : (i : ι) → κ i → ι)
    (all retained : (i : ι) → Finset (κ i)) (h : ι → ℝ) (β : ℝ)
    (hh : ∀ j, 0 ≤ h j) (subset : ∀ i, retained i ⊆ all i)
    (complete : ∀ i, (∑ e ∈ all i, h (target i e)) = β * h i) :
    ∀ i, PhysicalMass.action (matrixCount target retained) h i ≤ β * h i := by
  intro i
  have nonneg := omittedMass_nonneg target all retained h hh i
  rw [← deficit_eq_omitted target all retained h β subset complete i] at nonneg
  exact sub_nonneg.mp nonneg

/-- Strict arithmetic loss occurs exactly when a genuinely positive
occurrence has been omitted.  The omission still needs external justification. -/
theorem strict_forward_loss_iff (target : (i : ι) → κ i → ι)
    (all retained : (i : ι) → Finset (κ i)) (h : ι → ℝ) (β : ℝ)
    (hh : ∀ j, 0 ≤ h j) (subset : ∀ i, retained i ⊆ all i)
    (complete : ∀ i, (∑ e ∈ all i, h (target i e)) = β * h i) (i : ι) :
    PhysicalMass.action (matrixCount target retained) h i < β * h i ↔
      ∃ e ∈ all i, e ∉ retained i ∧ 0 < h (target i e) := by
  classical
  rw [← sub_pos, deficit_eq_omitted target all retained h β subset complete i]
  simp only [omittedMass, Finset.sum_pos_iff_of_nonneg (fun e _ => hh (target i e)),
    Finset.mem_sdiff, and_assoc]

/-- Keeping all positive occurrences leaves a conservative row. -/
theorem conservative_of_positive_retained (target : (i : ι) → κ i → ι)
    (all retained : (i : ι) → Finset (κ i)) (h : ι → ℝ) (β : ℝ)
    (hh : ∀ j, 0 ≤ h j) (subset : ∀ i, retained i ⊆ all i)
    (complete : ∀ i, (∑ e ∈ all i, h (target i e)) = β * h i)
    (positive_retained : ∀ i e, e ∈ all i → 0 < h (target i e) → e ∈ retained i) :
    ∀ i, PhysicalMass.action (matrixCount target retained) h i = β * h i := by
  intro i
  apply le_antisymm (forward_budget target all retained h β hh subset complete i)
  apply le_of_not_gt
  intro strict
  obtain ⟨e, he, omitted, positive⟩ :=
    (strict_forward_loss_iff target all retained h β hh subset complete i).mp strict
  exact omitted (positive_retained i e he positive)

/-- Reuse the existing weighted transpose consumer after occurrence counting.
The supplied correspondence must bind the inverse matrix to these exact rows. -/
theorem weighted_deficit_eq_omitted (target : (i : ι) → κ i → ι)
    (all retained : (i : ι) → Finset (κ i)) (T : ι → ι → ℝ)
    (m h : ι → ℝ) (β : ℝ)
    (subset : ∀ i, retained i ⊆ all i)
    (complete : ∀ i, (∑ e ∈ all i, h (target i e)) = β * h i)
    (transport : ∀ i j, m i * T i j = m j * matrixCount target retained j i)
    (j : ι) :
    PhysicalMass.deficit T (fun i => m i * h i) β j =
      m j * omittedMass target all retained h j := by
  rw [PhysicalMass.weighted_deficit T (matrixCount target retained) m h β transport j,
    deficit_eq_omitted target all retained h β subset complete j]

end RowFamilies

section QuotientCounts

variable {Ω E ι : Type*} [Fintype Ω] [Fintype E]

/-- Actual size of a supplied quotient fiber, including singleton fibers. -/
noncomputable def fiberSize (q : Ω → ι) (i : ι) : ℕ :=
  rowCount q Finset.univ i

omit [Fintype E] in
/-- Positivity of the quotient weight requires an actual representative. -/
theorem fiberSize_pos_iff (q : Ω → ι) (i : ι) :
    0 < fiberSize q i ↔ ∃ x, q x = i := by
  classical
  simp [fiberSize, rowCount, Finset.card_pos, Finset.nonempty_def]

/-- Forward degree from one ordered state into one quotient label.
The separate edge type retains parallel occurrence identities. -/
noncomputable def forwardDegree (source target : E → Ω) (q : Ω → ι)
    (x : Ω) (j : ι) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e => source e = x ∧ q (target e) = j)).card

/-- Incoming degree at one ordered state, grouped by the source label.
This is the row-parent/column-child convention of the inverse matrix. -/
noncomputable def inverseDegree (source target : E → Ω) (q : Ω → ι)
    (x : Ω) (j : ι) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e => target e = x ∧ q (source e) = j)).card

omit [Fintype E] in
/-- Cardinality of an edge family partitioned into equally sized fibers.
No group action or freeness hypothesis is hidden in this counting step. -/
theorem card_eq_fiberSize_mul [DecidableEq Ω] (q : Ω → ι) (anchor : E → Ω)
    (edges : Finset E) (i : ι) (degree : ℕ)
    (maps : ∀ e ∈ edges, q (anchor e) = i)
    (uniform : ∀ x, q x = i →
      (edges.filter (fun e => anchor e = x)).card = degree) :
    edges.card = fiberSize q i * degree := by
  classical
  let fiber := Finset.univ.filter (fun x => q x = i)
  calc
    edges.card = ∑ x ∈ fiber, (edges.filter (fun e => anchor e = x)).card :=
      Finset.card_eq_sum_card_fiberwise (fun e he =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, maps e he⟩)
    _ = ∑ _ ∈ fiber, degree := by
      apply Finset.sum_congr rfl
      intro x hx
      exact uniform x (Finset.mem_filter.mp hx).2
    _ = fiberSize q i * degree := by simp [fiber, fiberSize, rowCount]

/-- Double count all literal edges in a quotient block.  Forward and
inverse counts are allowed to differ when their fiber sizes differ. -/
theorem weighted_count_transport (source target : E → Ω) (q : Ω → ι)
    (F T : ι → ι → ℕ)
    (forward_uniform : ∀ x j, forwardDegree source target q x j = F (q x) j)
    (inverse_uniform : ∀ x j, inverseDegree source target q x j = T (q x) j)
    (i j : ι) :
    fiberSize q i * T i j = fiberSize q j * F j i := by
  classical
  let edges := Finset.univ.filter (fun e => q (source e) = j ∧ q (target e) = i)
  have source_count : edges.card = fiberSize q j * F j i := by
    apply card_eq_fiberSize_mul q source edges j (F j i)
    · intro e he
      exact (Finset.mem_filter.mp he).2.1
    · intro x hx
      have fiber_eq : edges.filter (fun e => source e = x) =
          Finset.univ.filter (fun e => source e = x ∧ q (target e) = i) := by
        ext e
        simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨_, hi⟩, hsource⟩
          exact ⟨hsource, hi⟩
        · rintro ⟨hsource, hi⟩
          exact ⟨⟨by rw [hsource, hx], hi⟩, hsource⟩
      rw [fiber_eq]
      change forwardDegree source target q x i = F j i
      rw [forward_uniform, hx]
  have target_count : edges.card = fiberSize q i * T i j := by
    apply card_eq_fiberSize_mul q target edges i (T i j)
    · intro e he
      exact (Finset.mem_filter.mp he).2.2
    · intro x hx
      have fiber_eq : edges.filter (fun e => target e = x) =
          Finset.univ.filter (fun e => target e = x ∧ q (source e) = j) := by
        ext e
        simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨hj, _⟩, htarget⟩
          exact ⟨htarget, hj⟩
        · rintro ⟨htarget, hj⟩
          exact ⟨⟨hj, by rw [htarget, hx]⟩, htarget⟩
      rw [fiber_eq]
      change inverseDegree source target q x j = T i j
      rw [inverse_uniform, hx]
  exact target_count.symm.trans source_count

theorem weighted_count_transport_real (source target : E → Ω) (q : Ω → ι)
    (F T : ι → ι → ℕ)
    (forward_uniform : ∀ x j, forwardDegree source target q x j = F (q x) j)
    (inverse_uniform : ∀ x j, inverseDegree source target q x j = T (q x) j)
    (i j : ι) :
    (fiberSize q i : ℝ) * (T i j : ℝ) =
      (fiberSize q j : ℝ) * (F j i : ℝ) := by
  exact_mod_cast weighted_count_transport source target q F T
    forward_uniform inverse_uniform i j

/-- Literal edge counting supplies the weighted-deficit premise.  This
composition makes no assertion about a geometric overlap vector. -/
theorem quotient_deficit [Fintype ι] (source target : E → Ω) (q : Ω → ι)
    (F T : ι → ι → ℕ)
    (forward_uniform : ∀ x j, forwardDegree source target q x j = F (q x) j)
    (inverse_uniform : ∀ x j, inverseDegree source target q x j = T (q x) j)
    (h : ι → ℝ) (β : ℝ) (j : ι) :
    PhysicalMass.deficit (fun i j => (T i j : ℝ))
      (fun i => (fiberSize q i : ℝ) * h i) β j =
      (fiberSize q j : ℝ) *
        (β * h j - PhysicalMass.action (fun i j => (F i j : ℝ)) h j) :=
  PhysicalMass.weighted_deficit _ _ _ h β
    (weighted_count_transport_real source target q F T forward_uniform inverse_uniform) j

/-- Constant nonzero fibers justify cancelling their common weight.
A mixed fixed/free quotient does not meet this hypothesis. -/
theorem transpose_of_constant_fiber (source target : E → Ω) (q : Ω → ι)
    (F T : ι → ι → ℕ)
    (forward_uniform : ∀ x j, forwardDegree source target q x j = F (q x) j)
    (inverse_uniform : ∀ x j, inverseDegree source target q x j = T (q x) j)
    (c : ℕ) (hc : c ≠ 0) (constant : ∀ i, fiberSize q i = c) :
    ∀ i j, T i j = F j i := by
  intro i j
  have transport := weighted_count_transport source target q F T
    forward_uniform inverse_uniform i j
  rw [constant i, constant j] at transport
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc) transport

end QuotientCounts

end PscVerif.OccurrenceMassCounts
