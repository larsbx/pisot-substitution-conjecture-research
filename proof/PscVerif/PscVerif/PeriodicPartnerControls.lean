/-
# Finite controls for periodic-partner extraction

Exact word and integer-vector identities behind the `1/012/21` vertex-asymptote
counterexample, a nonzero periodic branch-locus numerator from Barge--Diamond--Swanson,
and two finite partner graphs.

The six-state graph is an **abstract finite control**, not a substitution tiling
space or a realization of (Z1)--(Z4).  It shows why a symmetric, everywhere-nonempty
partner relation, coordinate-disjoint partners, and a stack-equivalence constraint
on co-partners do not force a triangle or regular letter degrees.  The geometric
interpretation of the word identities, including the legal infinite tilings and
their asymptotic tails, is a written proof in the accompanying research note.

No tiling-space theorem, coincidence-rank computation, or universal (NM_V) assertion
is encoded in this file.  All finite decisions use Lean kernel reduction.
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.Infix
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FinCases

namespace Psc.PeriodicPartnerControls

abbrev Letter := Fin 3
abbrev Word := List Letter

/-! ## The `1/012/21` non-origin merge -/

def mergeSubst : Letter → Word := ![[1], [0, 1, 2], [2, 1]]

def mergeImage (w : Word) : Word := w.flatMap mergeSubst

def mergeLeft : Letter → Letter := ![1, 0, 2]

def mergeRight : Letter → Letter := ![1, 2, 1]

def mergeMatrix : Matrix Letter Letter ℤ := ![![0, 1, 0], ![1, 1, 1], ![0, 1, 1]]

def mergeStart : Letter → ℤ := ![1, 0, -1]

def mergeEnd : Letter → ℤ := ![1, 1, 1]

/-- The displayed matrix really counts the images, by columns. -/
theorem mergeMatrix_counts :
    ∀ i a : Letter, mergeMatrix i a = ((mergeSubst a).count i : ℤ) := by
  intro i a
  fin_cases i <;> fin_cases a <;> decide

theorem merge_left_endpoints :
    ∀ a : Letter, (mergeSubst a).head? = some (mergeLeft a) := by
  decide

theorem merge_right_endpoints :
    ∀ a : Letter, (mergeSubst a).getLast? = some (mergeRight a) := by
  decide

theorem merge_left_injective : Function.Injective mergeLeft := by
  decide

/-- The two different letters just before the eventual common ray merge. -/
theorem merge_right_collision :
    (0 : Letter) ≠ 2 ∧ mergeRight 0 = mergeRight 2 := by
  decide

/-- The interior patch is preserved with the common tail word `121` appended. -/
theorem merge_patch_identity :
    mergeImage [1, 2, 2] = [0] ++ [1, 2, 2] ++ [1, 2, 1] := by
  decide

/-- The vertex-ray patch appends exactly the same tail word. -/
theorem merge_ray_identity :
    mergeImage [2, 1, 0] = [2, 1, 0] ++ [1, 2, 1] := by
  decide

/-- Both patches have literal legal occurrences, without a numerical search. -/
theorem merge_legal_patch_occurrences :
    mergeImage (mergeSubst 1) = [1, 0] ++ [1, 2, 2] ++ [1] ∧
    mergeImage (mergeSubst 2) = [2, 1, 0] ++ [1, 2] := by
  decide

/-- The legal seam `1.2` has both germs fixed by the second substitution power. -/
theorem merge_vertex_seam :
    [1, 2].IsInfix (mergeSubst 1) ∧ mergeRight (mergeRight 1) = 1 ∧ mergeLeft 2 = 2 := by
  decide

/-- Placing the patch `122` at `x` makes its retained copy start at `x` again. -/
theorem merge_start_equation :
    mergeMatrix.mulVec mergeStart + ![1, 0, 0] = mergeStart := by
  decide

/-- Bind the displayed integer columns to counts of the actual three words. -/
theorem merge_word_count_vectors :
    (∀ a : Letter, (([1, 2, 2] : Word).count a : ℤ) = (![0, 1, 2] : Letter → ℤ) a) ∧
    (∀ a : Letter, (([2, 1, 0] : Word).count a : ℤ) = (![1, 1, 1] : Letter → ℤ) a) ∧
    (∀ a : Letter, (([1, 2, 1] : Word).count a : ℤ) = (![0, 2, 1] : Letter → ℤ) a) := by
  constructor
  · intro a; fin_cases a <;> decide
  constructor <;> intro a <;> fin_cases a <;> decide

/-- The same certificate in the existing interior-address convention `v = -x`:
`σ(1) = P 1 Q`, with nonempty `P,Q`, and `(M-I)v = p(P)`. -/
theorem merge_interior_address_equations :
    mergeSubst 1 = [0] ++ [1] ++ [2] ∧
    mergeMatrix.mulVec ![-1, 0, 1] - (![-1, 0, 1] : Letter → ℤ) = ![1, 0, 0] := by
  decide

/-- The two finite patches end at the same integral vertex `z = (1,1,1)`. -/
theorem merge_same_endpoint :
    mergeStart + ![0, 1, 2] = mergeEnd ∧ (![1, 1, 1] : Letter → ℤ) = mergeEnd := by
  decide

/-- Their last letters differ, so the common-tail boundary is a genuine branch. -/
theorem merge_distinct_branch_letters :
    ([1, 2, 2] : Word).getLast? = some 2 ∧
    ([2, 1, 0] : Word).getLast? = some 0 ∧ (2 : Letter) ≠ 0 := by
  decide

/-- The appended tail has exactly the displacement from `z` to `M z`. -/
theorem merge_tail_displacement :
    mergeEnd + ![0, 2, 1] = mergeMatrix.mulVec mergeEnd := by
  decide

/-! ## A periodic base point need not be zero

Barge--Diamond--Swanson, arXiv:0804.0930, Example 3, uses the irreducible
two-letter Pisot matrix `A = [[5,7],[2,3]]`.  The numerator `(1,-1)` gives
the nonzero fixed torus point `(1/3,-1/3)`.  These are just the exact
arithmetic identities; the paper supplies the branch-locus realization.
-/

def branchMatrix : Matrix (Fin 2) (Fin 2) ℤ := ![![5, 7], ![2, 3]]

def branchNumerator : Fin 2 → ℤ := ![1, -1]

theorem branch_numerator_fixed_mod_three :
    branchMatrix.mulVec branchNumerator = branchNumerator + ![-3, 0] := by
  decide

theorem branch_numerator_nonzero_mod_three :
    ¬ (∀ i : Fin 2, branchNumerator i % 3 = 0) := by
  decide

/-! ## Connected seam graph with nonregular, triangle-free partner data -/

/-- All six edges of the connected bipartite seam graph `K_(3,2)`. -/
abbrev Seam := Fin 3 × Fin 2

/-- Exactly one left letter is zero, and the right letters differ. -/
def modelPartner (e f : Seam) : Prop :=
  e.2 ≠ f.2 ∧ ((e.1 = 0 ∧ f.1 ≠ 0) ∨ (f.1 = 0 ∧ e.1 ≠ 0))

instance (e f : Seam) : Decidable (modelPartner e f) := by
  unfold modelPartner
  infer_instance

/-- The finite shadow of right/left asymptotic classes is equality of a side label. -/
def modelSameSide (e f : Seam) : Prop := e.1 = f.1 ∨ e.2 = f.2

/-- Abstract equivalence allowed by the co-partner conclusion of (W4).
This does not define actual stable coincidence of tilings. -/
def modelStack (e f : Seam) : Prop :=
  e.2 = f.2 ∧ (e.1 = 0 ↔ f.1 = 0)

instance (e f : Seam) : Decidable (modelStack e f) := by
  unfold modelStack
  infer_instance

def modelPartners (e : Seam) : Finset Seam := Finset.univ.filter (modelPartner e)

theorem model_seam_count : Fintype.card Seam = 6 := by
  decide

/-- Any two seam edges are joined through a third sharing their respective side labels. -/
theorem model_seam_connected (e f : Seam) :
    ∃ m : Seam, modelSameSide e m ∧ modelSameSide m f := by
  exact ⟨(e.1, f.2), Or.inl rfl, Or.inr rfl⟩

theorem model_partner_symmetric :
    ∀ e f : Seam, modelPartner e f → modelPartner f e := by
  decide

theorem model_partner_disjoint_labels :
    ∀ e f : Seam, modelPartner e f → e.1 ≠ f.1 ∧ e.2 ≠ f.2 := by
  decide

theorem model_partner_nonempty :
    ∀ e : Seam, ∃ f : Seam, modelPartner e f := by
  decide

theorem model_partner_triangle_free :
    ∀ e f g : Seam, modelPartner e f → modelPartner e g → ¬ modelPartner f g := by
  decide

theorem model_stack_equivalence : Equivalence modelStack := by
  constructor <;> decide

theorem model_copartners_stack_equivalent :
    ∀ e f g : Seam, modelPartner e f → modelPartner e g → modelStack f g := by
  decide

theorem model_partners_not_stack_equivalent :
    ∀ e f : Seam, modelPartner e f → ¬ modelStack e f := by
  decide

/-- A common partner can have two different partners with the same right label. -/
theorem model_asymptotic_copartners :
    modelPartner (0, 0) (1, 1) ∧ modelPartner (0, 0) (2, 1) ∧
    ((1, 1) : Seam) ≠ (2, 1) ∧ (((1, 1) : Seam).2 = ((2, 1) : Seam).2) ∧
    ¬ modelPartner (1, 1) (2, 1) := by
  decide

/-- The missing covering hypothesis cannot be replaced by symmetry and nonempty fibres. -/
theorem model_nonconstant_degree :
    (modelPartners (0, 0)).card = 2 ∧ (modelPartners (1, 1)).card = 1 := by
  decide

/-- All six degrees are determined, including both values of the right letter. -/
theorem model_degree_formula :
    ∀ e : Seam, (modelPartners e).card = if e.1 = 0 then 2 else 1 := by
  decide

theorem model_betti_count : (6 : ℤ) - 3 - 2 + 1 = 2 := by
  decide

/-! ## The cyclic `012/120/201` triangle control -/

def triangleSubst : Letter → Word := ![[0, 1, 2], [1, 2, 0], [2, 0, 1]]

def rho : Letter → Letter := ![1, 2, 0]

def triangleImage (w : Word) : Word := w.flatMap triangleSubst

def rotateSeam (e : Letter × Letter) : Letter × Letter := (rho e.1, rho e.2)

def trianglePartner (e f : Letter × Letter) : Prop :=
  f = rotateSeam e ∨ e = rotateSeam f

instance (e f : Letter × Letter) : Decidable (trianglePartner e f) := by
  unfold trianglePartner
  infer_instance

theorem triangle_relabelling_commutes :
    ∀ a : Letter, (triangleSubst a).map rho = triangleSubst (rho a) := by
  decide

theorem triangle_rho_order_three :
    ∀ a : Letter, rho (rho (rho a)) = a ∧ rho a ≠ a := by
  decide

/-- Every seam is literally present in the fourth image of `0`. -/
theorem triangle_all_bigrams_legal :
    ∀ a b : Letter,
      [a, b].IsInfix (triangleImage (triangleImage (triangleImage (triangleSubst 0)))) := by
  decide

/-- The two cyclic relabellings really do close a third partner edge. -/
theorem triangle_closes : ∀ e : Letter × Letter,
    trianglePartner e (rotateSeam e) ∧
    trianglePartner e (rotateSeam (rotateSeam e)) ∧
    trianglePartner (rotateSeam e) (rotateSeam (rotateSeam e)) ∧
    e ≠ rotateSeam e ∧ e ≠ rotateSeam (rotateSeam e) ∧
    rotateSeam e ≠ rotateSeam (rotateSeam e) := by
  decide

theorem triangle_partner_disjoint_labels :
    ∀ e f : Letter × Letter, trianglePartner e f → e.1 ≠ f.1 ∧ e.2 ≠ f.2 := by
  decide

end Psc.PeriodicPartnerControls
