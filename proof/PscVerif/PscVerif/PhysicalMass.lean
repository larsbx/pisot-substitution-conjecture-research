import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Relation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Physical mass loss on a finite directed graph

The convention throughout is that `T i j` is the weight of the edge from
row/parent `i` to column/child `j`. Thus the physical mass budget is the
**transpose** budget. All results are generic finite algebra: they neither
import a concrete graph certificate nor assert a geometric overlap cover.

The two inequalities force equality in the primal inequality and force the
product of each mass deficit with its overlap coordinate to be zero. A zero
coordinate propagates forward along a positive matrix entry. Finiteness then
turns one strict loss per source strongly connected component into zero at
every vertex. No sign assumption on the scalar `theta` is required.
-/

namespace PscVerif.PhysicalMass

open scoped BigOperators

section Algebra

variable {ι : Type*} [Fintype ι]

/-- Row action; repeated occurrences must be included in `T i j`. -/
def action (T : ι → ι → ℝ) (v : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, T i j * v j

/-- Transpose action, with the same row-parent/column-child orientation. -/
def transposeAction (T : ι → ι → ℝ) (h : ι → ℝ) (j : ι) : ℝ :=
  ∑ i, T i j * h i

def deficit (T : ι → ι → ℝ) (h : ι → ℝ) (theta : ℝ) (j : ι) : ℝ :=
  theta * h j - transposeAction T h j

def slack (T : ι → ι → ℝ) (v : ι → ℝ) (theta : ℝ) (i : ι) : ℝ :=
  action T v i - theta * v i

/-- The adjoint pairing fixes the transpose orientation explicitly. -/
theorem pairing (T : ι → ι → ℝ) (h v : ι → ℝ) :
    (∑ i, h i * action T v i) = ∑ j, transposeAction T h j * v j := by
  simp only [action, transposeAction, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact conservation, prior to any positivity assumptions. -/
theorem deficit_conservation (T : ι → ι → ℝ) (h v : ι → ℝ) (theta : ℝ) :
    (∑ i, h i * slack T v theta i) +
      (∑ j, deficit T h theta j * v j) = 0 := by
  simp only [slack, deficit, mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [pairing]
  have commute : (∑ i, h i * (theta * v i)) = ∑ i, theta * h i * v i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [commute]
  ring

theorem deficit_nonneg (T : ι → ι → ℝ) (h : ι → ℝ) (theta : ℝ)
    (budget : ∀ i, transposeAction T h i ≤ theta * h i) :
    ∀ i, 0 ≤ deficit T h theta i := by
  intro i
  exact sub_nonneg.mpr (budget i)

theorem slack_nonneg (T : ι → ι → ℝ) (v : ι → ℝ) (theta : ℝ)
    (supersolution : ∀ i, theta * v i ≤ action T v i) :
    ∀ i, 0 ≤ slack T v theta i := by
  intro i
  exact sub_nonneg.mpr (supersolution i)

/-- Nonnegative summands in the conservation identity vanish individually.
Nonnegative mass is enough here; strict positivity is used for saturation. -/
theorem products_zero (T : ι → ι → ℝ) (h v : ι → ℝ) (theta : ℝ)
    (hh : ∀ i, 0 ≤ h i) (hv : ∀ i, 0 ≤ v i)
    (supersolution : ∀ i, theta * v i ≤ action T v i)
    (budget : ∀ i, transposeAction T h i ≤ theta * h i) :
    (∀ i, h i * slack T v theta i = 0) ∧
      (∀ i, deficit T h theta i * v i = 0) := by
  have hs : ∀ i, 0 ≤ h i * slack T v theta i :=
    fun i => mul_nonneg (hh i) (slack_nonneg T v theta supersolution i)
  have hd : ∀ i, 0 ≤ deficit T h theta i * v i :=
    fun i => mul_nonneg (deficit_nonneg T h theta budget i) (hv i)
  have hs_sum : 0 ≤ ∑ i, h i * slack T v theta i :=
    Finset.sum_nonneg (fun i _ => hs i)
  have hd_sum : 0 ≤ ∑ i, deficit T h theta i * v i :=
    Finset.sum_nonneg (fun i _ => hd i)
  have conserved := deficit_conservation T h v theta
  have hs_zero : (∑ i, h i * slack T v theta i) = 0 := by linarith
  have hd_zero : (∑ i, deficit T h theta i * v i) = 0 := by linarith
  constructor
  · intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hs i)).mp hs_zero i
      (Finset.mem_univ i)
  · intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hd i)).mp hd_zero i
      (Finset.mem_univ i)

/-- Every primal inequality saturates. This uses strict mass positivity. -/
theorem saturation (T : ι → ι → ℝ) (h v : ι → ℝ) (theta : ℝ)
    (hh : ∀ i, 0 < h i) (hv : ∀ i, 0 ≤ v i)
    (supersolution : ∀ i, theta * v i ≤ action T v i)
    (budget : ∀ i, transposeAction T h i ≤ theta * h i) :
    ∀ i, action T v i = theta * v i := by
  have hz := (products_zero T h v theta (fun i => (hh i).le) hv
    supersolution budget).1
  intro i
  have hs : slack T v theta i = 0 :=
    (mul_eq_zero.mp (hz i)).resolve_left (ne_of_gt (hh i))
  exact sub_eq_zero.mp hs

/-- A strictly losing column has zero overlap coordinate. -/
theorem zero_at_loss (T : ι → ι → ℝ) (h v : ι → ℝ) (theta : ℝ)
    (hh : ∀ i, 0 ≤ h i) (hv : ∀ i, 0 ≤ v i)
    (supersolution : ∀ i, theta * v i ≤ action T v i)
    (budget : ∀ i, transposeAction T h i ≤ theta * h i)
    (j : ι) (loss : 0 < deficit T h theta j) : v j = 0 := by
  have hz := (products_zero T h v theta hh hv supersolution budget).2 j
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt loss)

end Algebra

section DirectedGraph

variable {ι : Type*}

/-- Directed reachability includes the path of length zero. -/
abbrev Reach (E : ι → ι → Prop) : ι → ι → Prop := Relation.ReflTransGen E

/-- Two representatives belong to the same strongly connected component. -/
def SameSCC (E : ι → ι → Prop) (i j : ι) : Prop := Reach E i j ∧ Reach E j i

/-- The SCC of `s` is a source: every predecessor can be reached back from `s`.
This definition is independent of the choice of SCC representative. -/
def IsSource (E : ι → ι → Prop) (s : ι) : Prop :=
  ∀ i, Reach E i s → Reach E s i

theorem isSource_of_sameSCC (E : ι → ι → Prop) {s t : ι}
    (source : IsSource E s) (same : SameSCC E s t) : IsSource E t := by
  intro i hit
  exact same.2.trans (source i (hit.trans same.2))

/-- The reachability definition is exactly the usual absence of incoming
edges from outside the SCC, not an absence of outgoing edges. -/
theorem isSource_iff_no_incoming (E : ι → ι → Prop) (s : ι) :
    IsSource E s ↔
      ∀ a b, SameSCC E s b → E a b → SameSCC E s a := by
  constructor
  · intro source a b same edge
    have has : Reach E a s := (Relation.ReflTransGen.single edge).trans same.2
    exact ⟨source a has, has⟩
  · intro closed a has
    induction has using Relation.ReflTransGen.head_induction_on with
    | refl => exact Relation.ReflTransGen.refl
    | @head a b edge path ih => exact (closed a b ⟨ih, path⟩ edge).1

/-- Every vertex of a finite directed graph has a source SCC ancestor.
The proof minimizes the cardinality of the predecessor set, so it does not
assume an SCC algorithm, an exported component list, or root completeness. -/
theorem exists_source_ancestor [Fintype ι] (E : ι → ι → Prop) (x : ι) :
    ∃ s, IsSource E s ∧ Reach E s x := by
  classical
  let pred : ι → Finset ι := fun i => Finset.univ.filter (fun j => Reach E j i)
  have mem_pred : ∀ i j, j ∈ pred i ↔ Reach E j i := by
    intro i j
    simp [pred]
  have self : ∀ i, i ∈ pred i := fun i => (mem_pred i i).mpr .refl
  obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image (pred x)
    (fun i => (pred i).card) ⟨x, self x⟩
  have hsx : Reach E s x := (mem_pred x s).mp hs
  refine ⟨s, ?_, hsx⟩
  intro y hys
  have hyx : Reach E y x := hys.trans hsx
  have subset : pred y ⊆ pred s := by
    intro z hz
    exact (mem_pred s z).mpr (((mem_pred y z).mp hz).trans hys)
  have equal : pred y = pred s := Finset.eq_of_subset_of_card_le subset
    (hmin y ((mem_pred x y).mpr hyx))
  apply (mem_pred y s).mp
  rw [equal]
  exact self s

/-- At least one losing vertex in every source SCC. -/
def SourceLoss (E : ι → ι → Prop) (losing : ι → Prop) : Prop :=
  ∀ s, IsSource E s → ∃ j, SameSCC E s j ∧ losing j

/-- On a finite graph, the source-SCC loss condition is equivalent to every
vertex being reachable from a losing vertex. This is a graph statement; it
does not say that source loss is necessary for every matrix obstruction. -/
theorem sourceLoss_iff_loss_reaches_all [Fintype ι]
    (E : ι → ι → Prop) (losing : ι → Prop) :
    SourceLoss E losing ↔ ∀ x, ∃ j, losing j ∧ Reach E j x := by
  constructor
  · intro loss x
    obtain ⟨s, source, path⟩ := exists_source_ancestor E x
    obtain ⟨j, same, hj⟩ := loss s source
    exact ⟨j, hj, same.2.trans path⟩
  · intro reaches s source
    obtain ⟨j, hj, path⟩ := reaches s
    exact ⟨j, ⟨source j path, path⟩, hj⟩

/-- Complete reachability from declared roots implies that each source SCC
contains a root. A packet's root list alone does not prove this premise. -/
theorem source_contains_root (E : ι → ι → Prop) (root : ι → Prop)
    (complete : ∀ x, ∃ r, root r ∧ Reach E r x) (s : ι)
    (source : IsSource E s) : ∃ r, root r ∧ SameSCC E s r := by
  obtain ⟨r, hr, path⟩ := complete s
  exact ⟨r, hr, source r path, path⟩

end DirectedGraph

section Obstruction

variable {ι : Type*} [Fintype ι]

/-- Positive support in the row-parent to column-child direction. -/
def support (T : ι → ι → ℝ) (i j : ι) : Prop := 0 < T i j

/-- Saturation and nonnegativity propagate zero forward along a positive edge. -/
theorem zero_of_positive_edge (T : ι → ι → ℝ) (v : ι → ℝ) (theta : ℝ)
    (hT : ∀ i j, 0 ≤ T i j) (hv : ∀ i, 0 ≤ v i)
    (saturated : ∀ i, action T v i = theta * v i)
    {i j : ι} (hi : v i = 0) (edge : support T i j) : v j = 0 := by
  classical
  have term_le : T i j * v j ≤ action T v i :=
    Finset.single_le_sum (fun k _ => mul_nonneg (hT i k) (hv k))
      (Finset.mem_univ j)
  have row_zero : action T v i = 0 := by rw [saturated i, hi, mul_zero]
  rw [row_zero] at term_le
  have product_zero : T i j * v j = 0 :=
    le_antisymm term_le (mul_nonneg (hT i j) (hv j))
  exact (mul_eq_zero.mp product_zero).resolve_left (ne_of_gt edge)

theorem zero_of_reachable (T : ι → ι → ℝ) (v : ι → ℝ) (theta : ℝ)
    (hT : ∀ i j, 0 ≤ T i j) (hv : ∀ i, 0 ≤ v i)
    (saturated : ∀ i, action T v i = theta * v i)
    {i j : ι} (hi : v i = 0) (path : Reach (support T) i j) : v j = 0 := by
  induction path with
  | refl => exact hi
  | tail _ edge ih => exact zero_of_positive_edge T v theta hT hv saturated ih edge

/-- The local form only needs a path from one losing vertex to the target. -/
theorem zero_of_loss_reaches (T : ι → ι → ℝ) (h v : ι → ℝ) (theta : ℝ)
    (hT : ∀ i j, 0 ≤ T i j) (hh : ∀ i, 0 < h i) (hv : ∀ i, 0 ≤ v i)
    (supersolution : ∀ i, theta * v i ≤ action T v i)
    (budget : ∀ i, transposeAction T h i ≤ theta * h i)
    {j x : ι} (loss : 0 < deficit T h theta j)
    (path : Reach (support T) j x) : v x = 0 := by
  exact zero_of_reachable T v theta hT hv
    (saturation T h v theta hh hv supersolution budget)
    (zero_at_loss T h v theta (fun i => (hh i).le) hv supersolution budget j loss)
    path

/-- Main finite-matrix obstruction. It requires no modular obstruction,
fitted positive weights, nonempty-index assumption, or sign assumption on theta. -/
theorem zero_of_source_loss (T : ι → ι → ℝ) (h v : ι → ℝ) (theta : ℝ)
    (hT : ∀ i j, 0 ≤ T i j) (hh : ∀ i, 0 < h i) (hv : ∀ i, 0 ≤ v i)
    (supersolution : ∀ i, theta * v i ≤ action T v i)
    (budget : ∀ i, transposeAction T h i ≤ theta * h i)
    (loss : SourceLoss (support T) (fun j => 0 < deficit T h theta j)) :
    ∀ x, v x = 0 := by
  intro x
  obtain ⟨j, hj, path⟩ :=
    (sourceLoss_iff_loss_reaches_all (support T) (fun j => 0 < deficit T h theta j)).mp
      loss x
  exact zero_of_loss_reaches T h v theta hT hh hv supersolution budget hj path

/-- If only selected overlap coordinates are targets, loss need only reach
those targets; unrelated source components need not be ruled out. -/
theorem zero_on_targets (T : ι → ι → ℝ) (h v : ι → ℝ) (theta : ℝ)
    (hT : ∀ i j, 0 ≤ T i j) (hh : ∀ i, 0 < h i) (hv : ∀ i, 0 ≤ v i)
    (supersolution : ∀ i, theta * v i ≤ action T v i)
    (budget : ∀ i, transposeAction T h i ≤ theta * h i)
    (target : ι → Prop)
    (reaches : ∀ x, target x →
      ∃ j, 0 < deficit T h theta j ∧ Reach (support T) j x) :
    ∀ x, target x → v x = 0 := by
  intro x hx
  obtain ⟨j, loss, path⟩ := reaches x hx
  exact zero_of_loss_reaches T h v theta hT hh hv supersolution budget loss path

/-- An alternative interface: losses reach each declared root, and the roots
reach the entire graph. Both reachability obligations are explicit. -/
theorem zero_of_root_cover (T : ι → ι → ℝ) (h v : ι → ℝ) (theta : ℝ)
    (hT : ∀ i j, 0 ≤ T i j) (hh : ∀ i, 0 < h i) (hv : ∀ i, 0 ≤ v i)
    (supersolution : ∀ i, theta * v i ≤ action T v i)
    (budget : ∀ i, transposeAction T h i ≤ theta * h i)
    (root : ι → Prop)
    (loss_to_root : ∀ r, root r →
      ∃ j, 0 < deficit T h theta j ∧ Reach (support T) j r)
    (root_cover : ∀ x, ∃ r, root r ∧ Reach (support T) r x) :
    ∀ x, v x = 0 := by
  intro x
  obtain ⟨r, hr, path⟩ := root_cover x
  obtain ⟨j, loss, to_root⟩ := loss_to_root r hr
  exact zero_of_loss_reaches T h v theta hT hh hv supersolution budget loss
    (to_root.trans path)

/-- Any surviving coordinate has an ancestor source SCC whose every deficit
is zero. This is a necessary obstruction to this loss argument, not a
Perron-Frobenius converse asserting that such an SCC produces a supersolution. -/
theorem conservative_source_ancestor_of_nonzero
    (T : ι → ι → ℝ) (h v : ι → ℝ) (theta : ℝ)
    (hT : ∀ i j, 0 ≤ T i j) (hh : ∀ i, 0 < h i) (hv : ∀ i, 0 ≤ v i)
    (supersolution : ∀ i, theta * v i ≤ action T v i)
    (budget : ∀ i, transposeAction T h i ≤ theta * h i)
    (x : ι) (nonzero : v x ≠ 0) :
    ∃ s, IsSource (support T) s ∧ Reach (support T) s x ∧
      ∀ j, SameSCC (support T) s j → deficit T h theta j = 0 := by
  obtain ⟨s, source, path⟩ := exists_source_ancestor (support T) x
  refine ⟨s, source, path, ?_⟩
  intro j same
  have not_positive : ¬ 0 < deficit T h theta j := by
    intro loss
    exact nonzero (zero_of_loss_reaches T h v theta hT hh hv supersolution budget
      loss (same.2.trans path))
  exact le_antisymm (le_of_not_gt not_positive) (deficit_nonneg T h theta budget j)

theorem conservative_source_of_nonzero
    (T : ι → ι → ℝ) (h v : ι → ℝ) (theta : ℝ)
    (hT : ∀ i j, 0 ≤ T i j) (hh : ∀ i, 0 < h i) (hv : ∀ i, 0 ≤ v i)
    (supersolution : ∀ i, theta * v i ≤ action T v i)
    (budget : ∀ i, transposeAction T h i ≤ theta * h i)
    (nonzero : ∃ x, v x ≠ 0) :
    ∃ s, IsSource (support T) s ∧
      ∀ j, SameSCC (support T) s j → deficit T h theta j = 0 := by
  obtain ⟨x, hx⟩ := nonzero
  obtain ⟨s, source, _, conservative⟩ :=
    conservative_source_ancestor_of_nonzero T h v theta hT hh hv
      supersolution budget x hx
  exact ⟨s, source, conservative⟩

end Obstruction

section MassTransport

variable {ι : Type*} [Fintype ι]

/-- Orbit multiplicities give a weighted transpose identity. `F` is the
forward incidence matrix; `T` retains the inverse row-parent convention.
This theorem also covers mixed orbit sizes, where `F = Tᵀ` need not hold. -/
theorem weighted_transpose (T F : ι → ι → ℝ) (m h : ι → ℝ)
    (transport : ∀ i j, m i * T i j = m j * F j i) (j : ι) :
    transposeAction T (fun i => m i * h i) j = m j * action F h j := by
  simp only [transposeAction, action, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    T i j * (m i * h i) = (m i * T i j) * h i := by ring
    _ = (m j * F j i) * h i := by rw [transport i j]
    _ = m j * (F j i * h i) := by ring

theorem weighted_deficit (T F : ι → ι → ℝ) (m h : ι → ℝ) (theta : ℝ)
    (transport : ∀ i j, m i * T i j = m j * F j i) (j : ι) :
    deficit T (fun i => m i * h i) theta j =
      m j * (theta * h j - action F h j) := by
  unfold deficit
  rw [weighted_transpose T F m h transport j]
  ring

theorem budget_of_weighted_transport
    (T F : ι → ι → ℝ) (m h : ι → ℝ) (theta : ℝ)
    (hm : ∀ i, 0 ≤ m i)
    (transport : ∀ i j, m i * T i j = m j * F j i)
    (forward_budget : ∀ j, action F h j ≤ theta * h j) :
    ∀ j, transposeAction T (fun i => m i * h i) j ≤ theta * (m j * h j) := by
  intro j
  rw [weighted_transpose T F m h transport j]
  calc
    m j * action F h j ≤ m j * (theta * h j) :=
      mul_le_mul_of_nonneg_left (forward_budget j) (hm j)
    _ = theta * (m j * h j) := by ring

theorem weighted_loss_iff (T F : ι → ι → ℝ) (m h : ι → ℝ) (theta : ℝ)
    (transport : ∀ i j, m i * T i j = m j * F j i)
    (j : ι) (hm : 0 < m j) :
    0 < deficit T (fun i => m i * h i) theta j ↔ action F h j < theta * h j := by
  rw [weighted_deficit T F m h theta transport j]
  constructor
  · intro positive
    nlinarith
  · intro strict
    exact mul_pos hm (sub_pos.mpr strict)

omit [Fintype ι] in
/-- Constant nonzero orbit size cancels, giving the ordinary transpose.
PR #515's constant size two is a special case of this algebraic implication. -/
theorem transpose_of_constant_orbit (T F : ι → ι → ℝ) (c : ℝ) (hc : c ≠ 0)
    (transport : ∀ i j, c * T i j = c * F j i) :
    ∀ i j, T i j = F j i := by
  intro i j
  exact mul_left_cancel₀ hc (transport i j)

end MassTransport

/-- Abstract refinement obligations for an imported physical-mass certificate.
The fields are proofs, not acceptance flags. In a concrete application the
caller must authenticate complete occurrence multiplicities and exact masses
before constructing these fields. This module supplies no such instance for
the exported PR #515 packet, and does not assume geometric realizability. -/
structure Refinement (ι : Type*) [Fintype ι] where
  matrix : ι → ι → ℝ
  mass : ι → ℝ
  theta : ℝ
  matrix_nonneg : ∀ i j, 0 ≤ matrix i j
  mass_pos : ∀ i, 0 < mass i
  transpose_budget : ∀ j, transposeAction matrix mass j ≤ theta * mass j
  source_loss : SourceLoss (support matrix) (fun j => 0 < deficit matrix mass theta j)

/-- A refinement certificate consumes an actual nonnegative overlap vector and
an actual supersolution proof; neither is manufactured from a checked file. -/
theorem Refinement.zero_of_supersolution {ι : Type*} [Fintype ι]
    (cert : Refinement ι) (v : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (supersolution : ∀ i, cert.theta * v i ≤ action cert.matrix v i) :
    ∀ i, v i = 0 :=
  zero_of_source_loss cert.matrix cert.mass v cert.theta cert.matrix_nonneg cert.mass_pos
    hv supersolution cert.transpose_budget cert.source_loss

/-- Build the transpose-budget refinement from exact forward mass transport.
Orbit sizes stay in the mass vector, so no constant-orbit assumption is hidden. -/
def Refinement.of_forward_mass {ι : Type*} [Fintype ι]
    (T F : ι → ι → ℝ) (m h : ι → ℝ) (theta : ℝ)
    (hT : ∀ i j, 0 ≤ T i j) (hm : ∀ i, 0 < m i) (hh : ∀ i, 0 < h i)
    (transport : ∀ i j, m i * T i j = m j * F j i)
    (forward_budget : ∀ j, action F h j ≤ theta * h j)
    (source_loss : SourceLoss (support T) (fun j => action F h j < theta * h j)) :
    Refinement ι where
  matrix := T
  mass := fun i => m i * h i
  theta := theta
  matrix_nonneg := hT
  mass_pos := fun i => mul_pos (hm i) (hh i)
  transpose_budget := budget_of_weighted_transport T F m h theta (fun i => (hm i).le)
    transport forward_budget
  source_loss := by
    intro s source
    obtain ⟨j, same, loss⟩ := source_loss s source
    exact ⟨j, same, (weighted_loss_iff T F m h theta transport j (hm j)).mpr loss⟩

end PscVerif.PhysicalMass
