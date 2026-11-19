/-
Singleton-fibre convergence, the finite endpoint and ray deductions, and
the grouped cycle calculation for the stack quotient argument. The topology
of the strict component is abstracted here as a compact space.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Separation.Hausdorff
import PscVerif.VertexAsymptoteRange

namespace Psc.PeriodicPartner

open Filter Function Set
open scoped BigOperators Topology

/-- Every lift of a net converging to a point with a singleton fibre converges
to the sole member of that fibre. -/
theorem tendsto_of_singleton_fibre {X Y I : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] {p : X → Y} (hp : Continuous p) {x : X}
    (hsingle : ∀ z, p z = p x → z = x) {l : Filter I} {u : I → X}
    (h : Tendsto (p ∘ u) l (𝓝 (p x))) : Tendsto u l (𝓝 x) := by
  rw [tendsto_iff_forall_eventually_mem] at h ⊢
  intro V hV
  obtain ⟨O, hOV, hO, hx⟩ := mem_nhds_iff.mp hV
  have hclosed : IsClosed (p '' Oᶜ) := (hO.isClosed_compl.isCompact.image hp).isClosed
  have hx' : p x ∈ (p '' Oᶜ)ᶜ := by
    rintro ⟨z, hz, hpz⟩
    exact hz (hsingle z hpz ▸ hx)
  filter_upwards [h _ (hclosed.isOpen_compl.mem_nhds hx')] with i hi
  exact hOV (by
    by_contra hnot
    exact hi ⟨u i, hnot, rfl⟩)

open Psc.VertexAsymptoteRange in
/-- For a connected ternary eventual range, cycle rank at least two gives an
injective endpoint direction. The vertex bounds are expressed using the
sixth-iterate test for periodic letters. -/
theorem injective_endpoint_of_large_cycle_rank (gR gL : Letter → Letter)
    (L R : Finset Letter) (E : Finset Seam)
    (hL : L ⊆ Finset.univ.filter (fun a => gR^[6] a = a))
    (hR : R ⊆ Finset.univ.filter (fun a => gL^[6] a = a)) (hE : E ⊆ L ×ˢ R)
    (hRank : 2 ≤ (E.card : ℤ) - L.card - R.card + 1) : Injective gR ∨ Injective gL := by
  by_contra! h
  have hl : L.card ≤ 2 :=
    (Finset.card_le_card hL).trans (periodic_letters_card_le_two gR h.1)
  have hr : R.card ≤ 2 :=
    (Finset.card_le_card hR).trans (periodic_letters_card_le_two gL h.2)
  obtain ⟨hsize, _⟩ := (cycle_rank_bound L R E hE (Or.inl hl)).2 hRank
  rcases hsize with ⟨_, hthree⟩ | ⟨hthree, _⟩ <;> omega

/-- If eventual coincidence transports ray disjointness between `a` and `b`,
then any nonempty disjointness relation splits `{a,b}` from its third letter. -/
theorem three_letter_germ_disjointness (N : Fin 3 → Fin 3 → Prop)
    (hsymm : ∀ ⦃i j⦄, N i j → N j i) (hirrefl : ∀ i, ¬ N i i)
    {a b : Fin 3} (hab : a ≠ b)
    (htransport : ∀ i, N a i ↔ N b i) (hnonempty : ∃ i j, N i j) :
    ∃ c, c ≠ a ∧ c ≠ b ∧
      ∀ i j, N i j ↔ (i = c ∧ j ≠ c) ∨ (j = c ∧ i ≠ c) := by
  classical
  have third : ∀ a b : Fin 3, a ≠ b →
      ∃ c, c ≠ a ∧ c ≠ b ∧ ∀ i : Fin 3, i = a ∨ i = b ∨ i = c := by decide
  obtain ⟨c, hca, hcb, hexhaust⟩ := third a b hab
  have htwo {i} (hi : i ≠ c) : i = a ∨ i = b := by
    rcases hexhaust i with ha | hb | hc
    · exact Or.inl ha
    · exact Or.inr hb
    · exact False.elim (hi hc)
  have hnab : ¬ N a b := fun h => hirrefl b ((htransport b).mp h)
  have hinside {i j} (hi : i ≠ c) (hj : j ≠ c) : ¬ N i j := by
    rcases htwo hi with ha | hb <;> rcases htwo hj with hja | hjb
    · simpa only [ha, hja] using hirrefl a
    · simpa only [ha, hjb] using hnab
    · rw [hb, hja]
      exact fun h => hnab (hsymm h)
    · simpa only [hb, hjb] using hirrefl b
  have hcross {i} (hi : i ≠ c) : N i c ↔ N a c := by
    rcases htwo hi with rfl | rfl
    · rfl
    · exact (htransport c).symm
  have hac : N a c := by
    obtain ⟨i, j, hij⟩ := hnonempty
    by_cases hi : i = c
    · subst i
      have hj : j ≠ c := fun hj => hirrefl c (hj ▸ hij)
      exact (hcross hj).mp (hsymm hij)
    · have hj : j = c := by
        by_contra hne
        exact hinside hi hne hij
      exact (hcross hi).mp (hj ▸ hij)
  refine ⟨c, hca, hcb, fun i j => ⟨?_, ?_⟩⟩
  · intro hij
    by_cases hi : i = c
    · subst i
      exact Or.inl ⟨rfl, fun hj => hirrefl c (hj ▸ hij)⟩
    · exact Or.inr ⟨by_contra (fun hj => hinside hi hj hij), hi⟩
  · rintro (⟨rfl, hj⟩ | ⟨rfl, hi⟩)
    · exact hsymm ((hcross hj).mpr hac)
    · exact (hcross hi).mpr hac

private def groupCycle {I J A : Type*} [Fintype I] [Fintype J] [AddCommGroup A]
    (p : I → Bool) (q : J → Bool) (w : I → J → A) (u v : Bool) : A :=
  ∑ i, ∑ j, if p i = u ∧ q j = v then w i j else 0

private theorem groupCycle_row {I J A : Type*} [Fintype I] [Fintype J] [AddCommGroup A]
    (p : I → Bool) (q : J → Bool) (w : I → J → A) (h : ∀ i, ∑ j, w i j = 0)
    (u : Bool) : groupCycle p q w u false + groupCycle p q w u true = 0 := by
  unfold groupCycle
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hp : p i = u
  · rw [← Finset.sum_add_distrib]
    refine Eq.trans ?_ (h i)
    apply Finset.sum_congr rfl
    intro j _
    cases q j <;> simp [hp]
  · simp [hp]

private theorem groupCycle_swap {I J A : Type*} [Fintype I] [Fintype J] [AddCommGroup A]
    (p : I → Bool) (q : J → Bool) (w : I → J → A) (u v : Bool) :
    groupCycle p q w u v = groupCycle q p (fun j i => w i j) v u := by
  unfold groupCycle
  rw [Finset.sum_comm]
  simp only [and_comm]

/-- Push a cycle by summing edge coefficients on its grouped endpoints.
Each side has at most two groups, encoded by `Bool`. Zero edge weights
cover missing seams. The grouped cycle has one free entry. -/
theorem grouped_cycle_entries {I J A : Type*} [Fintype I] [Fintype J] [AddCommGroup A]
    (p : I → Bool) (q : J → Bool) (w : I → J → A)
    (hrow : ∀ i, ∑ j, w i j = 0) (hcol : ∀ j, ∑ i, w i j = 0) :
    let x (u v : Bool) := ∑ i, ∑ j, if p i = u ∧ q j = v then w i j else 0
    ∀ u v, x u v = if u = v then x false false else -x false false := by
  change ∀ u v, groupCycle p q w u v =
    if u = v then groupCycle p q w false false else -groupCycle p q w false false
  let x := groupCycle p q w
  change ∀ u v, x u v = if u = v then x false false else -x false false
  have hLeft (u : Bool) := groupCycle_row p q w hrow u
  have hRight (v : Bool) : x false v + x true v = 0 := by
    change groupCycle p q w false v + groupCycle p q w true v = 0
    rw [groupCycle_swap p q w false v, groupCycle_swap p q w true v]
    exact groupCycle_row q p (fun j i => w i j) hcol v
  have hft : x false true = -x false false := eq_neg_of_add_eq_zero_right (hLeft false)
  have htf : x true false = -x false false := eq_neg_of_add_eq_zero_right (hRight false)
  have htt : x true true = x false false := by
    have h : x true false + x true true = 0 := hLeft true
    rw [htf] at h
    simpa only [neg_neg] using eq_neg_of_add_eq_zero_right h
  intro u v
  cases u <;> cases v <;> simp [hft, htf, htt]

end Psc.PeriodicPartner
