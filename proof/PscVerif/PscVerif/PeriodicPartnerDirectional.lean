/-
Singleton-fibre convergence, the finite endpoint and ray deductions. The topology
of the strict component is abstracted here as a compact space.
-/
import Mathlib.Algebra.Ring.Commute
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Separation.Hausdorff
import PscVerif.VertexAsymptoteRange
import PscVerif.PeriodicPartnerSeamCycles

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

/-- The normalized phase in the square-root eigenfunction argument is
constant on a preconnected parameter space. -/
theorem continuous_square_one_eq_one {T K : Type*} [TopologicalSpace T]
    [PreconnectedSpace T] [CommRing K] [IsDomain K] [TopologicalSpace K] [T2Space K]
    {f : T → K} (hf : Continuous f) (hsq : ∀ t, f t ^ 2 = 1)
    {t₀ : T} (hstart : f t₀ = 1) (t : T) : f t = 1 := by
  have hfinite : (range f).Finite := by
    refine ((finite_singleton (-1 : K)).insert 1).subset ?_
    rintro _ ⟨s, rfl⟩
    simpa only [mem_insert_iff, mem_singleton_iff] using sq_eq_one_iff.mp (hsq s)
  have hconstant := (isPreconnected_range hf).isDiscrete_iff_subsingleton.mp hfinite.isDiscrete
  exact (hconstant ⟨t, rfl⟩ ⟨t₀, rfl⟩).trans hstart

/-- The upper bound on stack cohomology and the lower bound on the cover's
base saturate the even part. The signed incidence identity then has no
nonzero modular roots in the original incidence factor. -/
theorem even_stack_residue_degrees {degree stack base r q d₂ : ℕ}
    (hupper : stack ≤ degree + 1) (hlower : degree + 1 ≤ base)
    (hfixed : base ≤ degree + r) (hdim : stack = degree + r + q)
    (hmod₂ : d₂ + r = 1 + q) :
    stack = degree + 1 ∧ base = degree + 1 ∧ r = 1 ∧ q = 0 ∧ d₂ = 0 := by
  omega

end Psc.PeriodicPartner
