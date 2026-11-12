import PscVerif.CompactNeighborhood
import PscVerif.NamedCutProximity

/-!
# Open neighborhoods capture the actual named balanced cuts

The original prefix tiles are compact in `Stable × H_M`. For any open
neighborhood of their distinct-letter intersections, every sufficiently
deep actual balanced cut lies in that neighborhood. The threshold is
uniform over all actual marks and a fixed finite source carrier. Strict
system membership supplies the distinct following letters; no strict
system is constructed here.

The final cover theorem selects a finite subcover before selecting the
generation threshold. Cut points are the original common Parikh vectors,
not the possibly repeated reference witness ordinals. No lattice count,
Haar normalization, positive measure or exact intersection membership is
asserted.

Pre-code gate: `docs/c4-compact-neighborhood-literature-2026-11-12.md`.
-/

namespace Psc.NamedCutNeighborhood

open Set Filter
open Psc.Binomial Psc.OccurrenceTransport Psc.OccurrenceFinite
open Psc.OccurrenceInverse Psc.OccurrenceResidue Psc.PrefixAddress
open Psc.PrefixClosure Psc.NamedStableChart Psc.NamedPrefixCompact
open Psc.NamedCutProximity Psc.CompactNeighborhood
open scoped Topology

/-- The union retains every ordered distinct-letter intersection in the
actual source's own original product carrier. -/
def overlapUnion (fixture : Fin 2) : Set (Ambient (substitution fixture) Stable) :=
  ⋃ a : Fin 3, ⋃ b : Fin 3, ⋃ (_ : a ≠ b), tiles fixture a ∩ tiles fixture b

theorem inter_subset_overlapUnion (fixture : Fin 2) (a b : Fin 3) (hab : a ≠ b) :
    tiles fixture a ∩ tiles fixture b ⊆ overlapUnion fixture := by
  intro x hx
  exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨hab, hx⟩⟩⟩

/-- A finite union of intersections of the already authenticated compact
tiles remains compact, including the possibility that it is empty. -/
theorem overlapUnion_compact (fixture : Fin 2) : IsCompact (overlapUnion fixture) := by
  apply isCompact_iUnion
  intro a
  apply isCompact_iUnion
  intro b
  apply isCompact_iUnion
  intro _
  exact (tiles_compact fixture a).inter (tiles_compact fixture b)

/-- Fixed-label version: the tolerance and residue depth are chosen from
the open neighborhood before the uniform generation threshold. -/
theorem eventually_fixed_labels_mem (fixture : Fin 2) (u v : Word) (a b : Fin 3)
    (U : Set (Ambient (substitution fixture) Stable)) (hU : IsOpen U)
    (covered : tiles fixture a ∩ tiles fixture b ⊆ U) :
    ∀ᶠ n : ℕ in atTop,
      ∀ top : Mark (subst (iterateImages (substitution fixture) (12 * n)) u),
      ∀ bottom : Mark (subst (iterateImages (substitution fixture) (12 * n)) v),
        parikhZ top.before = parikhZ bottom.before →
        top.letter = a → bottom.letter = b →
        ambientStar (substitution fixture) piZ (parikhZ top.before) ∈ U := by
  obtain ⟨ε, hε, q, transfer⟩ :=
    exists_close_inter_subset (incidenceLinear (substitution fixture))
      (tiles_compact fixture a) (tiles_compact fixture b) hU covered
  obtain ⟨Nu, hu⟩ := eventually_all_prefixes_close fixture u q ε hε
  obtain ⟨Nv, hv⟩ := eventually_all_prefixes_close fixture v q ε hε
  refine eventually_atTop.mpr ⟨max Nu Nv, ?_⟩
  intro n hn top bottom balanced ha hb
  obtain ⟨jt, _, hkt, hbt, hrt⟩ := hu n ((le_max_left Nu Nv).trans hn) top
  obtain ⟨jb, _, hkb, hbb, hrb⟩ := hv n ((le_max_right Nu Nv).trans hn) bottom
  apply transfer (ambientStar (substitution fixture) piZ (parikhZ top.before))
  · refine ⟨ambientStar (substitution fixture) piZ
      (parikhZ (wordPrefix (word fixture) jt)), ?_, ?_⟩
    · simpa only [ha] using hkt
    · exact ⟨hbt, hrt⟩
  · refine ⟨ambientStar (substitution fixture) piZ
      (parikhZ (wordPrefix (word fixture) jb)), ?_, ?_⟩
    · simpa only [hb] using hkb
    · constructor
      · change ‖piZ (parikhZ top.before) -
          piZ (parikhZ (wordPrefix (word fixture) jb))‖ < ε
        simpa only [balanced] using hbb
      · change MadicResidue.quotient (incidenceLinear (substitution fixture)) q
          (parikhZ top.before) =
          MadicResidue.quotient (incidenceLinear (substitution fixture)) q
            (parikhZ (wordPrefix (word fixture) jb))
        simpa only [balanced] using hrb

/-- Finite label uniformization covers every pair of actual marks at once.
The source words remain fixed while the generation tends to infinity. -/
theorem eventually_distinct_cuts_mem (fixture : Fin 2) (u v : Word)
    (U : Set (Ambient (substitution fixture) Stable)) (hU : IsOpen U)
    (covered : overlapUnion fixture ⊆ U) :
    ∀ᶠ n : ℕ in atTop,
      ∀ top : Mark (subst (iterateImages (substitution fixture) (12 * n)) u),
      ∀ bottom : Mark (subst (iterateImages (substitution fixture) (12 * n)) v),
        parikhZ top.before = parikhZ bottom.before → top.letter ≠ bottom.letter →
        ambientStar (substitution fixture) piZ (parikhZ top.before) ∈ U := by
  have pairs : ∀ a b : Fin 3, ∀ᶠ n : ℕ in atTop,
      a ≠ b →
      ∀ top : Mark (subst (iterateImages (substitution fixture) (12 * n)) u),
      ∀ bottom : Mark (subst (iterateImages (substitution fixture) (12 * n)) v),
        parikhZ top.before = parikhZ bottom.before →
        top.letter = a → bottom.letter = b →
        ambientStar (substitution fixture) piZ (parikhZ top.before) ∈ U := by
    intro a b
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall fun _ hne => (hne hab).elim
    · exact (eventually_fixed_labels_mem fixture u v a b U hU
        ((inter_subset_overlapUnion fixture a b hab).trans covered)).mono
        fun _ hn _ => hn
  have allPairs := Filter.eventually_all.mpr fun a => Filter.eventually_all.mpr (pairs a)
  filter_upwards [allPairs] with n hn
  intro top bottom balanced distinct
  exact hn top.letter bottom.letter distinct top bottom balanced rfl rfl

/-- Original common cut points with distinct following letters. Membership
retains actual complete marks; reference witness ordinals are not counted. -/
def cutPoints (fixture : Fin 2) (u v : Word) (n : ℕ) :
    Set (Ambient (substitution fixture) Stable) :=
  {x | ∃ top : Mark (subst (iterateImages (substitution fixture) (12 * n)) u),
    ∃ bottom : Mark (subst (iterateImages (substitution fixture) (12 * n)) v),
      parikhZ top.before = parikhZ bottom.before ∧ top.letter ≠ bottom.letter ∧
      x = ambientStar (substitution fixture) piZ (parikhZ top.before)}

theorem eventually_cutPoints_subset (fixture : Fin 2) (u v : Word)
    (U : Set (Ambient (substitution fixture) Stable)) (hU : IsOpen U)
    (covered : overlapUnion fixture ⊆ U) :
    ∀ᶠ n : ℕ in atTop, cutPoints fixture u v n ⊆ U := by
  filter_upwards [eventually_distinct_cuts_mem fixture u v U hU covered] with n hn
  rintro x ⟨top, bottom, balanced, distinct, rfl⟩
  exact hn top bottom balanced distinct

/-- One threshold for a fixed finite carrier, rather than separate
thresholds depending on the individual cut or the generation. -/
theorem eventually_finite_source_cuts_subset (fixture : Fin 2) (C : Finset WordPair)
    (U : Set (Ambient (substitution fixture) Stable)) (hU : IsOpen U)
    (covered : overlapUnion fixture ⊆ U) :
    ∀ᶠ n : ℕ in atTop, ∀ T ∈ C, cutPoints fixture T.1 T.2 n ⊆ U := by
  apply C.eventually_all.mpr
  intro T _
  exact eventually_cutPoints_subset fixture T.1 T.2 U hU covered

/-- The actual strict-system contract supplies label separation at every
proper balanced cut, including the cut at zero. The common threshold is
uniform over all members of the supplied finite carrier and all their marks. -/
theorem eventually_strict_carrier_cuts_mem (fixture : Fin 2) {C : Finset WordPair}
    (strict : Psc.StrictSystem.StrictSystem (substitution fixture) C)
    (U : Set (Ambient (substitution fixture) Stable)) (hU : IsOpen U)
    (covered : overlapUnion fixture ⊆ U) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ T ∈ C,
      ∀ top : Mark (subst (iterateImages (substitution fixture) (12 * n)) T.1),
      ∀ bottom : Mark (subst (iterateImages (substitution fixture) (12 * n)) T.2),
        parikhZ top.before = parikhZ bottom.before →
        ambientStar (substitution fixture) piZ (parikhZ top.before) ∈ U := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_finite_source_cuts_subset fixture C U hU covered)
  refine ⟨N, ?_⟩
  intro n hn T hT top bottom balanced
  apply hN n hn T hT
  exact ⟨top, bottom, balanced,
    (strict_cut_labels fixture strict T hT n top bottom balanced).2, rfl⟩

/-- A finite part of any open cover of the compact overlap union captures
all sufficiently deep actual strict cuts. The cover is selected before N. -/
theorem finite_open_cover_captures_strict_cuts (fixture : Fin 2)
    {C : Finset WordPair}
    (strict : Psc.StrictSystem.StrictSystem (substitution fixture) C)
    {ι : Type*} (U : ι → Set (Ambient (substitution fixture) Stable))
    (hU : ∀ i, IsOpen (U i)) (covered : overlapUnion fixture ⊆ ⋃ i, U i) :
    ∃ J : Finset ι, (overlapUnion fixture ⊆ ⋃ i ∈ J, U i) ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ T ∈ C,
        ∀ top : Mark (subst (iterateImages (substitution fixture) (12 * n)) T.1),
        ∀ bottom : Mark (subst (iterateImages (substitution fixture) (12 * n)) T.2),
          parikhZ top.before = parikhZ bottom.before →
          ∃ i ∈ J, ambientStar (substitution fixture) piZ (parikhZ top.before) ∈ U i := by
  obtain ⟨J, hJ⟩ := (overlapUnion_compact fixture).elim_finite_subcover U hU covered
  obtain ⟨N, hN⟩ := eventually_strict_carrier_cuts_mem fixture strict
    (⋃ i ∈ J, U i) (isOpen_biUnion fun i _ => hU i) hJ
  refine ⟨J, hJ, N, ?_⟩
  intro n hn T hT top bottom balanced
  simpa only [mem_iUnion, exists_prop] using hN n hn T hT top bottom balanced

/-- Empty overlap is allowed by the topology theorem. This conditional
absence statement does not infer that the actual overlap union is empty. -/
theorem eventually_no_distinct_cuts_of_empty_overlap (fixture : Fin 2) (u v : Word)
    (empty : overlapUnion fixture = ∅) :
    ∀ᶠ n : ℕ in atTop, cutPoints fixture u v n = ∅ := by
  have h := eventually_cutPoints_subset fixture u v ∅ isOpen_empty (by rw [empty])
  exact h.mono fun _ hn => Set.eq_empty_iff_forall_notMem.mpr fun _ hx => hn hx

/-- The smaller overlap union uses exactly the represented cut pairs of
the supplied carrier. Strictness later proves that these labels differ. -/
def carrierOverlap (fixture : Fin 2) (C : Finset WordPair) :
    Set (Ambient (substitution fixture) Stable) :=
  ⋃ a : Fin 3, ⋃ b : Fin 3, ⋃ (_ : Psc.StrictSystem.CutPair C a b),
    tiles fixture a ∩ tiles fixture b

theorem carrierOverlap_compact (fixture : Fin 2) (C : Finset WordPair) :
    IsCompact (carrierOverlap fixture C) := by
  apply isCompact_iUnion
  intro a
  apply isCompact_iUnion
  intro b
  apply isCompact_iUnion
  intro _
  exact (tiles_compact fixture a).inter (tiles_compact fixture b)

/-- Only the intersections represented by the actual carrier must be
covered. The supplied strict system authenticates the label of each cut;
unrepresented distinct-letter intersections need not lie in the target. -/
theorem eventually_carrierOverlap_strict_cuts_mem (fixture : Fin 2)
    {C : Finset WordPair}
    (strict : Psc.StrictSystem.StrictSystem (substitution fixture) C)
    (U : Set (Ambient (substitution fixture) Stable)) (hU : IsOpen U)
    (covered : carrierOverlap fixture C ⊆ U) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ T ∈ C,
      ∀ top : Mark (subst (iterateImages (substitution fixture) (12 * n)) T.1),
      ∀ bottom : Mark (subst (iterateImages (substitution fixture) (12 * n)) T.2),
        parikhZ top.before = parikhZ bottom.before →
        ambientStar (substitution fixture) piZ (parikhZ top.before) ∈ U := by
  classical
  have allSources : ∀ᶠ n : ℕ in atTop, ∀ T ∈ C,
      ∀ top : Mark (subst (iterateImages (substitution fixture) (12 * n)) T.1),
      ∀ bottom : Mark (subst (iterateImages (substitution fixture) (12 * n)) T.2),
        parikhZ top.before = parikhZ bottom.before →
        ambientStar (substitution fixture) piZ (parikhZ top.before) ∈ U := by
    apply C.eventually_all.mpr
    intro T hT
    have pairs : ∀ a b : Fin 3, ∀ᶠ n : ℕ in atTop,
        Psc.StrictSystem.CutPair C a b →
        ∀ top : Mark (subst (iterateImages (substitution fixture) (12 * n)) T.1),
        ∀ bottom : Mark (subst (iterateImages (substitution fixture) (12 * n)) T.2),
          parikhZ top.before = parikhZ bottom.before →
          top.letter = a → bottom.letter = b →
          ambientStar (substitution fixture) piZ (parikhZ top.before) ∈ U := by
      intro a b
      by_cases hp : Psc.StrictSystem.CutPair C a b
      · have hpair : tiles fixture a ∩ tiles fixture b ⊆ U := by
          intro x hx
          exact covered (mem_iUnion.mpr ⟨a, mem_iUnion.mpr
            ⟨b, mem_iUnion.mpr ⟨hp, hx⟩⟩⟩)
        exact (eventually_fixed_labels_mem fixture T.1 T.2 a b U hU hpair).mono
          fun _ hn _ => hn
      · exact Filter.Eventually.of_forall fun _ hp' => (hp hp').elim
    have allPairs := Filter.eventually_all.mpr fun a => Filter.eventually_all.mpr (pairs a)
    filter_upwards [allPairs] with n hn
    intro top bottom balanced
    exact hn top.letter bottom.letter
      (strict_cut_labels fixture strict T hT n top bottom balanced).1
      top bottom balanced rfl rfl
  exact eventually_atTop.mp allSources

/-- A finite open cover of only the represented cut-pair intersections
suffices for the original common cut points, with one threshold for C. -/
theorem finite_carrierOverlap_cover_captures_strict_cuts (fixture : Fin 2)
    {C : Finset WordPair}
    (strict : Psc.StrictSystem.StrictSystem (substitution fixture) C)
    {ι : Type*} (U : ι → Set (Ambient (substitution fixture) Stable))
    (hU : ∀ i, IsOpen (U i)) (covered : carrierOverlap fixture C ⊆ ⋃ i, U i) :
    ∃ J : Finset ι, (carrierOverlap fixture C ⊆ ⋃ i ∈ J, U i) ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ T ∈ C,
        ∀ top : Mark (subst (iterateImages (substitution fixture) (12 * n)) T.1),
        ∀ bottom : Mark (subst (iterateImages (substitution fixture) (12 * n)) T.2),
          parikhZ top.before = parikhZ bottom.before →
          ∃ i ∈ J, ambientStar (substitution fixture) piZ (parikhZ top.before) ∈ U i := by
  obtain ⟨J, hJ⟩ := (carrierOverlap_compact fixture C).elim_finite_subcover U hU covered
  obtain ⟨N, hN⟩ := eventually_carrierOverlap_strict_cuts_mem fixture strict
    (⋃ i ∈ J, U i) (isOpen_biUnion fun i _ => hU i) hJ
  refine ⟨J, hJ, N, ?_⟩
  intro n hn T hT top bottom balanced
  simpa only [mem_iUnion, exists_prop] using hN n hn T hT top bottom balanced

end Psc.NamedCutNeighborhood
