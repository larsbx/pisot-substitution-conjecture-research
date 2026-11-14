import PscVerif.OccurrenceSuccessor
import PscVerif.TerminationFactors

/-!
# Literal half-coincidence hits give finite balanced-pair reachability

A finite packet set covers the actual interior overlaps in every substituted
seed word. Each covered packet has a composable literal `InteriorStep` path
to zero integral prefix difference. These premises imply a uniform bound on
the lengths of late-generation irreducible balanced factors, and hence finite
actual `ChildNC` reachability. No balanced-word carrier or factor bound is an
input. The finite overlap coverage and zero-hit premises remain explicit.

The bounded-gap argument follows Sirvent--Solomyak, Theorem 5.6. Here literal
zero integral difference supplies a balanced cut directly, without a rational
independence assumption. Only positive exact length scaling is used; the
separate Pisot construction and universal hitting problem are not proved.

Pre-code decision: `docs/bh-finite-reachability-stop-go-2026-11-14.md`.
-/

namespace Psc.BHFiniteReachability

open Psc.Binomial Psc.Incidence Psc.Reduction Psc.Descendants
open Psc.OccurrenceNewborn Psc.OccurrenceTransport Psc.OccurrenceSuccessor

/-- Coverage refers to literal marks in the two whole substituted seed words,
including generation zero. Equal word labels do not identify occurrences. -/
def CoversSeedIterates (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (T : WordPair) (C : Set Packet) : Prop :=
  ∀ n (top : Mark ((subst s)^[n] T.1)) (bottom : Mark ((subst s)^[n] T.2)),
    (MarkedPair.mk (((subst s)^[n] T.1), ((subst s)^[n] T.2)) top bottom).Overlaps ℓ →
    (MarkedPair.mk (((subst s)^[n] T.1), ((subst s)^[n] T.2)) top bottom).packet ∈ C

/-- A balanced prefix cut in the full inflated words, bounded by the inflated
endpoints of the original selected top tile. The suffixes retain the literal
prefix realization, even after an earlier zero hit has been padded. -/
def TileCut (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (m : MarkedPair) (n : ℕ) : Prop :=
  ∃ u v ru rv : Word,
    (subst s)^[n] m.words.1 = u ++ ru ∧
    (subst s)^[n] m.words.2 = v ++ rv ∧ Equiv1 u v ∧
    β ^ n * physicalLength ℓ m.top.before ≤ physicalLength ℓ u ∧
    physicalLength ℓ u ≤ β ^ n * (physicalLength ℓ m.top.before + ℓ m.top.letter)

theorem physicalLength_subst (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a) (w : Word) :
    physicalLength ℓ (subst s w) = β * physicalLength ℓ w := by
  induction w with
  | nil => simp [subst]
  | cons a w ih => rw [subst_cons, physicalLength_append, hscale, ih,
      physicalLength_cons, mul_add]

theorem physicalLength_iterate (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a) (n : ℕ) (w : Word) :
    physicalLength ℓ ((subst s)^[n] w) = β ^ n * physicalLength ℓ w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', physicalLength_subst s ℓ β hscale, ih,
      pow_succ]
    ring

private theorem mark_bounds (ℓ : Fin 3 → ℝ) (hℓ : ∀ a, 0 ≤ ℓ a)
    {w : Word} (m : Mark w) :
    0 ≤ physicalLength ℓ m.before ∧
      physicalLength ℓ m.before + ℓ m.letter ≤ physicalLength ℓ w := by
  refine ⟨physicalLength_nonneg ℓ hℓ _, ?_⟩
  have h := congrArg (physicalLength ℓ) m.split
  rw [physicalLength_append, physicalLength_cons] at h
  linarith [physicalLength_nonneg ℓ hℓ m.after]

/-- A chosen literal packet path gives a depth independent of its occurrence
realization. The full prefixes are retained throughout, without localization
to intermediate balanced factors. -/
theorem packet_path_tileCut (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    {p q : Packet} (hpath : Relation.ReflTransGen (InteriorStep s ℓ) p q)
    (hq : q.delta = 0) :
    ∃ n, ∀ m : MarkedPair, m.packet = p → TileCut s ℓ β m n := by
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨0, ?_⟩
    intro m hm
    have hzero : residual m.top.before m.bottom.before = 0 := by
      exact (congrArg Packet.delta hm).trans hq
    have hbal := equiv1_of_parikhZ_eq (sub_eq_zero.mp hzero)
    refine ⟨m.top.before, m.bottom.before, m.top.letter :: m.top.after,
      m.bottom.letter :: m.bottom.after, m.top.split, m.bottom.split, hbal, ?_, ?_⟩
    · simp
    · simpa using le_add_of_nonneg_right (a := physicalLength ℓ m.top.before)
        (le_of_lt (hpos m.top.letter))
  | @head p r hpr _ ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    intro m hm
    have hedge : DigitStep s m.packet r := by simpa only [hm] using hpr.1
    obtain ⟨dt, db, hr⟩ := hedge
    have hnext : (m.inflate s dt db).packet = r := by
      exact (m.inflate_packet s dt db).trans hr.symm
    obtain ⟨u, v, ru, rv, hu, hv, hbal, hlo, hhi⟩ := hn (m.inflate s dt db) hnext
    refine ⟨u, v, ru, rv, ?_, ?_, hbal, ?_, ?_⟩
    · simpa only [Function.iterate_succ_apply, MarkedPair.inflate] using hu
    · simpa only [Function.iterate_succ_apply, MarkedPair.inflate] using hv
    · have hd := (mark_bounds ℓ (fun a => le_of_lt (hpos a)) dt).1
      change β ^ n * physicalLength ℓ (subst s m.top.before ++ dt.before) ≤ _ at hlo
      rw [physicalLength_append, physicalLength_subst s ℓ β hscale] at hlo
      have hmul := mul_nonneg (le_of_lt (pow_pos hβ n)) hd
      rw [pow_succ]
      nlinarith
    · have hd := (mark_bounds ℓ (fun a => le_of_lt (hpos a)) dt).2
      rw [hscale] at hd
      change physicalLength ℓ dt.before + ℓ dt.letter ≤ β * ℓ m.top.letter at hd
      change _ ≤ β ^ n *
        (physicalLength ℓ (subst s m.top.before ++ dt.before) + ℓ dt.letter) at hhi
      rw [physicalLength_append, physicalLength_subst s ℓ β hscale] at hhi
      have hmul := mul_le_mul_of_nonneg_left hd (le_of_lt (pow_pos hβ n))
      rw [pow_succ]
      nlinarith

/-- A balanced cut survives further substitution. Padding does not ask for
an additional hitting path after zero, or for equality of endpoint letters. -/
theorem TileCut.pad (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hβ : 0 < β) (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    {m : MarkedPair} {n D : ℕ} (h : TileCut s ℓ β m n) (hnD : n ≤ D) :
    TileCut s ℓ β m D := by
  obtain ⟨u, v, ru, rv, hu, hv, hbal, hlo, hhi⟩ := h
  let k := D - n
  have hkn : k + n = D := Nat.sub_add_cancel hnD
  refine ⟨(subst s)^[k] u, (subst s)^[k] v,
    (subst s)^[k] ru, (subst s)^[k] rv, ?_, ?_,
    equiv1_iterate_subst s k hbal, ?_, ?_⟩
  · rw [← hkn, Function.iterate_add_apply, hu, iterate_subst_append]
  · rw [← hkn, Function.iterate_add_apply, hv, iterate_subst_append]
  · rw [physicalLength_iterate s ℓ β hscale, ← hkn, pow_add]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlo (le_of_lt (pow_pos hβ k))
  · rw [physicalLength_iterate s ℓ β hscale, ← hkn, pow_add]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hhi (le_of_lt (pow_pos hβ k))

/-- Finitely many chosen literal zero-hit paths have a common padded depth.
No finiteness of balanced words is used in obtaining this depth. -/
theorem uniform_tileCut_depth (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (C : Finset Packet)
    (hhit : ∀ p ∈ C, ∃ q, Relation.ReflTransGen (InteriorStep s ℓ) p q ∧ q.delta = 0) :
    ∃ D, ∀ m : MarkedPair, m.packet ∈ C → TileCut s ℓ β m D := by
  classical
  have hdepth : ∀ p ∈ C, ∃ n, ∀ m : MarkedPair,
      m.packet = p → TileCut s ℓ β m n := by
    intro p hp
    obtain ⟨q, hpq, hq⟩ := hhit p hp
    exact packet_path_tileCut s ℓ β hpos hβ hscale hpq hq
  choose depth hdepth using hdepth
  let D := C.attach.sup (fun p => depth p.1 p.2)
  refine ⟨D, ?_⟩
  intro m hm
  apply TileCut.pad s ℓ β hβ hscale (hdepth m.packet hm m rfl)
  exact Finset.le_sup (f := fun p : {p // p ∈ C} => depth p.1 p.2)
    (Finset.mem_attach C ⟨m.packet, hm⟩)

private theorem balanced_prefix_boundary (ℓ : Fin 3 → ℝ)
    {w z u v ru rv : Word} (hwhole : Equiv1 w z)
    (hu : w = u ++ ru) (hv : z = v ++ rv) (hbal : Equiv1 u v) :
    ∃ j, factorBoundary ℓ (red w z) j = physicalLength ℓ u := by
  have hk : u.length ≤ w.length := by rw [hu]; simp
  have htop : w.take u.length = u := by rw [hu]; simp
  have hbot : z.take u.length = v := by rw [hbal.length_eq, hv]; simp
  obtain ⟨j, hj⟩ := (zero_return_iff hwhole hk).1 (by rwa [htop, hbot])
  refine ⟨j, ?_⟩
  unfold factorBoundary
  rw [← take_red_top hwhole.length_eq j, hj, htop]

/-- Actual balanced cuts in every selected overlapping tile force a bound on
every irreducible factor after the same inflation depth. The contradiction
uses consecutive ordinals in the complete reduction, retaining repetitions. -/
theorem factor_bound_of_tileCuts (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (M : ℝ) (hM : ∀ a, ℓ a ≤ M) (D : ℕ) {u v : Word} (hbal : Equiv1 u v)
    (hcuts : ∀ (top : Mark u) (bottom : Mark v),
      (MarkedPair.mk (u, v) top bottom).Overlaps ℓ →
      TileCut s ℓ β (MarkedPair.mk (u, v) top bottom) D)
    {U : WordPair} (hU : U ∈ red ((subst s)^[D] u) ((subst s)^[D] v)) :
    physicalLength ℓ U.1 ≤ 2 * β ^ D * M := by
  classical
  have hnonneg : ∀ a, 0 ≤ ℓ a := fun a => le_of_lt (hpos a)
  have hMpos : 0 < M := (hpos 0).trans_le (hM 0)
  let w := (subst s)^[D] u
  let z := (subst s)^[D] v
  let bs := red w z
  have hwhole : Equiv1 w z := equiv1_iterate_subst s D hbal
  obtain ⟨j, hj, hjU⟩ := List.getElem_of_mem hU
  have hordinal : bs[j]? = some U := by
    rw [List.getElem?_eq_getElem hj, hjU]
  let a := factorBoundary ℓ bs j
  let b := factorBoundary ℓ bs (j + 1)
  let c := β ^ D
  let R := c * M
  have hc : 0 < c := pow_pos hβ D
  have hR : 0 < R := mul_pos hc hMpos
  have hab : b = a + physicalLength ℓ U.1 := factorBoundary_succ ℓ hordinal
  have ha : 0 ≤ a := physicalLength_nonneg ℓ hnonneg _
  have hb : b ≤ c * physicalLength ℓ u := by
    have h := factorBoundary_mono ℓ hnonneg bs (Nat.succ_le_of_lt hj)
    have he : factorBoundary ℓ bs bs.length = c * physicalLength ℓ u := by
      simp only [factorBoundary, List.take_length, bs, red_top hwhole.length_eq]
      exact physicalLength_iterate s ℓ β hscale D u
    exact h.trans_eq he
  by_contra hbound
  have hlong : 2 * R < physicalLength ℓ U.1 := by
    simpa only [R, c, mul_assoc] using lt_of_not_ge hbound
  have hopen : (a + R) / c < (b - R) / c := by
    apply (div_lt_div_iff_of_pos_right hc).2
    linarith
  obtain ⟨x, hxlo, hxhi, hxavoid⟩ := exists_between_avoiding
    (prefixCuts ℓ u ∪ prefixCuts ℓ v) _ _ hopen
  have hxscaledlo : a + R < c * x := by
    simpa only [mul_comm] using (div_lt_iff₀ hc).1 hxlo
  have hxscaledhi : c * x < b - R := by
    simpa only [mul_comm] using (lt_div_iff₀ hc).1 hxhi
  have hx0 : 0 < x := by
    apply (mul_lt_mul_iff_right₀ hc).1
    simpa only [mul_zero] using (show 0 < c * x by linarith)
  have hxend : x < physicalLength ℓ u := by
    apply (mul_lt_mul_iff_right₀ hc).1
    linarith
  have hxendbot : x < physicalLength ℓ v := by
    rwa [← physicalLength_of_equiv1 ℓ hbal]
  have htopcut : ∀ i ≤ u.length, x ≠ physicalLength ℓ (u.take i) := by
    intro i hi he
    apply hxavoid
    rw [he]
    exact Finset.mem_union_left _ (mem_prefixCuts ℓ u i hi)
  have hbotcut : ∀ i ≤ v.length, x ≠ physicalLength ℓ (v.take i) := by
    intro i hi he
    apply hxavoid
    rw [he]
    exact Finset.mem_union_right _ (mem_prefixCuts ℓ v i hi)
  obtain ⟨top, htlo, hthi⟩ := exists_mark_containing ℓ u x hx0 hxend htopcut
  obtain ⟨bottom, hblo, hbhi⟩ := exists_mark_containing ℓ v x hx0 hxendbot hbotcut
  obtain ⟨pu, pv, ru, rv, hpu, hpv, hpbal, hplo, hphi⟩ :=
    hcuts top bottom ⟨x, htlo, hthi, hblo, hbhi⟩
  change c * physicalLength ℓ top.before ≤ physicalLength ℓ pu at hplo
  change physicalLength ℓ pu ≤ c * (physicalLength ℓ top.before + ℓ top.letter) at hphi
  have hletter := mul_le_mul_of_nonneg_left (hM top.letter) hc.le
  have htoplo := mul_lt_mul_of_pos_left htlo hc
  have htophi := mul_lt_mul_of_pos_left hthi hc
  have hcutlo : a < physicalLength ℓ pu := by dsimp [R] at hxscaledlo; nlinarith
  have hcuthi : physicalLength ℓ pu < b := by dsimp [R] at hxscaledhi; nlinarith
  obtain ⟨k, hk⟩ := balanced_prefix_boundary ℓ hwhole hpu hpv hpbal
  by_cases hkj : k ≤ j
  · have h := factorBoundary_mono ℓ hnonneg bs hkj
    rw [hk] at h
    exact (not_lt_of_ge h) hcutlo
  · have h := factorBoundary_mono ℓ hnonneg bs (show j + 1 ≤ k by omega)
    rw [hk] at h
    exact (not_lt_of_ge h) hcuthi

private theorem length_mul_le_physicalLength (ℓ : Fin 3 → ℝ) (μ : ℝ)
    (hμ : ∀ a, μ ≤ ℓ a) (w : Word) :
    (w.length : ℝ) * μ ≤ physicalLength ℓ w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.length_cons, Nat.cast_add, Nat.cast_one, physicalLength_cons]
    nlinarith [hμ a]

private theorem finite_words_length_le (N : ℕ) :
    {w : Word | w.length ≤ N}.Finite := by
  induction N with
  | zero =>
    apply (Set.finite_singleton ([] : Word)).subset
    intro w hw
    exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
  | succ N ih =>
    have hcons := ((Set.finite_univ : (Set.univ : Set (Fin 3)).Finite).prod ih).image
      (fun p : Fin 3 × Word => p.1 :: p.2)
    apply ((Set.finite_singleton ([] : Word)).union hcons).subset
    intro w hw
    cases w with
    | nil => exact Or.inl rfl
    | cons a w => exact Or.inr ⟨(a, w), ⟨Set.mem_univ a, by simpa using hw⟩, rfl⟩

/-- A positive lower letter length turns a physical factor bound into a finite
word-pair set. Both tracks are bounded because their Parikh vectors agree. -/
theorem finite_balanced_pairs_of_physical_bound (ℓ : Fin 3 → ℝ)
    (hpos : ∀ a, 0 < ℓ a) (B : ℝ) :
    {U : WordPair | Equiv1 U.1 U.2 ∧ physicalLength ℓ U.1 ≤ B}.Finite := by
  let μ := min (ℓ 0) (min (ℓ 1) (ℓ 2))
  have hμpos : 0 < μ := lt_min (hpos 0) (lt_min (hpos 1) (hpos 2))
  have hμ : ∀ a, μ ≤ ℓ a := by
    intro a
    fin_cases a
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N, hN⟩ := exists_nat_gt (B / μ)
  apply ((finite_words_length_le N).prod (finite_words_length_le N)).subset
  rintro U ⟨hbal, hbound⟩
  have hlen : U.1.length ≤ N := by
    have hL := (length_mul_le_physicalLength ℓ μ hμ U.1).trans hbound
    have hN' : B < (N : ℝ) * μ := (div_lt_iff₀ hμpos).1 hN
    have hlt : (U.1.length : ℝ) < (N : ℝ) :=
      (mul_lt_mul_iff_left₀ hμpos).1 (hL.trans_lt hN')
    exact le_of_lt (by exact_mod_cast hlt)
  exact ⟨hlen, by change U.2.length ≤ N; rwa [← hbal.length_eq]⟩

/-- Finite actual packet coverage and literal zero hits supply, rather than
assume, a uniform physical bound after a common depth. Generation `D + n`
is obtained from the actual coarse seed generation `n`. -/
theorem bounded_late_factors_of_finite_packet_hits
    (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (T : WordPair) (hT : Equiv1 T.1 T.2) (C : Finset Packet)
    (hcover : CoversSeedIterates s ℓ T (↑C : Set Packet))
    (hhit : ∀ p ∈ C, ∃ q, Relation.ReflTransGen (InteriorStep s ℓ) p q ∧ q.delta = 0) :
    ∃ D : ℕ, ∃ B : ℝ, ∀ n U,
      U ∈ red ((subst s)^[D + n] T.1) ((subst s)^[D + n] T.2) →
      physicalLength ℓ U.1 ≤ B := by
  let M := max (ℓ 0) (max (ℓ 1) (ℓ 2))
  have hM : ∀ a, ℓ a ≤ M := by
    intro a
    fin_cases a
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨D, hD⟩ := uniform_tileCut_depth s ℓ β hpos hβ hscale C hhit
  refine ⟨D, 2 * β ^ D * M, ?_⟩
  intro n U hU
  apply factor_bound_of_tileCuts s ℓ β hpos hβ hscale M hM D
    (equiv1_iterate_subst s n hT)
  · intro top bottom hover
    exact hD _ (hcover n top bottom hover)
  · simpa only [Function.iterate_add_apply] using hU

/-- Every actual irreducible factor in every generation belongs to a finite
set. The generations below the derived depth are included explicitly; there
is no assumption that the late-generation estimate already holds there. -/
theorem finite_factors_of_finite_packet_hits
    (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (T : WordPair) (hT : Equiv1 T.1 T.2) (C : Finset Packet)
    (hcover : CoversSeedIterates s ℓ T (↑C : Set Packet))
    (hhit : ∀ p ∈ C, ∃ q, Relation.ReflTransGen (InteriorStep s ℓ) p q ∧ q.delta = 0) :
    {U | ∃ n, U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2)}.Finite := by
  obtain ⟨D, B, hbound⟩ := bounded_late_factors_of_finite_packet_hits
    s ℓ β hpos hβ hscale T hT C hcover hhit
  let early := (List.range D).flatMap
    (fun n => red ((subst s)^[n] T.1) ((subst s)^[n] T.2))
  apply ((List.finite_toSet early).union
    (finite_balanced_pairs_of_physical_bound ℓ hpos B)).subset
  rintro U ⟨n, hn⟩
  by_cases hnD : n < D
  · exact Or.inl (List.mem_flatMap.mpr ⟨n, List.mem_range.mpr hnD, hn⟩)
  · refine Or.inr ⟨(red_isBlock (equiv1_iterate_subst s n hT) U hn).2.1, ?_⟩
    have he : D + (n - D) = n := by omega
    exact hbound (n - D) U (by simpa only [he] using hn)

/-- The existing actual terminal-child reachability set is finite under a
finite complete actual overlap cover with literal zero-offset hits. This is
the finiteness half of balanced-pair termination, with no productivity or
spectral conclusion and no supplied balanced-word carrier. -/
theorem finite_reachable_of_finite_packet_hits
    (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (T : WordPair) (hT : IsBlock T) (C : Finset Packet)
    (hcover : CoversSeedIterates s ℓ T (↑C : Set Packet))
    (hhit : ∀ p ∈ C, ∃ q, Relation.ReflTransGen (InteriorStep s ℓ) p q ∧ q.delta = 0) :
    {U | Relation.ReflTransGen (ChildNC s) T U}.Finite :=
  (Psc.TerminationFactors.finite_factors_iff_finite_reachableNC hT).1
    (finite_factors_of_finite_packet_hits s ℓ β hpos hβ hscale T hT.2.1 C hcover hhit)

/-! ## Integral-zero boundary control -/

/-- The middle `2` occurrences in the actual irreducible balanced pair
`021 / 120`. Unit lengths give physical alignment, while the preceding
letters have different integral Parikh vectors. -/
def physicalZeroControl : MarkedPair :=
  ⟨([0, 2, 1], [1, 2, 0]), ⟨[0], 2, [1], rfl⟩, ⟨[1], 2, [0], rfl⟩⟩

private theorem physicalLength_unit (w : Word) :
    physicalLength (fun _ => 1) w = (w.length : ℝ) := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih, add_comm]

/-- Even on a genuine irreducible balanced word pair, physical zero does
not give the depth-zero cut supplied by integral zero. This control rules
out dropping the exact integral target without rational independence. -/
theorem physical_zero_does_not_supply_tileCut :
    IsBlock physicalZeroControl.words ∧
      physicalZeroControl.Overlaps (fun _ => 1) ∧
      offset (fun _ => 1) physicalZeroControl.packet.delta = 0 ∧
      physicalZeroControl.packet.delta ≠ 0 ∧
      ¬ TileCut (fun a => [a]) (fun _ => 1) 1 physicalZeroControl 0 := by
  refine ⟨by unfold physicalZeroControl IsBlock; decide, ?_, ?_, by decide, ?_⟩
  · refine ⟨(3 / 2 : ℝ), ?_⟩
    change physicalLength (fun _ => 1) [0] < (3 / 2 : ℝ) ∧
      (3 / 2 : ℝ) < physicalLength (fun _ => 1) [0] + 1 ∧
      physicalLength (fun _ => 1) [1] < (3 / 2 : ℝ) ∧
      (3 / 2 : ℝ) < physicalLength (fun _ => 1) [1] + 1
    norm_num
  · change offset (fun _ => 1) (residual [0] [1]) = 0
    rw [offset_residual]
    simp
  · rintro ⟨u, v, ru, rv, hu, hv, hbal, hlo, hhi⟩
    change [0, 2, 1] = u ++ ru at hu
    change [1, 2, 0] = v ++ rv at hv
    have hlo' : (1 : ℝ) ≤ u.length := by
      simpa [physicalZeroControl, physicalLength_unit] using hlo
    have hhi' : u.length ≤ 2 := by
      change physicalLength (fun _ => 1) u ≤
        (1 : ℝ) ^ 0 * (physicalLength (fun _ => 1) [0] + 1) at hhi
      norm_num [physicalLength_unit] at hhi
      exact hhi
    have hlen : u.length = 1 ∨ u.length = 2 := by
      have hl : 1 ≤ u.length := by exact_mod_cast hlo'
      have hh : u.length ≤ 2 := hhi'
      omega
    have hu' : ([0, 2, 1] : Word).take u.length = u := by rw [hu]; simp
    have hv' : ([1, 2, 0] : Word).take u.length = v := by
      rw [hbal.length_eq, hv]
      simp
    have htest : Equiv1 (([0, 2, 1] : Word).take u.length)
        (([1, 2, 0] : Word).take u.length) := by rwa [hu', hv']
    have hcount := htest 0
    rcases hlen with hlen | hlen <;> simp [hlen] at hcount

end Psc.BHFiniteReachability
