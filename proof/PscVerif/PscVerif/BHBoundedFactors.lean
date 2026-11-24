import PscVerif.BHFiniteCarrier
import PscVerif.OccurrenceFinite
import PscVerif.OccurrenceInverse

/-!
# Literal zero hits from bounded actual balanced factors

A cut strictly inside the inflated common interval determines two literal
right-hand marks. Pulling back a common interior point recovers the original
ordered marks and their digit path. See
`docs/bh-higher-determinant-stop-go-2026-11-24.md`.
-/

namespace Psc.BHBoundedFactors

open Psc.Binomial Psc.Incidence Psc.Reduction Psc.Descendants
open Psc.OccurrenceNewborn Psc.OccurrenceTransport Psc.OccurrenceAncestry
open Psc.OccurrenceInverse Psc.BHFiniteReachability Psc.OccurrenceFinite

/-- A whole-word edge retains both marks with their original track order
and all surrounding letters. -/
def WholeStep (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (m m' : MarkedPair) : Prop :=
  ∃ (dt : Mark (s m.top.letter)) (db : Mark (s m.bottom.letter)),
    m.inflate s dt db = m' ∧ m'.Overlaps ℓ

theorem WholeStep.packet {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ} {m m' : MarkedPair}
    (h : WholeStep s ℓ m m') : InteriorStep s ℓ m.packet m'.packet := by
  obtain ⟨dt, db, rfl, hi⟩ := h
  exact ⟨m.inflate_digitStep s dt db, (MarkedPair.overlaps_iff ℓ _).mp hi⟩

private def inside {w : Word} (ℓ : Fin 3 → ℝ) (m : Mark w) (x : ℝ) : Prop :=
  physicalLength ℓ m.before < x ∧ x < physicalLength ℓ m.before + ℓ m.letter

/-- At an inflated common interior point, the terminal marks determine a
composable whole-word path from the specified original marks. -/
private theorem path_at_scaled_point (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (m : MarkedPair) (n : ℕ)
    (top : Mark ((subst s)^[n] m.words.1)) (bot : Mark ((subst s)^[n] m.words.2))
    (x : ℝ) (ht : inside ℓ m.top x) (hb : inside ℓ m.bottom x)
    (hT : inside ℓ top (β ^ n * x)) (hB : inside ℓ bot (β ^ n * x)) :
    Relation.ReflTransGen (WholeStep s ℓ) m
      ⟨(((subst s)^[n] m.words.1), ((subst s)^[n] m.words.2)), top, bot⟩ := by
  revert top bot hT hB
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
    intro top bot hT hB
    have heqt := marks_eq_of_overlap ℓ (fun a => (hpos a).le) top m.top x
      hT.1 hT.2 ht.1 ht.2
    have heqb := marks_eq_of_overlap ℓ (fun a => (hpos a).le) bot m.bottom x
      hB.1 hB.2 hb.1 hb.2
    cases heqt
    cases heqb
    cases m
    exact .refl
  | succ n ih =>
    let goal (T : WordPair) : Prop :=
      ∀ (t : Mark T.1) (b : Mark T.2),
        inside ℓ t (β ^ (n + 1) * x) → inside ℓ b (β ^ (n + 1) * x) →
        Relation.ReflTransGen (WholeStep s ℓ) m ⟨T, t, b⟩
    change goal (((subst s)^[n + 1] m.words.1), ((subst s)^[n + 1] m.words.2))
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    intro top bot hT hB
    obtain ⟨pt, dt, rfl⟩ := mark_uninflate s _ top
    obtain ⟨pb, db, rfl⟩ := mark_uninflate s _ bot
    have pull {w : Word} (p : Mark w) (d : Mark (s p.letter))
        (h : inside ℓ (p.inflate s d) (β ^ (n + 1) * x)) :
        inside ℓ p (β ^ n * x) := by
      obtain ⟨hlo, hhi⟩ := inflate_interval_bounds s ℓ β hpos hscale p d
      obtain ⟨hl, hr⟩ := h
      rw [pow_succ, mul_comm (β ^ n) β, mul_assoc] at hl hr
      exact ⟨lt_of_mul_lt_mul_left (hlo.trans_lt hl) hβ.le,
        lt_of_mul_lt_mul_left (hr.trans_le hhi) hβ.le⟩
    apply (ih pt pb (pull pt dt hT) (pull pb db hB)).tail
    exact ⟨dt, db, rfl, β ^ (n + 1) * x, hT.1, hT.2, hB.1, hB.2⟩

/-- A window wider than a bound for the factors contains a common Parikh
cut strictly between its endpoints. -/
private theorem partition_cut (ℓ : Fin 3 → ℝ) (B : ℝ) (bs : List WordPair)
    (hbs : ∀ U ∈ bs, Equiv1 U.1 U.2 ∧ physicalLength ℓ U.1 ≤ B)
    (x y : ℝ) (hx : 0 ≤ x)
    (hy : y ≤ physicalLength ℓ (bs.map Prod.fst).flatten) (hwide : x + B < y)
    (hB : 0 ≤ B) :
    ∃ p q ru rv : Word,
      (bs.map Prod.fst).flatten = p ++ ru ∧ (bs.map Prod.snd).flatten = q ++ rv ∧
      Equiv1 p q ∧ x < physicalLength ℓ p ∧ physicalLength ℓ p < y := by
  induction bs generalizing x y with
  | nil =>
    simp only [List.map_nil, List.flatten_nil, physicalLength_nil] at hy
    linarith
  | cons U bs ih =>
    obtain ⟨hbal, hlen⟩ := hbs U (List.mem_cons_self)
    simp only [List.map_cons, List.flatten_cons, physicalLength_append] at hy ⊢
    by_cases hcut : x < physicalLength ℓ U.1
    · exact ⟨U.1, U.2, _, _, rfl, rfl, hbal, hcut, by linarith⟩
    · obtain ⟨p, q, ru, rv, htop, hbot, hpq, hlo, hhi⟩ :=
        ih (fun V hV => hbs V (List.mem_cons_of_mem U hV))
          (x - physicalLength ℓ U.1) (y - physicalLength ℓ U.1)
          (sub_nonneg.mpr (le_of_not_gt hcut)) (by linarith) (by linarith)
      refine ⟨U.1 ++ p, U.2 ++ q, ru, rv, ?_, ?_, hbal.append hpq, ?_, ?_⟩
      · rw [htop, List.append_assoc]
      · rw [hbot, List.append_assoc]
      · rw [physicalLength_append]
        linarith
      · rw [physicalLength_append]
        linarith

/-- A bound for the actual reductions of a balanced word pair gives a zero
hit from every original strict overlap. The endpoint has balanced full
prefixes and the complete two-track ancestry. -/
theorem whole_zero_hit_of_bound (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 1 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (m : MarkedPair) (hbal : Equiv1 m.words.1 m.words.2) (hover : m.Overlaps ℓ)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ n U, U ∈ red ((subst s)^[n] m.words.1) ((subst s)^[n] m.words.2) →
      physicalLength ℓ U.1 ≤ B) :
    ∃ m', Relation.ReflTransGen (WholeStep s ℓ) m m' ∧ m'.packet.delta = 0 := by
  obtain ⟨x, hxt, htx, hxb, hbx⟩ := hover
  obtain ⟨y, hxy, hy⟩ := exists_between (lt_min htx hbx)
  have hβpos : 0 < β := lt_trans zero_lt_one hβ
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (B / (y - x)) hβ
  have hwide := (div_lt_iff₀ (sub_pos.mpr hxy)).mp hn
  let u := (subst s)^[n] m.words.1
  let v := (subst s)^[n] m.words.2
  have huv : Equiv1 u v := equiv1_iterate_subst s n hbal
  have hnonneg : ∀ a, 0 ≤ ℓ a := fun a => (hpos a).le
  have hpow : 0 < β ^ n := pow_pos hβpos n
  have hleft : 0 ≤ β ^ n * x := mul_nonneg hpow.le
    ((physicalLength_nonneg ℓ hnonneg m.top.before).trans hxt.le)
  have hright : β ^ n * y < physicalLength ℓ u := by
    rw [physicalLength_iterate s ℓ β hscale]
    exact mul_lt_mul_of_pos_left ((lt_min_iff.mp hy).1.trans_le
      (mark_prefix_bounds ℓ hnonneg m.top).2) hpow
  have hright' : β ^ n * y < physicalLength ℓ v := by
    rw [physicalLength_iterate s ℓ β hscale]
    exact mul_lt_mul_of_pos_left ((lt_min_iff.mp hy).2.trans_le
      (mark_prefix_bounds ℓ hnonneg m.bottom).2) hpow
  obtain ⟨p, q, ru, rv, hp, hq, hpq, hlo, hhi⟩ :=
    partition_cut ℓ B (red u v)
      (fun U hU => ⟨(red_isBlock huv U hU).2.1, hbound n U hU⟩)
      (β ^ n * x) (β ^ n * y) hleft (by rw [red_top huv.length_eq]; exact hright.le)
      (by nlinarith only [hwide]) hB
  rw [red_top huv.length_eq] at hp
  rw [red_bot huv.length_eq] at hq
  have hcut := physicalLength_of_equiv1 ℓ hpq
  cases ru with
  | nil => simp only [List.append_nil] at hp; rw [hp] at hright; linarith
  | cons a ru =>
    cases rv with
    | nil => simp only [List.append_nil] at hq; rw [hq] at hright'; linarith
    | cons b rv =>
      let top : Mark u := ⟨p, a, ru, hp⟩
      let bot : Mark v := ⟨q, b, rv, hq⟩
      obtain ⟨z, hzlo, hzhi⟩ := exists_between
        (lt_min hhi (lt_min (lt_add_of_pos_right _ (hpos a)) (lt_add_of_pos_right _ (hpos b))))
      let point := z / β ^ n
      have hpointlo : x < point := (lt_div_iff₀ hpow).2 (by nlinarith only [hlo, hzlo])
      have hpointhi : point < y := (div_lt_iff₀ hpow).2
        (by simpa only [mul_comm y] using (lt_min_iff.mp hzhi).1)
      have hpoint : β ^ n * point = z := by
        change β ^ n * (z / β ^ n) = z
        rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hpow)]
      have hends := lt_min_iff.mp (lt_min_iff.mp hzhi).2
      refine ⟨⟨(u, v), top, bot⟩, path_at_scaled_point s ℓ β hpos hβpos hscale m n top bot
        point ⟨hxt.trans hpointlo, hpointhi.trans (lt_min_iff.mp hy).1⟩
        ⟨hxb.trans hpointlo, hpointhi.trans (lt_min_iff.mp hy).2⟩ ?_ ?_, ?_⟩
      · rw [hpoint]
        exact ⟨hzlo, hends.1⟩
      · rw [hpoint]
        change physicalLength ℓ q < z ∧ z < physicalLength ℓ q + ℓ b
        rw [← hcut]
        exact ⟨hzlo, hends.2⟩
      · exact sub_eq_zero.mpr (parikhZ_eq_of_equiv1 hpq)


private def occursIn (ℓ : Fin 3 → ℝ) (T : WordPair) (p : Packet) : Prop :=
  ∃ (top : Mark T.1) (bot : Mark T.2),
    let m : MarkedPair := ⟨T, top, bot⟩
    m.Overlaps ℓ ∧ m.packet = p

/-- The packet set of the actual strict overlaps in the complete seed
iterates, with both ordered types and the full integral displacement. -/
def seedPackets (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (T : WordPair) : Set Packet :=
  {p | ∃ n, occursIn ℓ (((subst s)^[n] T.1), ((subst s)^[n] T.2)) p}

/-- Any literal child in the geometry is realized in the next actual
generation, including all children of already aligned marks. -/
theorem seedPackets_closed {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ} {T : WordPair}
    {p q : Packet} (hp : p ∈ seedPackets s ℓ T) (hedge : InteriorStep s ℓ p q) :
    q ∈ seedPackets s ℓ T := by
  obtain ⟨n, top, bot, _, rfl⟩ := hp
  let m : MarkedPair := ⟨(((subst s)^[n] T.1), ((subst s)^[n] T.2)), top, bot⟩
  obtain ⟨⟨dt, db, hq⟩, hqint⟩ := hedge
  have hnext : (m.inflate s dt db).packet = q := (m.inflate_packet s dt db).trans hq.symm
  refine ⟨n + 1, ?_⟩
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
  rw [← hnext] at hqint
  exact ⟨m.top.inflate s dt, m.bottom.inflate s db,
    (MarkedPair.overlaps_iff ℓ _).mpr hqint, hnext⟩

/-- Localizing each strict overlap to its own actual factor makes the
seed packet set finite as soon as the full factor set is finite. -/
theorem seedPackets_finite_of_finite_factors (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (hpos : ∀ a, 0 < ℓ a) (T : WordPair) (hT : Equiv1 T.1 T.2)
    (hfin : {U | ∃ n, U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2)}.Finite) :
    (seedPackets s ℓ T).Finite := by
  apply (packetSupport hfin.toFinset).finite_toSet.subset
  rintro _ ⟨n, top, bot, hover, rfl⟩
  let m : MarkedPair := ⟨(((subst s)^[n] T.1), ((subst s)^[n] T.2)), top, bot⟩
  have hbal : Equiv1 m.words.1 m.words.2 := equiv1_iterate_subst s n hT
  let L := m.localize ℓ hpos hbal hover
  exact mem_packetSupport.mpr ⟨L.target,
    hfin.mem_toFinset.mpr ⟨n, List.mem_of_getElem? L.atOrdinal⟩, L.packet_eq hbal⟩

/-- A uniform physical factor bound supplies an integral zero hit for
every member of the actual seed packet set. -/
theorem seedPackets_zero_hits_of_bound (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (β : ℝ) (hpos : ∀ a, 0 < ℓ a) (hβ : 1 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (T : WordPair) (hT : Equiv1 T.1 T.2) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ n U, U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2) →
      physicalLength ℓ U.1 ≤ B) :
    ∀ p ∈ seedPackets s ℓ T, ∃ q,
      Relation.ReflTransGen (InteriorStep s ℓ) p q ∧ q.delta = 0 := by
  rintro _ ⟨n, top, bot, hover, rfl⟩
  let m : MarkedPair := ⟨(((subst s)^[n] T.1), ((subst s)^[n] T.2)), top, bot⟩
  have hlate : ∀ j U, U ∈ red ((subst s)^[j] m.words.1) ((subst s)^[j] m.words.2) →
      physicalLength ℓ U.1 ≤ B := by
    intro j U hU
    exact hbound (j + n) U (by simpa only [Function.iterate_add_apply] using hU)
  obtain ⟨m', hpath, hzero⟩ := whole_zero_hit_of_bound s ℓ β hpos hβ hscale
    m (equiv1_iterate_subst s n hT) hover B hB hlate
  exact ⟨m'.packet, hpath.lift MarkedPair.packet (fun _ _ h => h.packet), hzero⟩

/-- The forward BH carrier contract is equivalent to finite actual
balanced-pair reachability for an irreducible seed in expanding geometry.
The reverse direction can choose exactly the packets of the seed iterates. -/
theorem finite_reachable_iff_closed_packet_cover (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (β : ℝ) (hpos : ∀ a, 0 < ℓ a) (hβ : 1 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a) (T : WordPair) (hT : IsBlock T) :
    {U | Relation.ReflTransGen (ChildNC s) T U}.Finite ↔
      ∃ C : Finset Packet, CoversWords ℓ T (↑C : Set Packet) ∧
        (∀ p ∈ C, ∀ q, InteriorStep s ℓ p q → q ∈ C) ∧
        (∀ p ∈ C, ∃ q, Relation.ReflTransGen (InteriorStep s ℓ) p q ∧ q.delta = 0) := by
  constructor
  · intro hreach
    have hfin := (Psc.TerminationFactors.finite_factors_iff_finite_reachableNC hT).2 hreach
    have hcarrier := seedPackets_finite_of_finite_factors s ℓ hpos T hT.2.1 hfin
    obtain ⟨B, hbound⟩ := (hfin.image (fun U => physicalLength ℓ U.1)).bddAbove
    have hhit := seedPackets_zero_hits_of_bound s ℓ β hpos hβ hscale T hT.2.1
      (max 0 B) (le_max_left _ _)
      (fun n U hU => (hbound ⟨U, ⟨n, hU⟩, rfl⟩).trans (le_max_right _ _))
    refine ⟨hcarrier.toFinset, ?_, ?_, fun p hp => hhit p (hcarrier.mem_toFinset.mp hp)⟩
    · intro top bot hover
      exact hcarrier.mem_toFinset.mpr ⟨0, top, bot, hover, rfl⟩
    · intro p hp q hedge
      exact hcarrier.mem_toFinset.mpr (seedPackets_closed (hcarrier.mem_toFinset.mp hp) hedge)
  · rintro ⟨C, hseed, hclosed, hhit⟩
    exact Psc.BHFiniteCarrier.finite_reachable_of_closed_packet_cover s ℓ β hpos
      (zero_lt_one.trans hβ) hscale T hT C hseed hclosed hhit


/-- Marks in an actual irreducible factor can be placed back in both whole
tracks. The preceding factors contribute one balanced prefix. -/
private theorem occursIn_of_factor (ℓ : Fin 3 → ℝ) {u v : Word}
    (hbal : Equiv1 u v) (m : MarkedPair) (hm : m.words ∈ red u v)
    (hi : m.packet.Interior ℓ) : occursIn ℓ (u, v) m.packet := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hm
  let a := (pre.map Prod.fst).flatten
  let b := (pre.map Prod.snd).flatten
  have hab : Equiv1 a b := equiv1_join pre fun V hV =>
    (red_isBlock hbal V (by rw [hsplit]; exact List.mem_append_left _ hV)).2.1
  have hu : u = a ++ m.words.1 ++ (post.map Prod.fst).flatten := by
    rw [← red_top hbal.length_eq, hsplit]
    simp [a, List.append_assoc]
  have hv : v = b ++ m.words.2 ++ (post.map Prod.snd).flatten := by
    rw [← red_bot hbal.length_eq, hsplit]
    simp [b, List.append_assoc]
  let top : Mark u := ⟨a ++ m.top.before, m.top.letter,
    m.top.after ++ (post.map Prod.fst).flatten, by
      rw [hu]
      simpa [List.append_assoc] using
        congrArg (fun w => a ++ w ++ (post.map Prod.fst).flatten) m.top.split⟩
  let bot : Mark v := ⟨b ++ m.bottom.before, m.bottom.letter,
    m.bottom.after ++ (post.map Prod.snd).flatten, by
      rw [hv]
      simpa [List.append_assoc] using
        congrArg (fun w => b ++ w ++ (post.map Prod.snd).flatten) m.bottom.split⟩
  let g : MarkedPair := ⟨(u, v), top, bot⟩
  have hg : g.packet = m.packet := by
    change (⟨m.top.letter, m.bottom.letter,
      residual (a ++ m.top.before) (b ++ m.bottom.before)⟩ : Packet) = m.packet
    rw [residual_trim hab]
    rfl
  exact ⟨top, bot, (MarkedPair.overlaps_iff ℓ g).mpr (by rwa [hg]), hg⟩

/-- If the finite closed carrier hits equal-letter zero, the terminal
balanced-pair algorithm also has productivity from every reachable factor. -/
theorem terminates_of_closed_diagonal_cover (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (β : ℝ) (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a) (T : WordPair) (hT : IsBlock T)
    (C : Finset Packet) (hseed : CoversWords ℓ T (↑C : Set Packet))
    (hclosed : ∀ p ∈ C, ∀ q, InteriorStep s ℓ p q → q ∈ C)
    (hhit : ∀ p ∈ C, ∃ q, Relation.ReflTransGen (InteriorStep s ℓ) p q ∧ q.Diagonal) :
    Psc.StrictSystem.TerminatesWithCoincidence s T := by
  have hcover := Psc.BHFiniteCarrier.covers_seed_iterates_of_closed
    s ℓ β hpos hβ hscale T C hseed hclosed
  refine ⟨Psc.BHFiniteCarrier.finite_reachable_of_closed_packet_cover
    s ℓ β hpos hβ hscale T hT C hseed hclosed (fun p hp => ?_), ?_⟩
  · obtain ⟨q, hpath, hd⟩ := hhit p hp
    exact ⟨q, hpath, hd.2⟩
  · intro U hU
    obtain ⟨n, hn⟩ := (reflTransGen_child_iff s hT).mp
      (hU.lift id fun _ _ h => h.2)
    have hb := equiv1_iterate_subst s n hT.2.1
    have hblock := red_isBlock hb U hn
    have hbot : U.2 ≠ [] := fun h => hblock.1
      (List.length_eq_zero_iff.mp (by simpa [h] using hblock.2.1.length_eq))
    obtain ⟨m, hm, hi⟩ := first_marks_interior U hblock.1 hbot ℓ hpos
    have hfactor : m.words ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2) := hm ▸ hn
    obtain ⟨top, bot, hover, hpack⟩ := occursIn_of_factor ℓ hb m hfactor hi
    have hmem : m.packet ∈ C := hpack ▸ hcover n top bot hover
    obtain ⟨q, hpath, hdiag⟩ := hhit m.packet hmem
    obtain ⟨V, hV, _, heq⟩ := packet_path_literal_target s ℓ hpos m (hm ▸ hblock) hpath hdiag
    rw [hm] at hV
    exact Psc.TerminationFactors.productive_of_full_child_path hV heq

/-! ## Expanding zero-hit control -/

private def swapSigma (a : Fin 3) : Word :=
  if a = 0 then [0, 1] else if a = 1 then [1, 0] else [2, 2]

private def swapSeed : WordPair := ([0, 1], [1, 0])

private theorem swap_reachable (U : WordPair)
    (hU : Relation.ReflTransGen (ChildNC swapSigma) swapSeed U) :
    U = swapSeed ∨ U = swapSeed.swap := by
  induction hU with
  | refl => exact Or.inl rfl
  | tail _ hstep ih =>
    have hred : red (subst swapSigma swapSeed.1) (subst swapSigma swapSeed.2) =
      [swapSeed, swapSeed.swap] := by decide
    have hred' : red (subst swapSigma swapSeed.swap.1) (subst swapSigma swapSeed.swap.2) =
      [swapSeed.swap, swapSeed] := by decide
    have hmem := hstep.2
    rcases ih with rfl | rfl
    · change _ ∈ red (subst swapSigma swapSeed.1) (subst swapSigma swapSeed.2) at hmem
      simpa only [hred, List.mem_cons, List.not_mem_nil, or_false] using hmem
    · change _ ∈ red (subst swapSigma swapSeed.swap.1) (subst swapSigma swapSeed.swap.2) at hmem
      rw [hred'] at hmem
      exact (List.mem_cons.mp hmem).elim Or.inr (fun h => Or.inl (List.mem_singleton.mp h))

/-- The two Thue–Morse swap blocks have finite reachability in expanding
unit geometry and hence a closed carrier with literal zero hits. Neither
reachable block is a label coincidence. -/
theorem expanding_zero_cover_without_coincidence :
    (∃ C : Finset Packet, CoversWords (fun _ => 1) swapSeed (↑C : Set Packet) ∧
      (∀ p ∈ C, ∀ q, InteriorStep swapSigma (fun _ => 1) p q → q ∈ C) ∧
      (∀ p ∈ C, ∃ q, Relation.ReflTransGen (InteriorStep swapSigma (fun _ => 1)) p q ∧
        q.delta = 0)) ∧ ¬ Psc.StrictSystem.TerminatesWithCoincidence swapSigma swapSeed := by
  have hblock : IsBlock swapSeed := by unfold swapSeed IsBlock; decide
  have hscale : ∀ a, physicalLength (fun _ => 1) (swapSigma a) = (2 : ℝ) * 1 := by
    intro a
    fin_cases a <;> norm_num [swapSigma]
  have hfinite : {U | Relation.ReflTransGen (ChildNC swapSigma) swapSeed U}.Finite := by
    exact ((Set.finite_singleton swapSeed).union (Set.finite_singleton swapSeed.swap)).subset
      fun U hU => swap_reachable U hU
  refine ⟨(finite_reachable_iff_closed_packet_cover swapSigma (fun _ => 1) 2
    (fun _ => zero_lt_one) (by norm_num) hscale swapSeed hblock).mp hfinite, ?_⟩
  rintro ⟨_, hprod⟩
  obtain ⟨U, hu, hdiag⟩ := hprod swapSeed .refl
  rcases swap_reachable U hu with rfl | rfl
  · exact (by decide : swapSeed.1 ≠ swapSeed.2) hdiag
  · exact (by decide : swapSeed.swap.1 ≠ swapSeed.swap.2) hdiag

end Psc.BHBoundedFactors
