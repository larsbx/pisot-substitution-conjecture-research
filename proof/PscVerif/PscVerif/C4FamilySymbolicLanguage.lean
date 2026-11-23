import PscVerif.C4FamilySymbolicSection
import Mathlib.Data.List.OfFn

/-! The letter itinerary of the actual tile-start transversal has exactly
the bi-infinite words with all finite subwords in the literal language. -/

namespace Psc.C4FamilySymbolicLanguage

open Function Filter Set
open scoped Topology
open Psc.ParameterFamilyTiling (geometry expansion_gt_one every_letter_in_square)
open Psc.PeriodicPartnerHull (LengthSubst)
open Psc.PeriodicPartnerRealization (origin tileAt_eq tileAt_spec)
open Psc.PeriodicPartnerHullCompact (rightTile leftTile rightTile_start_succ leftTile_start_succ)
open Psc.PeriodicPartnerEvenTails (place_append)
open Psc.C4FamilySymbolicSection

variable {k : ℕ} {hk : 1 ≤ k}

local notation "G" => geometry k hk
local notation "H" => nextHomeomorph (k := k) (hk := hk)

/-- Read the label at each signed tile index. Index zero is the tile
starting at the marked origin. -/
noncomputable def itinerary (B : Transversal k hk) (i : ℤ) : Fin 3 :=
  (origin ((H ^ i) B).1).1

@[simp] theorem itinerary_next (B : Transversal k hk) (i : ℤ) :
    itinerary (next B) i = itinerary B (i + 1) := by
  rw [itinerary, itinerary, zpow_add_one, Homeomorph.mul_apply]
  rfl

theorem continuous_itinerary : Continuous (itinerary (k := k) (hk := hk)) := by
  apply continuous_pi
  intro i
  exact ((Psc.PeriodicPartnerOriginContinuity.isLocallyConstant_origin (S := G)).comp
    Prod.fst).continuous.comp (continuous_subtype_val.comp ((H ^ i).continuous))

theorem itinerary_injective : Injective (itinerary (k := k) (hk := hk)) := by
  intro B D h
  have hR (n : ℕ) : (rightTile B.1 n).1 = (rightTile D.1 n).1 := by
    have he := congrFun h (n : ℤ)
    simpa only [itinerary, origin_pow_label] using he
  have hL (n : ℕ) : (leftTile B.1 n).1 = (leftTile D.1 n).1 := by
    have he := congrFun h (-(n : ℤ))
    simpa only [itinerary, origin_neg_pow_label] using he
  have hr (n : ℕ) : rightTile B.1 n = rightTile D.1 n := by
    apply Prod.ext (hR n)
    induction n with
    | zero => exact B.2.trans D.2.symm
    | succ n ih => rw [rightTile_start_succ, rightTile_start_succ, ih, hR]
  have hl (n : ℕ) : leftTile B.1 n = leftTile D.1 n := by
    apply Prod.ext (hL n)
    induction n with
    | zero => exact B.2.trans D.2.symm
    | succ n ih => rw [leftTile_start_succ, leftTile_start_succ, ih, hL]
  apply Subtype.ext
  apply Subtype.ext
  ext q
  constructor
  · intro hq
    obtain ⟨n, rfl | rfl⟩ := exists_right_or_left hq
    · rw [hr]; exact Psc.PeriodicPartnerHullCompact.rightTile_mem D.1 n
    · rw [hl]; exact Psc.PeriodicPartnerHullCompact.leftTile_mem D.1 n
  · intro hq
    obtain ⟨n, rfl | rfl⟩ := exists_right_or_left hq
    · rw [← hr]; exact Psc.PeriodicPartnerHullCompact.rightTile_mem B.1 n
    · rw [← hl]; exact Psc.PeriodicPartnerHullCompact.leftTile_mem B.1 n

/-- A finite block beginning at a signed index. -/
def block (x : ℤ → Fin 3) (i : ℤ) (n : ℕ) : List (Fin 3) :=
  List.ofFn fun j : Fin n => x (i + (j : ℕ))

private theorem block_at (x : ℤ → Fin 3) (i : ℤ) {n j : ℕ} (hj : j < n) :
    (block x i n)[j]? = some (x (i + (j : ℤ))) := by
  simp [block, hj]

/-- Words in the literal substitution language. -/
def LegalWord (k : ℕ) (hk : 1 ≤ k) (w : List (Fin 3)) : Prop :=
  ∃ a n, w.IsInfix ((geometry k hk).iterWord n a)

/-- The two-sided subshift defined by its substitution language. -/
def LegalSequence (k : ℕ) (hk : 1 ≤ k) (x : ℤ → Fin 3) : Prop :=
  ∀ i n, LegalWord k hk (block x i n)

abbrev SymbolicHull (k : ℕ) (hk : 1 ≤ k) := {x : ℤ → Fin 3 // LegalSequence k hk x}

private noncomputable def forwardWord (B : Transversal k hk) : ℕ → List (Fin 3)
  | 0 => []
  | n + 1 => (origin B.1).1 :: forwardWord (next B) n

private theorem itinerary_reindex (B : Transversal k hk) (i j : ℤ) :
    itinerary ((H ^ i) B) j = itinerary B (j + i) := by
  rw [itinerary, itinerary, zpow_add, Homeomorph.mul_apply]

private theorem forwardWord_eq_block (B : Transversal k hk) (n : ℕ) :
    forwardWord B n = block (itinerary B) 0 n := by
  induction n generalizing B with
  | zero => simp [forwardWord, block]
  | succ n ih =>
    rw [forwardWord, ih]
    simp only [block, List.ofFn_succ]
    congr 1

private theorem placed_forwardWord (B : Transversal k hk) (n : ℕ) :
    ∀ q ∈ (G).place (forwardWord B n) 0, q ∈ B.1.1 := by
  induction n generalizing B with
  | zero => simp [forwardWord, LengthSubst.place]
  | succ n ih =>
    intro q hq
    simp only [forwardWord, LengthSubst.place, List.mem_cons, zero_add] at hq
    rcases hq with rfl | hq
    · have hT := (tileAt_spec B.1 0).1
      change origin B.1 ∈ B.1.1 at hT
      have he : ((origin B.1).1, (0 : ℝ)) = origin B.1 := Prod.ext rfl B.2.symm
      rwa [he]
    · have he := (G).place_add (forwardWord (next B) n) 0 (roof B)
      rw [zero_add] at he
      change q ∈ (G).place (forwardWord (next B) n) (roof B) at hq
      rw [he] at hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      exact ih (next B) r hr

private theorem forwardWord_eq_of_placed (B : Transversal k hk) (w : List (Fin 3))
    (h : ∀ q ∈ (G).place w 0, q ∈ B.1.1) : forwardWord B w.length = w := by
  induction w generalizing B with
  | nil => rfl
  | cons a w ih =>
    have ha : (a, (0 : ℝ)) ∈ B.1.1 := h _ (by simp [LengthSubst.place])
    have he : origin B.1 = (a, 0) :=
      tileAt_eq ha ⟨le_rfl, by simpa using (G).ℓ_pos a⟩
    have hroof : roof B = (G).ℓ a := by simp [roof, he]
    simp only [List.length_cons, forwardWord, he, List.cons.injEq, true_and]
    apply ih (next B)
    intro q hq
    change (q.1, q.2 + roof B) ∈ B.1.1
    apply h
    rw [LengthSubst.place, List.mem_cons, zero_add, ← hroof]
    refine Or.inr ?_
    have hh := (G).place_add w 0 (roof B)
    rw [zero_add] at hh
    rw [hh]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩

private theorem prefix_of_place_subset {u v : List (Fin 3)} {x : ℝ}
    (h : ∀ q ∈ (G).place u x, q ∈ (G).place v x) : u.IsPrefix v := by
  induction u generalizing v x with
  | nil => exact ⟨v, rfl⟩
  | cons a u ih =>
    cases v with
    | nil => exact (List.not_mem_nil (h (a, x) (by simp [LengthSubst.place]))).elim
    | cons b v =>
      have he : a = b := by
        rcases List.mem_cons.mp (h (a, x) (by simp [LengthSubst.place])) with he | he
        · exact congrArg Prod.fst he
        · have hb := ((G).place_mem_bounds he).1
          linarith [(G).ℓ_pos b]
      subst b
      obtain ⟨p, hp⟩ := ih (v := v) (x := x + (G).ℓ a) fun q hq => by
        rcases List.mem_cons.mp (h q (List.mem_cons_of_mem _ hq)) with he | he
        · have ha := ((G).place_mem_bounds hq).1
          rw [he] at ha
          linarith [(G).ℓ_pos a]
        · exact he
      exact ⟨p, by simpa only [List.cons_append] using congrArg (List.cons a) hp⟩

private theorem infix_of_place_subset {u v : List (Fin 3)} {x y : ℝ}
    (h : ∀ q ∈ (G).place u x, q ∈ (G).place v y) : u.IsInfix v := by
  induction v generalizing u x y with
  | nil =>
    cases u with
    | nil => exact ⟨[], [], rfl⟩
    | cons a w => exact (List.not_mem_nil (h (a, x) (by simp [LengthSubst.place]))).elim
  | cons b v ih =>
    cases u with
    | nil => exact ⟨[], b :: v, rfl⟩
    | cons a u =>
      rcases List.mem_cons.mp (h (a, x) (by simp [LengthSubst.place])) with hs | ht
      · obtain rfl : x = y := congrArg Prod.snd hs
        obtain ⟨post, he⟩ := prefix_of_place_subset h
        exact ⟨[], post, he⟩
      · have hstart := ((G).place_mem_bounds ht).1
        obtain ⟨pre, post, he⟩ := ih (u := a :: u) (x := x) (y := y + (G).ℓ b)
          (fun q hq => by
            rcases List.mem_cons.mp (h q hq) with heq | hh
            · have hb := ((G).place_mem_bounds hq).1
              rw [heq] at hb
              linarith [(G).ℓ_pos b]
            · exact hh)
        exact ⟨b :: pre, post, by simpa only [List.cons_append] using congrArg (List.cons b) he⟩

private theorem forwardWord_legal (B : Transversal k hk) (n : ℕ) :
    LegalWord k hk (forwardWord B n) := by
  let w := forwardWord B n
  let L := (w.map (G).ℓ).sum
  have hL : 0 ≤ L := (G).sum_nonneg w
  obtain ⟨a, j, t, hj⟩ := B.1.2.2 (L + 1)
  refine ⟨a, j, infix_of_place_subset (k := k) (hk := hk) (x := t) (y := 0) ?_⟩
  intro q hq
  have he := (G).place_add w 0 t
  rw [zero_add] at he
  change q ∈ (G).place w t at hq
  rw [he] at hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  have hbounds := (G).place_mem_bounds hp
  have hp' : ((G).supp p ∩ Ioo (-(L + 1)) (L + 1)).Nonempty := by
    refine ⟨p.2, ⟨le_rfl, lt_add_of_pos_right _ ((G).ℓ_pos _)⟩, ?_⟩
    change 0 ≤ p.2 ∧ p.2 + (G).ℓ p.1 ≤ 0 + L at hbounds
    exact ⟨by linarith [hbounds.1], by linarith [hbounds.2, (G).ℓ_pos p.1]⟩
  have hm := hj p (placed_forwardWord B n p hp) hp'
  rwa [(G).supertile_eq_place] at hm

private theorem block_reindex (B : Transversal k hk) (i : ℤ) (n : ℕ) :
    block (itinerary ((H ^ i) B)) 0 n = block (itinerary B) i n := by
  unfold block
  congr 1
  funext j
  rw [itinerary_reindex, zero_add, add_comm]

theorem itinerary_legal (B : Transversal k hk) :
    LegalSequence k hk (itinerary B) := by
  intro i n
  rw [← block_reindex B i n, ← forwardWord_eq_block]
  exact forwardWord_legal _ n

private theorem exists_placed_legalWord (T : (G).Hull) {w : List (Fin 3)}
    (hw : LegalWord k hk w) :
    ∃ x, ∀ q ∈ (G).place w x, q ∈ T.1 := by
  obtain ⟨a, n, pre, post, hword⟩ := hw
  obtain ⟨b, x, hx⟩ := (G).contains_supertile_of_level (expansion_gt_one k hk).le T (2 + n)
  obtain ⟨s, hs⟩ := every_letter_in_square k hk a b
  have hsub := (G).shifted_supertile_subset hs n
  let y := x + (G).β ^ n * s
  have hall : ∀ q ∈ (G).place ((G).iterWord n a) y, q ∈ T.1 := by
    intro q hq
    have he := (G).place_add ((G).iterWord n a) 0 y
    rw [zero_add] at he
    rw [he] at hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    apply hx
    change (p.1, p.2 + y + -x) ∈ (G).supertile b (2 + n)
    apply hsub
    change (p.1, p.2 + y + -x + -((G).β ^ n * s)) ∈ (G).supertile a n
    rw [show p.2 + y + -x + -((G).β ^ n * s) = p.2 by dsimp [y]; ring]
    rcases p with ⟨p, u⟩
    rwa [(G).supertile_eq_place]
  refine ⟨y + (pre.map (G).ℓ).sum, fun q hq => hall q ?_⟩
  rw [← hword, List.append_assoc, place_append, place_append]
  exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hq)))

private theorem exists_forwardWord {w : List (Fin 3)} (hw : LegalWord k hk w) :
    ∃ B : Transversal k hk, forwardWord B w.length = w := by
  obtain ⟨T, _, h₀, _⟩ := Psc.ParameterFamilyTiling.fixed_hull_tiling k hk
  obtain ⟨x, hx⟩ := exists_placed_legalWord T hw
  cases w with
  | nil => exact ⟨reanchor T (1, 0) h₀, rfl⟩
  | cons a w =>
    have ha : (a, x) ∈ T.1 := hx _ (by simp [LengthSubst.place])
    refine ⟨reanchor T (a, x) ha, forwardWord_eq_of_placed _ _ ?_⟩
    intro q hq
    change (q.1, q.2 + x) ∈ T.1
    apply hx
    rw [← zero_add x, (G).place_add]
    exact List.mem_map.mpr ⟨q, hq, by simp⟩

theorem exists_itinerary (x : SymbolicHull k hk) :
    ∃ B : Transversal k hk, itinerary B = x.1 := by
  classical
  have he (n : ℕ) : ∃ B : Transversal k hk,
      block (itinerary B) 0 (2 * n + 1) = block x.1 (-(n : ℤ)) (2 * n + 1) := by
    obtain ⟨B, h⟩ := exists_forwardWord (x.2 (-(n : ℤ)) (2 * n + 1))
    have hlen : (block x.1 (-(n : ℤ)) (2 * n + 1)).length = 2 * n + 1 := by simp [block]
    rw [hlen, forwardWord_eq_block] at h
    exact ⟨B, h⟩
  choose B hB using he
  let seq := fun n : ℕ => itinerary ((H ^ (n : ℤ)) (B n))
  have hlim : Tendsto seq atTop (𝓝 x.1) := by
    apply tendsto_pi_nhds.mpr
    intro j
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ge_atTop j.natAbs] with n hn
    have hj₁ : -(n : ℤ) ≤ j := by omega
    have hj₂ : j ≤ (n : ℤ) := by omega
    let d := (j + (n : ℤ)).toNat
    have hd : (d : ℤ) = j + (n : ℤ) := Int.toNat_of_nonneg (by omega)
    have hdn : d < 2 * n + 1 := by omega
    have h := congrArg (fun w : List (Fin 3) => w[d]?) (hB n)
    rw [block_at _ _ hdn, block_at _ _ hdn, zero_add, hd] at h
    change itinerary ((H ^ (n : ℤ)) (B n)) j = x.1 j
    simpa only [itinerary_reindex, show -(n : ℤ) + (j + n) = j by ring] using Option.some.inj h
  have hclosed : IsClosed (range (itinerary (k := k) (hk := hk))) :=
    (isCompact_range continuous_itinerary).isClosed
  exact hclosed.mem_of_tendsto hlim (Eventually.of_forall fun n => mem_range_self _)

/-- The transversal and the literal two-sided word hull are homeomorphic. -/
noncomputable def itineraryHomeomorph : Transversal k hk ≃ₜ SymbolicHull k hk := by
  let f := fun B : Transversal k hk => (⟨itinerary B, itinerary_legal B⟩ : SymbolicHull k hk)
  have hf : Continuous f := continuous_itinerary.subtype_mk _
  let e := Equiv.ofBijective f
    ⟨fun _ _ h => itinerary_injective (congrArg Subtype.val h), fun x => by
      obtain ⟨B, h⟩ := exists_itinerary x
      exact ⟨B, Subtype.ext h⟩⟩
  exact e.toHomeomorphOfContinuousClosed hf hf.isClosedMap

/-- Left shift on legal bi-infinite words. -/
def shift (x : SymbolicHull k hk) : SymbolicHull k hk :=
  ⟨fun i => x.1 (i + 1), fun i n => by
    have he : block (fun j => x.1 (j + 1)) i n = block x.1 (i + 1) n := by
      unfold block
      congr 1
      funext j
      exact congrArg x.1 (add_right_comm i (j : ℕ) 1)
    rw [he]
    exact x.2 _ _⟩

theorem itineraryHomeomorph_next (B : Transversal k hk) :
    itineraryHomeomorph (next B) = shift (itineraryHomeomorph B) := by
  apply Subtype.ext
  exact funext (itinerary_next B)

theorem continuous_shift : Continuous (shift (k := k) (hk := hk)) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun i => (continuous_apply (i + 1)).comp continuous_subtype_val

end Psc.C4FamilySymbolicLanguage
