/-
# Literal third-level entry for the BH run families

The source gate is `docs/bh-third-level-and-diagonal-stop-go-2026-11-24.md`.
The construction follows `docs/bh-third-level-windows-2026-11-24.md`.
All selected letters below are actual marks in the original words.
-/
import PscVerif.BHDiagonalLiteral
import PscVerif.OccurrenceWidth
import PscVerif.OccurrenceAncestry
import PscVerif.OccurrenceInverse
import PscVerif.ClassAMinusPrefixAssembly
import PscVerif.BHThirdLevelGeometry
import PscVerif.BHThirdLevelTransport

namespace Psc.BHThirdLevelEntry

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn Psc.OccurrenceTransport
open Psc.OccurrenceSuccessor Psc.OccurrenceMass Psc.OccurrenceWidth
open Psc.OccurrenceAncestry Psc.OccurrenceInverse Psc.OccurrenceFinite
open Psc.BHNearDiagonalLiteral Psc.ClassAMinusPrefixAssembly Matrix

theorem physical_replicate (ℓ : Fin 3 → ℝ) (n : ℕ) (a : Fin 3) :
    physicalLength ℓ (List.replicate n a) = n * ℓ a := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, Nat.cast_succ, add_mul, add_comm]

/-- The exact length scaling uses no off-diagonal energy hypothesis. -/
theorem run_lengths_scale {r k : ℕ} {β : ℝ} (h : RunFamily r k β) (a : Fin 3) :
    physicalLength (lengths r β) (sigma r k a) = β * lengths r β a := by
  have hb : (r : ℝ) / β * β = r := div_mul_cancel₀ _ h.beta_pos.ne'
  fin_cases a
  · simp [sigma, lengths]
  · simp [sigma, lengths, physical_replicate]
    nlinarith only [h.quadratic_eq]
  · simp [sigma, lengths, physical_replicate]
    nlinarith only [hb]

theorem physical_subst (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a) (w : Word) :
    physicalLength ℓ (subst s w) = β * physicalLength ℓ w := by
  induction w with
  | nil => simp [subst]
  | cons a w ih =>
    simp only [subst_cons, physicalLength_append, physicalLength_cons, hscale, ih]
    ring

/-- Every strict full packet reaches an actual overlap of width at least
one half. This applies to the diagonal and both adjacent bands. -/
theorem run_reaches_half_mass {r k : ℕ} {β : ℝ} (h : RunFamily r k β)
    (hlarge : 3 < β) (p : Packet) (hp : p.Interior (lengths r β)) :
    ∃ q, Relation.ReflTransGen (InteriorStep (sigma r k) (lengths r β)) p q ∧
      (1 / 2 : ℝ) ≤ packetMass (lengths r β) q :=
  reaches_half_mass (sigma r k) (lengths r β) β h.lengths_ge_one hlarge
    (run_lengths_scale h) p hp

/-- Half-open containment retains a concrete occurrence even at a cut. -/
theorem mark_containing_halfopen (ℓ : Fin 3 → ℝ) (w : Word) (x : ℝ)
    (hx : 0 ≤ x) (hend : x < physicalLength ℓ w) :
    ∃ m : Mark w, physicalLength ℓ m.before ≤ x ∧
      x < physicalLength ℓ m.before + ℓ m.letter := by
  induction w generalizing x with
  | nil => simp at hend; linarith
  | cons a w ih =>
    by_cases hfirst : x < ℓ a
    · exact ⟨⟨[], a, w, rfl⟩, by simpa using hx, by simpa using hfirst⟩
    · have hrest : x - ℓ a < physicalLength ℓ w := by
        simp only [physicalLength_cons] at hend
        linarith
      obtain ⟨m, hm, hm'⟩ := ih (x - ℓ a) (by linarith) hrest
      let lifted : Mark (a :: w) :=
        ⟨a :: m.before, m.letter, m.after, by simpa using congrArg (List.cons a) m.split⟩
      refine ⟨lifted, ?_, ?_⟩
      · simp only [lifted, physicalLength_cons]
        linarith
      · simp only [lifted, physicalLength_cons]
        linarith

theorem last_mark_unique (u : Word) (a : Fin 3) (ha : a ∉ u)
    (m : Mark (u ++ [a])) (hm : m.letter = a) :
    m.before = u ∧ m.after = [] := by
  let last : Mark (u ++ [a]) := ⟨u, a, [], rfl⟩
  have hindex : m.index = u.length := by
    have hnot : ¬m.index < u.length := by
      intro hi
      have hs : u[m.index]'hi = a := by
        rw [List.getElem_append_left' hi [a], m.selected, hm]
      exact ha (List.mem_of_getElem hs)
    have hi := m.index_lt
    simp only [List.length_append, List.length_singleton] at hi
    omega
  have he : m = last := mark_eq_of_index _ _ hindex
  exact ⟨congrArg Mark.before he, congrArg Mark.after he⟩

/-- The only letter 2 in any image is the final letter of the image of 1;
its complete literal prefix, rather than only its position, is recovered. -/
theorem two_digit_structure (r k : ℕ) (a : Fin 3) (m : Mark (sigma r k a))
    (hm : m.letter = 2) :
    a = 1 ∧ m.before = 0 :: List.replicate k 1 ∧ m.after = [] := by
  have hmem : (2 : Fin 3) ∈ sigma r k a := by
    rw [m.split, ← hm]
    simp
  have ha : a = 1 := by
    fin_cases a <;> simp [sigma] at hmem ⊢
  subst a
  refine ⟨rfl, ?_⟩
  exact last_mark_unique (0 :: List.replicate k 1) 2 (by simp)
    (show Mark ((0 :: List.replicate k 1) ++ [2]) from m) hm

/-- Every type-2 mark in an inflated word has its actual parent-1 mark
and the exact physical start inherited from the common final prefix. -/
theorem two_mark_parent {r k : ℕ} {β : ℝ} (h : RunFamily r k β) (w : Word)
    (m : Mark (subst (sigma r k) w)) (hm : m.letter = 2) :
    ∃ p : Mark w, p.letter = 1 ∧
      physicalLength (lengths r β) m.before =
        β * physicalLength (lengths r β) p.before + (1 + (k : ℝ) * β) ∧
      m.before = subst (sigma r k) p.before ++ (0 :: List.replicate k 1) := by
  obtain ⟨p, d, rfl⟩ := mark_uninflate (sigma r k) w m
  have hd : d.letter = 2 := hm
  obtain ⟨hp, hdpre, _⟩ := two_digit_structure r k p.letter d hd
  refine ⟨p, hp, ?_, ?_⟩
  · simp only [Mark.inflate, physicalLength_append, physical_subst _ _ β
      (run_lengths_scale h), hdpre]
    simp [physical_replicate, lengths]
  · exact congrArg (fun u => subst (sigma r k) p.before ++ u) hdpre

/-- Distinct type-2 marks in a once-inflated word are separated by β².
The proof traces them to distinct original parent-1 occurrences. -/
theorem two_mark_separation {r k : ℕ} {β : ℝ} (h : RunFamily r k β) (w : Word)
    (m n : Mark (subst (sigma r k) w)) (hm : m.letter = 2) (hn : n.letter = 2)
    (hne : m ≠ n) :
    β ^ 2 ≤ |physicalLength (lengths r β) m.before -
      physicalLength (lengths r β) n.before| := by
  obtain ⟨p, hp, hmp, hmword⟩ := two_mark_parent h w m hm
  obtain ⟨q, hq, hnq, hnword⟩ := two_mark_parent h w n hn
  have hpq : p.index ≠ q.index := by
    intro hi
    have he : p = q := mark_eq_of_index _ _ hi
    subst q
    apply hne
    apply mark_eq_of_index
    simp only [Mark.index, hmword, hnword]
  have hpos := h.beta_pos
  have hnonneg : ∀ a, 0 ≤ lengths r β a := fun a => (by linarith [h.lengths_ge_one a])
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · have hsep := mark_end_le_start (lengths r β) hnonneg p q hlt
    rw [hp] at hsep
    change physicalLength (lengths r β) p.before + β ≤
      physicalLength (lengths r β) q.before at hsep
    have hd : β ^ 2 ≤ physicalLength (lengths r β) n.before -
        physicalLength (lengths r β) m.before := by nlinarith [hmp, hnq]
    rw [abs_sub_comm]
    exact hd.trans (le_abs_self _)
  · have hsep := mark_end_le_start (lengths r β) hnonneg q p hgt
    rw [hq] at hsep
    change physicalLength (lengths r β) q.before + β ≤
      physicalLength (lengths r β) p.before at hsep
    have hd : β ^ 2 ≤ physicalLength (lengths r β) m.before -
        physicalLength (lengths r β) n.before := by nlinarith [hmp, hnq]
    exact hd.trans (le_abs_self _)

/-- Starts of the images of actual type-2 parent marks, including the
external origin of this track. -/
def badStarts (r _k : ℕ) (β origin : ℝ) (w : Word) : Set ℝ :=
  {b | ∃ m : Mark w, m.letter = 2 ∧
    b = origin + β * physicalLength (lengths r β) m.before}

theorem badStarts_separated {r k : ℕ} {β : ℝ} (h : RunFamily r k β)
    (origin : ℝ) (w : Word) :
    ∀ b ∈ badStarts r k β origin (subst (sigma r k) w),
    ∀ c ∈ badStarts r k β origin (subst (sigma r k) w),
      b ≠ c → β ^ 3 ≤ |b - c| := by
  rintro b ⟨m, hm, rfl⟩ c ⟨n, hn, rfl⟩ hne
  have hmn : m ≠ n := by intro he; subst n; exact hne rfl
  have hsep := two_mark_separation h w m n hm hn hmn
  have he : origin + β * physicalLength (lengths r β) m.before -
      (origin + β * physicalLength (lengths r β) n.before) =
      β * (physicalLength (lengths r β) m.before -
        physicalLength (lengths r β) n.before) := by ring
  rw [he, abs_mul, abs_of_pos h.beta_pos]
  calc
    β ^ 3 = β * β ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsep h.beta_pos.le

theorem mark_letter_mem {w : Word} (m : Mark w) : m.letter ∈ w := by
  exact List.mem_of_getElem m.selected

/-- Each non-obstructing image starts with a type-1 tile after distance
zero or one; the actual ordinal is carried by the returned mark. -/
theorem first_one_digit (r k : ℕ) (hk : 0 < k) (β : ℝ) (a : Fin 3) (ha : a ≠ 2) :
    ∃ d : Mark (sigma r k a), d.letter = 1 ∧
      (physicalLength (lengths r β) d.before = 0 ∨
       physicalLength (lengths r β) d.before = 1) := by
  fin_cases a
  · exact ⟨⟨[], 1, [], by simp [sigma]⟩, rfl, Or.inl (by simp)⟩
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    refine ⟨⟨[0], 1, List.replicate n 1 ++ [2], ?_⟩, rfl, Or.inr ?_⟩
    · simp [sigma, List.replicate_succ]
    · simp [lengths]
  · exact False.elim (ha rfl)

def next_parent {w : Word} (m : Mark w) (a : Fin 3) (tail : Word)
    (h : m.after = a :: tail) : Mark w where
  before := m.before ++ [m.letter]
  letter := a
  after := tail
  split := m.split.trans (by simp [h])

theorem mark_word_length (ℓ : Fin 3 → ℝ) {w : Word} (m : Mark w) :
    physicalLength ℓ w = physicalLength ℓ m.before + ℓ m.letter +
      physicalLength ℓ m.after := by
  conv_lhs => rw [m.split]
  simp only [physicalLength_append, physicalLength_cons]
  ring

theorem inflate_start {r k : ℕ} {β : ℝ} (h : RunFamily r k β)
    (origin : ℝ) {w : Word} (m : Mark w) (d : Mark (sigma r k m.letter)) :
    origin + physicalLength (lengths r β) (m.inflate (sigma r k) d).before =
      origin + β * physicalLength (lengths r β) m.before +
        physicalLength (lengths r β) d.before := by
  simp only [Mark.inflate, physicalLength_append,
    physical_subst _ _ β (run_lengths_scale h)]
  ring

/-- An interior point of a clean window has an actual type-1 tile whose
start is at most three units to its right and whose end is to its right.
The final-2 case explicitly crosses into the next original parent mark. -/
theorem clean_window_locator {r k : ℕ} {β : ℝ} (h : RunFamily r k β)
    (hβ : 3 < β) (hr : (r : ℝ) < β) (w : Word) (origin a x : ℝ)
    (hleft : origin ≤ x)
    (hright : x + 3 < origin + physicalLength (lengths r β) (subst (sigma r k) w))
    (hxa : a ≤ x) (hxb : x + 3 < a + 4 * β)
    (hclean : ∀ b ∈ badStarts r k β origin w,
      b + 2 * β ≤ a ∨ a + 4 * β ≤ b) :
    ∃ d : Mark (subst (sigma r k) w), d.letter = 1 ∧
      origin + physicalLength (lengths r β) d.before ≤ x + 3 ∧
      x ≤ origin + physicalLength (lengths r β) d.before + β := by
  have hpos := h.beta_pos
  have hroot : (x-origin)/β < physicalLength (lengths r β) w := by
    apply (div_lt_iff₀ hpos).mpr
    rw [physical_subst _ _ β (run_lengths_scale h)] at hright
    nlinarith
  obtain ⟨m, hmlo, hmhi⟩ := mark_containing_halfopen (lengths r β) w
    ((x-origin)/β) (div_nonneg (sub_nonneg.mpr hleft) hpos.le) hroot
  let B := origin + β * physicalLength (lengths r β) m.before
  have hlo : B ≤ x := by
    have hh := (le_div_iff₀ hpos).mp hmlo
    dsimp [B]
    nlinarith
  have hhi : x < B + β * lengths r β m.letter := by
    have hh := (div_lt_iff₀ hpos).mp hmhi
    dsimp [B]
    nlinarith
  have htwo : β * lengths r β 2 < 2 * β := by
    change β * (1 + r / β) < 2 * β
    have he := div_mul_cancel₀ (r : ℝ) hpos.ne'
    nlinarith
  have hmnot : m.letter ≠ 2 := by
    intro he
    have hb : B ∈ badStarts r k β origin w := ⟨m, he, rfl⟩
    rcases hclean B hb with hb | hb
    · rw [he] at hhi
      linarith
    · linarith
  rcases (show m.letter = 0 ∨ m.letter = 1 from by omega) with hm0 | hm1
  · let d : Mark (sigma r k m.letter) := ⟨[], 1, [], by simp [sigma, hm0]⟩
    refine ⟨m.inflate (sigma r k) d, rfl, ?_, ?_⟩
    · rw [inflate_start h]
      simp only [d, physicalLength_nil, add_zero]
      linarith
    · rw [inflate_start h]
      simp only [d, physicalLength_nil, add_zero]
      rw [hm0] at hhi
      change x < B + β * 1 at hhi
      dsimp [B] at hhi
      linarith
  · by_cases hrunend : x < B + 1 + (k : ℝ) * β
    · by_cases hrunstart : B + 1 ≤ x
      · have hh : x-B-1 < physicalLength (lengths r β) (List.replicate k 1) := by
          rw [physical_replicate]
          change x-B-1 < (k : ℝ) * β
          linarith
        obtain ⟨v, hvlo, hvhi⟩ := mark_containing_halfopen (lengths r β)
          (List.replicate k 1) (x-B-1) (by linarith) hh
        have hv : v.letter = 1 := (List.mem_replicate.mp (mark_letter_mem v)).2
        let d : Mark (sigma r k m.letter) :=
          ⟨0 :: v.before, v.letter, v.after ++ [2], by
            rw [hm1]
            simp only [sigma, Matrix.cons_val_one, Matrix.cons_val_zero]
            change 0 :: (List.replicate k 1 ++ [2]) =
              0 :: (v.before ++ v.letter :: (v.after ++ [2]))
            apply congrArg (List.cons 0)
            calc
              List.replicate k 1 ++ [2] = (v.before ++ v.letter :: v.after) ++ [2] :=
                congrArg (fun t : Word => t ++ [2]) v.split
              _ = v.before ++ ((v.letter :: v.after) ++ [2]) := List.append_assoc _ _ _
              _ = v.before ++ v.letter :: (v.after ++ [2]) := by rw [List.cons_append]⟩
        refine ⟨m.inflate (sigma r k) d, hv, ?_, ?_⟩
        · rw [inflate_start h]
          simp only [d, physicalLength_cons]
          change origin + β * physicalLength (lengths r β) m.before +
            (1 + physicalLength (lengths r β) v.before) ≤ x + 3
          dsimp [B] at hvlo
          linarith
        · rw [inflate_start h]
          simp only [d, physicalLength_cons]
          change x ≤ origin + β * physicalLength (lengths r β) m.before +
            (1 + physicalLength (lengths r β) v.before) + β
          rw [hv] at hvhi
          change x - B - 1 < physicalLength (lengths r β) v.before + β at hvhi
          dsimp [B] at hvhi
          linarith
      · obtain ⟨d, hd, hpre⟩ := first_one_digit r k h.run_pos β m.letter hmnot
        refine ⟨m.inflate (sigma r k) d, hd, ?_, ?_⟩
        · rw [inflate_start h]
          rcases hpre with he | he <;> rw [he] <;> change B + _ ≤ x + 3 <;> linarith
        · rw [inflate_start h]
          rcases hpre with he | he <;> rw [he] <;> change x ≤ B + _ + β <;> linarith
    · let E := B + β * lengths r β m.letter
      have hEx : x < E := hhi
      have hEsmall : E < x + 2 := by
        dsimp [E]
        rw [hm1]
        change B + β * β < x + 2
        have hdiv : (r : ℝ)/β < 1 := (div_lt_one hpos).mpr hr
        nlinarith [h.quadratic_eq]
      have hafter : m.after ≠ [] := by
        intro he
        have htotal := mark_word_length (lengths r β) m
        rw [he, physicalLength_nil, add_zero] at htotal
        rw [physical_subst _ _ β (run_lengths_scale h), htotal] at hright
        dsimp [E, B] at hEsmall
        nlinarith
      obtain ⟨next, tail, htail⟩ := List.exists_cons_of_ne_nil hafter
      let q := next_parent m next tail htail
      have hqstart : origin + β * physicalLength (lengths r β) q.before = E := by
        simp only [q, next_parent, physicalLength_append, physicalLength_singleton]
        dsimp [E, B]
        ring
      have hqnot : q.letter ≠ 2 := by
        intro he
        have hbad : E ∈ badStarts r k β origin w := ⟨q, he, hqstart.symm⟩
        rcases hclean E hbad with hc | hc <;> linarith
      obtain ⟨d, hd, hpre⟩ := first_one_digit r k h.run_pos β q.letter hqnot
      refine ⟨q.inflate (sigma r k) d, hd, ?_, ?_⟩
      · rw [inflate_start h, hqstart]
        rcases hpre with he | he <;> rw [he] <;> linarith
      · rw [inflate_start h, hqstart]
        rcases hpre with he | he <;> rw [he] <;> linarith

theorem image_three (s : Fin 3 → Word) (a : Fin 3) :
    image s 3 a = subst s (subst s (subst s [a])) := by
  simp [image, Function.iterate_succ_apply']

/-- The shared clean window selects actual type-1 marks on both third-level
tracks. The bottom origin S is retained in the resulting distance bound. -/
theorem third_level_marks {r k : ℕ} {β : ℝ} (h : RunFamily r k β)
    (hβ : 12 < β) (hr : (r : ℝ) < β) (p : Packet) (S L : ℝ)
    (htlo : 0 ≤ L) (hblo : S ≤ L)
    (hthi : L + 18 * β ≤ physicalLength (lengths r β) (image (sigma r k) 3 p.top))
    (hbhi : L + 18 * β ≤ S + physicalLength (lengths r β) (image (sigma r k) 3 p.bottom)) :
    ∃ (top : Mark (image (sigma r k) 3 p.top))
      (bottom : Mark (image (sigma r k) 3 p.bottom)),
      top.letter = 1 ∧ bottom.letter = 1 ∧
      |(S + physicalLength (lengths r β) bottom.before) -
        physicalLength (lengths r β) top.before| ≤ 3 * β / 4 := by
  let u := subst (sigma r k) (subst (sigma r k) [p.top])
  let v := subst (sigma r k) (subst (sigma r k) [p.bottom])
  obtain ⟨a, hLa, haL, hct, hcb⟩ := BHThirdLevelGeometry.exists_clean_window β L
    (badStarts r k β 0 u) (badStarts r k β S v) hβ
    (badStarts_separated h 0 (subst (sigma r k) [p.top]))
    (badStarts_separated h S (subst (sigma r k) [p.bottom]))
  have htend : a + 4 * β ≤ physicalLength (lengths r β) (subst (sigma r k) u) := by
    have he := haL.trans hthi
    simpa only [image_three, u] using he
  have hbend : a + 4 * β ≤ S + physicalLength (lengths r β) (subst (sigma r k) v) := by
    have he := haL.trans hbhi
    simpa only [image_three, v] using he
  obtain ⟨dt, hdt, hdtlo, hdthi⟩ := clean_window_locator h (by linarith) hr u 0 a
    (a + 3 * β / 2) (by linarith) (by linarith) (by linarith) (by linarith) hct
  simp only [zero_add] at hdtlo hdthi
  let c := physicalLength (lengths r β) dt.before
  have hc0 : a + β / 2 ≤ c := by dsimp [c]; linarith
  have hc1 : c ≤ a + 3 * β / 2 + 3 := hdtlo
  obtain ⟨db, hdb, hdblo, hdbhi⟩ := clean_window_locator h (by linarith) hr v S a
    (c + β / 2) (by linarith) (by linarith) (by linarith) (by linarith) hcb
  let top : Mark (image (sigma r k) 3 p.top) :=
    ⟨dt.before, dt.letter, dt.after, by rw [image_three]; exact dt.split⟩
  let bottom : Mark (image (sigma r k) 3 p.bottom) :=
    ⟨db.before, db.letter, db.after, by rw [image_three]; exact db.split⟩
  refine ⟨top, bottom, hdt, hdb, ?_⟩
  change |(S + physicalLength (lengths r β) db.before) - c| ≤ 3 * β / 4
  apply abs_le.mpr
  constructor <;> linarith

/-- A half-unit source overlap enters the run window in exactly three
original-occurrence steps, with the entire integral displacement retained. -/
theorem half_mass_entry {r k : ℕ} {β : ℝ} (h : RunFamily r k β)
    (hβ : 12 < β) (hrβ : (r : ℝ) < β) (hwindow : 3 * β / 4 < (k : ℝ) - 1)
    (p : Packet) (hmass : (1 / 2 : ℝ) ≤ packetMass (lengths r β) p) :
    ∃ (q : Packet) (xs : List (ℕ × ℕ)), xs.length = 3 ∧
      OrderedInteriorPath (sigma r k) (lengths r β) p xs q ∧ Central r k β q := by
  let S : ℝ := -β ^ 3 * offset (lengths r β) p.delta
  let L : ℝ := max 0 S
  obtain ⟨htlo, hblo, hthi, hbhi⟩ := BHThirdLevelTransport.half_mass_common_interval
    h (run_lengths_scale h) hβ p hmass
  obtain ⟨top, bottom, htop, hbottom, hbound⟩ := third_level_marks h hβ hrβ p S L
    htlo hblo hthi hbhi
  obtain ⟨xs, hlen, hpath, hcentral⟩ := BHThirdLevelTransport.positioned_run_marks h
    (run_lengths_scale h) p 3 top bottom htop hbottom (hbound.trans hwindow.le)
  exact ⟨assembledPacket (sigma r k) p 3 top bottom, xs, hlen, hpath, hcentral⟩

/-- Every strict source packet, with arbitrary labels and all three
integral displacement coordinates, reaches the type-1/type-1 run window.
The hypotheses are elementary coefficient bounds, not an entry predicate. -/
theorem run_family_entry {r k : ℕ} {β : ℝ} (h : RunFamily r k β)
    (hβ : 12 < β) (hrβ : (r : ℝ) < β) (hwindow : 3 * β / 4 < (k : ℝ) - 1)
    (p : Packet) (hp : p.Interior (lengths r β)) :
    ∃ q, Relation.ReflTransGen (InteriorStep (sigma r k) (lengths r β)) p q ∧
      Central r k β q := by
  obtain ⟨middle, hfirst, hmass⟩ := run_reaches_half_mass h (by linarith) p hp
  obtain ⟨q, xs, _, hlast, hc⟩ := half_mass_entry h hβ hrβ hwindow middle hmass
  exact ⟨q, hfirst.trans hlast.interiorPath, hc⟩

/-- Every strict path can retain its actual ordered local occurrence
indices without changing any packet or intermediate strictness witness. -/
theorem interior_path_ordered (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    {p q : Packet} (hp : p.Interior ℓ)
    (hpath : Relation.ReflTransGen (InteriorStep s ℓ) p q) :
    ∃ xs : List (ℕ × ℕ), OrderedInteriorPath s ℓ p xs q := by
  induction hpath with
  | refl => exact ⟨[], .nil p hp⟩
  | tail _ hedge ih =>
    obtain ⟨xs, hx⟩ := ih
    obtain ⟨hdigit, hi⟩ := hedge
    obtain ⟨dt, db, hq⟩ := hdigit
    refine ⟨xs ++ [(dt.index, db.index)], .snoc hx dt.index db.index ?_ hi⟩
    exact ⟨dt, db, rfl, rfl, hq⟩

/-- Ordered form of the unrestricted strict-source entry theorem. The
same endpoint and full ordinal transcript are available to literal prefix
assembly; no projection or independently chosen endpoint is substituted. -/
theorem run_family_entry_ordered {r k : ℕ} {β : ℝ} (h : RunFamily r k β)
    (hβ : 12 < β) (hrβ : (r : ℝ) < β) (hwindow : 3 * β / 4 < (k : ℝ) - 1)
    (p : Packet) (hp : p.Interior (lengths r β)) :
    ∃ (q : Packet) (xs : List (ℕ × ℕ)),
      OrderedInteriorPath (sigma r k) (lengths r β) p xs q ∧ Central r k β q := by
  obtain ⟨q, hpath, hc⟩ := run_family_entry h hβ hrβ hwindow p hp
  obtain ⟨xs, hx⟩ := interior_path_ordered (sigma r k) (lengths r β) hp hpath
  exact ⟨q, xs, hx, hc⟩

end Psc.BHThirdLevelEntry
