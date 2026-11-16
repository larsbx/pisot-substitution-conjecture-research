import PscVerif.OccurrenceMass

/-! Selected large subintervals of inflated strict overlaps. -/
namespace Psc.OccurrenceWidth

open Psc.OccurrenceNewborn Psc.OccurrenceTransport Psc.OccurrenceSuccessor
  Psc.OccurrenceFinite Psc.OccurrenceMass

/-- The displayed common interval supplies a lower bound on overlap mass. -/
theorem le_intervalMass_of_common (a b c d l m : ℝ)
    (ha : a ≤ l) (hc : c ≤ l) (hb : l+m ≤ b) (hd : l+m ≤ d) :
    m ≤ intervalMass a b c d := by
  have hlo : max a c ≤ l := max_le ha hc
  have hhi : l+m ≤ min b d := le_min hb hd
  exact (show m ≤ min b d - max a c by linarith).trans (le_max_right _ _)

/-- Bind the positioned intervals of two literal marks to an actual indexed
child. The lower bound makes the child strict. -/
theorem child_of_marks (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a) (p : Packet)
    (dt : Mark (s p.top)) (db : Mark (s p.bottom)) (m : ℝ) (hm : 0 < m)
    (h : m ≤ intervalMass (physicalLength ℓ dt.before)
      (physicalLength ℓ dt.before + ℓ dt.letter)
      (-β * offset ℓ p.delta + physicalLength ℓ db.before)
      (-β * offset ℓ p.delta + physicalLength ℓ db.before + ℓ db.letter)) :
    ∃ q, InteriorStep s ℓ p q ∧ m ≤ packetMass ℓ q := by
  let i := markIndex dt
  let j := markIndex db
  have hmass : m ≤ packetMass ℓ (digitPacket s p i j) := by
    rw [digitPacket_mass s ℓ β hscale]
    change m ≤ intervalMass (physicalLength ℓ ((s p.top).take dt.index))
      (physicalLength ℓ ((s p.top).take dt.index) + ℓ ((s p.top)[dt.index]'dt.index_lt))
      (-β * offset ℓ p.delta + physicalLength ℓ ((s p.bottom).take db.index))
      (-β * offset ℓ p.delta + physicalLength ℓ ((s p.bottom).take db.index) +
        ℓ ((s p.bottom)[db.index]'db.index_lt))
    rw [dt.take_index, db.take_index, dt.selected, db.selected]
    exact h
  exact ⟨_, ⟨digitPacket_digitStep s p i j,
    (packetMass_pos_iff_interior ℓ _).mp (hm.trans_le hmass)⟩, hmass⟩

private def nextMark {w : Word} (m : Mark w) (a : Fin 3) (tail : Word)
    (h : m.after = a :: tail) : Mark w where
  before := m.before ++ [m.letter]
  letter := a
  after := tail
  split := m.split.trans (by simp [h])

private theorem mark_length {w : Word} (ℓ : Fin 3 → ℝ) (m : Mark w) :
    physicalLength ℓ w = physicalLength ℓ m.before + ℓ m.letter + physicalLength ℓ m.after := by
  conv_lhs => rw [m.split]
  simp only [physicalLength_append, physicalLength_cons]
  ring

/-- Select two actual marks containing a point strictly between the given
left and right limits in the shared inflated interval. -/
private theorem marks_in_window (ℓ : Fin 3 → ℝ)
    (u v : Word) (S lo hi : ℝ)
    (hlo : max 0 S ≤ lo) (hhi : hi ≤ min (physicalLength ℓ u) (S + physicalLength ℓ v))
    (hwin : lo < hi) :
    ∃ (x : ℝ) (dt : Mark u) (db : Mark v), lo < x ∧ x < hi ∧
      physicalLength ℓ dt.before < x ∧ x < physicalLength ℓ dt.before + ℓ dt.letter ∧
      S + physicalLength ℓ db.before < x ∧ x < S + physicalLength ℓ db.before + ℓ db.letter := by
  classical
  let bot := (prefixCuts ℓ v).image (fun z => S+z)
  obtain ⟨x, hxlo, hxhi, hx⟩ := exists_between_avoiding (prefixCuts ℓ u ∪ bot) lo hi hwin
  have ht0 := (le_max_left 0 S).trans hlo
  have hb0 := (le_max_right 0 S).trans hlo
  have hu := hhi.trans (min_le_left _ _)
  have hv := hhi.trans (min_le_right _ _)
  have htcut : ∀ i ≤ u.length, x ≠ physicalLength ℓ (u.take i) := by
    intro i hi he
    exact hx (Finset.mem_union.mpr (Or.inl (he ▸ mem_prefixCuts ℓ u i hi)))
  have hbcut : ∀ i ≤ v.length, x-S ≠ physicalLength ℓ (v.take i) := by
    intro i hi he
    apply hx
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
      ⟨_, mem_prefixCuts ℓ v i hi, by linarith⟩))
  obtain ⟨dt, ht, ht'⟩ := exists_mark_containing ℓ u x (by linarith) (by linarith) htcut
  obtain ⟨db, hb, hb'⟩ := exists_mark_containing ℓ v (x-S) (by linarith) (by linarith) hbcut
  exact ⟨x, dt, db, hxlo, hxhi, ht, ht', by linarith, by linarith⟩

/-- Scaling gives the exact common mass of the two literal inflated words. -/
theorem inflated_mass (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a) (p : Packet) :
    intervalMass 0 (physicalLength ℓ (s p.top)) (-β*offset ℓ p.delta)
      (-β*offset ℓ p.delta + physicalLength ℓ (s p.bottom)) = β*packetMass ℓ p := by
  rw [hscale, hscale, packetMass]
  convert intervalMass_scale 0 (ℓ p.top) (-offset ℓ p.delta)
    (ℓ p.bottom-offset ℓ p.delta) β hβ using 1
  congr 1 <;> ring

/-- If the inflated overlap has width at least `3*m` with `0<m≤1/2`, a
single actual child has width at least `m`. All tile lengths are at least
one in this normalization. -/
theorem child_mass_at_least (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hunit : ∀ a, 1 ≤ ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a) (p : Packet)
    (m : ℝ) (hm : 0 < m) (hmh : m ≤ 1/2) (hwide : 3*m ≤ β * packetMass ℓ p) :
    ∃ q, InteriorStep s ℓ p q ∧ m ≤ packetMass ℓ q := by
  let S := -β * offset ℓ p.delta
  let lo := max 0 S
  let hi := min (physicalLength ℓ (s p.top)) (S+physicalLength ℓ (s p.bottom))
  have hlen : 3*m ≤ hi-lo := by
    rw [← inflated_mass s ℓ β hβ.le hscale p] at hwide
    change 3*m ≤ max 0 (hi-lo) at hwide
    exact (le_max_iff.mp hwide).resolve_left (by linarith)
  obtain ⟨x, dt, db, hxlo, hxhi, ht, ht', hb, hb'⟩ := marks_in_window ℓ
    (s p.top) (s p.bottom) S lo (lo+m)
    le_rfl (by change lo+m ≤ hi; linarith) (by linarith)
  let T := physicalLength ℓ dt.before
  let B := S + physicalLength ℓ db.before
  let T' := T + ℓ dt.letter
  let B' := B + ℓ db.letter
  change T < x at ht
  change x < T' at ht'
  change B < x at hb
  change x < B' at hb'
  by_cases hmass : m ≤ intervalMass T T' B B'
  · exact child_of_marks s ℓ β hscale p dt db m hm hmass
  have hsmall : min T' B' - max T B < m := (le_max_right _ _).trans_lt (lt_of_not_ge hmass)
  have hT : T+1 ≤ T' := by dsimp [T']; linarith [hunit dt.letter]
  have hB : B+1 ≤ B' := by dsimp [B']; linarith [hunit db.letter]
  by_cases hTB : T ≤ B
  · have hshort : T' - B < m := by
      rw [max_eq_right hTB] at hsmall
      rcases le_total T' B' with he | he
      · simpa only [min_eq_left he] using hsmall
      · rw [min_eq_right he] at hsmall
        linarith
    have hroom : T'+m ≤ physicalLength ℓ (s p.top) := by
      have hcap : hi ≤ physicalLength ℓ (s p.top) := min_le_left _ _
      linarith
    have hafter : dt.after ≠ [] := by
      intro hn
      have hh := mark_length ℓ dt
      rw [hn, physicalLength_nil] at hh
      change _ = T' + 0 at hh
      linarith
    obtain ⟨a, tail, ha⟩ := List.exists_cons_of_ne_nil hafter
    let dt' := nextMark dt a tail ha
    have hstart : physicalLength ℓ dt'.before = T' := by
      simp [dt', nextMark, T', T]
    apply child_of_marks s ℓ β hscale p dt' db m hm
    rw [hstart]
    exact le_intervalMass_of_common _ _ _ _ T' m le_rfl (by linarith)
      (by linarith [hunit dt'.letter]) (by change T'+m ≤ B'; linarith)
  · have hshort : B' - T < m := by
      rw [max_eq_left (le_of_not_ge hTB)] at hsmall
      rcases le_total T' B' with he | he
      · rw [min_eq_left he] at hsmall
        linarith
      · simpa only [min_eq_right he] using hsmall
    have hroom : B'+m ≤ S+physicalLength ℓ (s p.bottom) := by
      have hcap : hi ≤ S+physicalLength ℓ (s p.bottom) := min_le_right _ _
      linarith
    have hafter : db.after ≠ [] := by
      intro hn
      have hh := mark_length ℓ db
      rw [hn, physicalLength_nil] at hh
      have hh' : S+physicalLength ℓ (s p.bottom) = B' := by dsimp [B', B]; linarith
      linarith
    obtain ⟨a, tail, ha⟩ := List.exists_cons_of_ne_nil hafter
    let db' := nextMark db a tail ha
    have hstart : S+physicalLength ℓ db'.before = B' := by
      simp [db', nextMark, B', B, add_assoc]
    apply child_of_marks s ℓ β hscale p dt db' m hm
    change m ≤ intervalMass T T' (S+physicalLength ℓ db'.before)
      (S+physicalLength ℓ db'.before + ℓ db'.letter)
    rw [hstart]
    exact le_intervalMass_of_common _ _ _ _ B' m (by linarith) le_rfl
      (by linarith) (by linarith [hunit db'.letter])

/-- Every strict overlap reaches width at least half a tile under inflation
by a factor greater than three. -/
theorem reaches_half_mass (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hunit : ∀ a, 1 ≤ ℓ a) (hβ : 3 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a) (p : Packet) (hp : p.Interior ℓ) :
    ∃ q, Relation.ReflTransGen (InteriorStep s ℓ) p q ∧ 1/2 ≤ packetMass ℓ q := by
  by_contra! hno
  let δ := (β/3-1)*packetMass ℓ p
  have hw := (packetMass_pos_iff_interior ℓ p).mpr hp
  have hδ : 0 < δ := mul_pos (by linarith) hw
  have hiter (k : ℕ) : ∃ q, Relation.ReflTransGen (InteriorStep s ℓ) p q ∧
      packetMass ℓ p + (k : ℝ)*δ ≤ packetMass ℓ q := by
    induction k with
    | zero => exact ⟨p, .refl, by simp⟩
    | succ k ih =>
      obtain ⟨q, hpath, hsize⟩ := ih
      have hmono : packetMass ℓ p ≤ packetMass ℓ q := by
        linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hδ.le]
      have hsmall : β*packetMass ℓ q < 3*(1/2) := by
        by_contra! hb
        obtain ⟨r, he, hm⟩ := child_mass_at_least s ℓ β hunit (by linarith) hscale q
          (1/2) (by norm_num) le_rfl hb
        exact (not_lt_of_ge hm) (hno r (hpath.tail he))
      let m := β*packetMass ℓ q/3
      have hm : 0 < m := div_pos (mul_pos (by linarith) (hw.trans_le hmono)) (by norm_num)
      obtain ⟨r, hr, hmr⟩ := child_mass_at_least s ℓ β hunit (by linarith) hscale q
        m hm (by dsimp [m]; linarith) (by dsimp [m]; linarith)
      have hg : δ ≤ (β/3-1)*packetMass ℓ q :=
        mul_le_mul_of_nonneg_left hmono (by linarith)
      refine ⟨r, hpath.tail hr, ?_⟩
      push_cast
      dsimp [m] at hmr
      linarith
  obtain ⟨k, hk⟩ := exists_nat_gt ((1/2 - packetMass ℓ p)/δ)
  obtain ⟨q, hq, hsize⟩ := hiter k
  have hlt := (div_lt_iff₀ hδ).mp hk
  linarith [hno q hq]

end Psc.OccurrenceWidth
