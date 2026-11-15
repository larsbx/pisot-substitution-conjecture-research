import PscVerif.ClassAZeroDefectEscape

/-! Selected literal RUN/RUN descent for the central `y/y` domain of minus Class A.
See `docs/bh-class-a-run-descent-2026-11-14.md` for the exact parameter scope. -/
namespace Psc.ClassARunDescent

open Psc.Incidence Psc.OccurrenceNewborn Psc.OccurrenceTransport Psc.OccurrenceSuccessor
  Psc.ClassAZeroDefectEscape Matrix

/-- Bottom-minus-top coordinates `(p,q,b-2*p-q)`, where `b = p+S`. -/
def yyPacket (p b q : ℤ) : Packet := packet 2 2 p q (b-2*p-q)

def lengths (α h : ℝ) : Fin 3 → ℝ := ![2+α-h, 1+h, 1]

def shift (α h : ℝ) (p b q : ℤ) : ℝ := b + (α-h)*p + h*q

def radius (p b : ℤ) : ℕ := max p.natAbs b.natAbs

private theorem cast_natAbs (z : ℤ) : (z.natAbs : ℝ) = |(z : ℝ)| := by
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]

private theorem exists_round_of_nonneg (c R : ℝ) (hc : 0 ≤ c) (hR : 1/2 ≤ R) (hR1 : R ≤ 1) :
    ∃ z : ℤ, |(z : ℝ)-c| ≤ R ∧ |(z : ℝ)| ≤ |c| + (1-R) := by
  let f := Int.floor c
  have hf : (f : ℝ) ≤ c := Int.floor_le c
  have hf' : c < (f : ℝ) + 1 := by
    exact_mod_cast Int.lt_succ_floor c
  have hf0 : 0 ≤ (f : ℝ) := by exact_mod_cast (Int.floor_nonneg.mpr hc)
  by_cases hnear : c-(f : ℝ) ≤ R
  · refine ⟨f, ?_, ?_⟩
    · exact abs_le.mpr ⟨by linarith, by linarith⟩
    · rw [abs_of_nonneg hf0, abs_of_nonneg hc]
      linarith
  · refine ⟨f+1, ?_, ?_⟩
    · push_cast
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · push_cast
      rw [abs_of_nonneg (by linarith : 0 ≤ (f : ℝ)+1), abs_of_nonneg hc]
      linarith

private theorem exists_round (c R : ℝ) (hR : 1/2 ≤ R) (hR1 : R ≤ 1) :
    ∃ z : ℤ, |(z : ℝ)-c| ≤ R ∧ |(z : ℝ)| ≤ |c| + (1-R) := by
  by_cases hc : 0 ≤ c
  · exact exists_round_of_nonneg c R hc hR hR1
  · obtain ⟨z, hd, hz⟩ := exists_round_of_nonneg (-c) R (by linarith) hR hR1
    refine ⟨-z, ?_, ?_⟩
    · push_cast
      rw [show -(z : ℝ)-c = -((z : ℝ)-(-c)) by ring, abs_neg]
      exact hd
    · simpa only [Int.cast_neg, abs_neg] using hz

private theorem offset_yy (α h : ℝ) (p b q : ℤ) :
    offset (lengths α h) (yyPacket p b q).delta = -shift α h p b q := by
  simp [offset, dotProduct, Fin.sum_univ_three, yyPacket, packet, lengths, shift]
  ring

private theorem interior_of_abs_shift_lt_one {α h : ℝ} (hpos : ∀ a, 0 < lengths α h a)
    {p b q : ℤ} (hs : |shift α h p b q| < 1) : (yyPacket p b q).Interior (lengths α h) := by
  apply (Packet.interior_iff_bounds _ hpos _).mpr
  rw [offset_yy]
  change -1 < -shift α h p b q ∧ -shift α h p b q < 1
  exact abs_lt.mp (by rwa [abs_neg] : |(-shift α h p b q)| < 1)

/-- Every chosen integer `b'` respecting the next strict strip produces a
literal ordered RUN/RUN edge when the inflated parent shift is in the
closed run-gap interval. -/
theorem run_to (n d : ℕ) (hn : 2 ≤ n)
    (α h β : ℝ) (hpos : ∀ a, 0 < lengths α h a)
    (hβn : β = (n : ℝ)+2+α) (hβh : β*h = 1)
    (hβa : β*α = (d : ℝ)-n+1-2*h) (p b q b' : ℤ)
    (hstart : |β * shift α h p b q| ≤ (n : ℝ)-2)
    (hnext : |shift α h b b' (b-2*p)| < 1) :
    ∃ i j : ℕ, 1 ≤ i ∧ i < n ∧ 1 ≤ j ∧ j < n ∧
      IndexedInteriorStep (sigma n d) (lengths α h) (yyPacket p b q) i j
        (yyPacket b b' (b-2*p)) := by
  let g : ℤ := ((d : ℤ)-n)*p + ((n : ℤ)+2)*b + q - b'
  have hg : (g : ℝ) = β * shift α h p b q - shift α h b b' (b-2*p) := by
    dsimp [g, shift]
    push_cast
    linear_combination -p * hβa + (p-q) * hβh - b * hβn
  have hgabs : |(g : ℝ)| < (n : ℝ)-1 := by
    rw [hg]
    have hu := abs_sub (β*shift α h p b q) (shift α h b b' (b-2*p))
    linarith
  have hn1 : 1 ≤ n := by omega
  have hgn : |g| < ((n : ℤ)-1) := by exact_mod_cast hgabs
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hgn
  have hi : g.toNat < runLength n d 2 := by simp [runLength]; omega
  have hj : (-g).toNat < runLength n d 2 := by simp [runLength]; omega
  have hgap : ((g.toNat : ℕ) : ℤ) - ((-g).toNat : ℤ) = g := by omega
  have hd := positive_step n d hn1 2 2 g.toNat (-g).toNat hi.le hj.le
    p q (b-2*p-q)
  have hp : 2*p+q+(b-2*p-q)-delta 2 2 = b := by simp [delta]
  have hq : q+(b-2*p-q)+delta 2 2 = b-2*p := by simp [delta]
  have hr : (((n+d : ℕ) : ℤ)*p+(n : ℤ)*q+((n-1 : ℕ) : ℤ)*(b-2*p-q)+
      ((-g).toNat : ℤ)-g.toNat) = b'-2*b-(b-2*p) := by
    simp only [Nat.cast_add, Nat.cast_sub hn1, Nat.cast_one]
    dsimp [g] at hgap
    linear_combination -hgap
  refine ⟨g.toNat+1, (-g).toNat+1, by omega, ?_, by omega, ?_, ?_⟩
  · simp [runLength] at hi
    omega
  · simp [runLength] at hj
    omega
  · refine ⟨?_, interior_of_abs_shift_lt_one hpos hnext⟩
    simpa only [yyPacket, positiveMark_letter_of_lt n d 2 g.toNat hi,
      positiveMark_letter_of_lt n d 2 (-g).toNat hj, hp, hq, hr] using hd

/-- Rounding gives a legal strict RUN/RUN successor and its quantitative
bound on the new integer slot. -/
theorem rounded_run_step (n d : ℕ) (hn : 2 ≤ n) (α h β R : ℝ)
    (hpos : ∀ a, 0 < lengths α h a) (ha : 0 ≤ α) (hh : 0 ≤ h) (hβ : 0 < β)
    (hβn : β = (n : ℝ)+2+α) (hβh : β*h = 1) (hβa : β*α = (d : ℝ)-n+1-2*h)
    (hR : 1/2 ≤ R) (hR1 : R < 1) (hβR : β*R = (n : ℝ)-2)
    (p b q : ℤ) (hstart : |shift α h p b q| ≤ R) :
    ∃ b' : ℤ, (b'.natAbs : ℝ) ≤ (α+2*h)*(radius p b : ℝ)+1-R ∧ |shift α h b b' (b-2*p)| ≤ R ∧
      ∃ i j : ℕ, 1 ≤ i ∧ i < n ∧ 1 ≤ j ∧ j < n ∧
        IndexedInteriorStep (sigma n d) (lengths α h) (yyPacket p b q) i j
          (yyPacket b b' (b-2*p)) := by
  let c : ℝ := 2*h*p-α*b
  obtain ⟨b', hnear, habs⟩ := exists_round c R hR hR1.le
  have hc : |c| ≤ (α+2*h)*(radius p b : ℝ) := by
    have hp : |(p : ℝ)| ≤ (radius p b : ℝ) := by
      rw [← cast_natAbs]
      exact_mod_cast (le_max_left p.natAbs b.natAbs)
    have hb : |(b : ℝ)| ≤ (radius p b : ℝ) := by
      rw [← cast_natAbs]
      exact_mod_cast (le_max_right p.natAbs b.natAbs)
    calc
      |c| ≤ |2*h*p| + |α*b| := abs_sub _ _
      _ = 2*h*|(p : ℝ)| + α*|(b : ℝ)| := by
        simp [abs_mul, abs_of_nonneg hh, abs_of_nonneg ha]
      _ ≤ (α+2*h)*(radius p b : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 2*h by linarith),
          mul_le_mul_of_nonneg_left hb ha]
  have hb' : (b'.natAbs : ℝ) ≤ (α+2*h)*(radius p b : ℝ)+1-R := by
    rw [cast_natAbs]
    linarith
  have hshift : |shift α h b b' (b-2*p)| ≤ R := by
    convert hnear using 2
    dsimp [shift, c]
    push_cast
    ring
  have hstart' : |β*shift α h p b q| ≤ (n : ℝ)-2 := by
    rw [abs_mul, abs_of_pos hβ, ← hβR]
    exact mul_le_mul_of_nonneg_left hstart hβ.le
  exact ⟨b', hb', hshift, run_to n d hn α h β hpos hβn hβh hβa p b q b'
    hstart' (hshift.trans_lt hR1)⟩

/-- For a radius with sufficient contraction margin, there is a strict
RUN/RUN choice staying in the domain and shrinking the new integer slot. -/
theorem shrinks_new_slot (n d : ℕ) (hn : 2 ≤ n) (α h β R : ℝ)
    (hpos : ∀ a, 0 < lengths α h a) (ha : 0 ≤ α) (hh : 0 ≤ h) (hβ : 0 < β)
    (hβn : β = (n : ℝ)+2+α) (hβh : β*h = 1) (hβa : β*α = (d : ℝ)-n+1-2*h)
    (hR : 1/2 ≤ R) (hR1 : R < 1) (hβR : β*R = (n : ℝ)-2)
    (p b q : ℤ) (hstart : |shift α h p b q| ≤ R)
    (hmargin : 1-R < (1-α-2*h)*(radius p b : ℝ)) :
    ∃ b' : ℤ, b'.natAbs < radius p b ∧ |shift α h b b' (b-2*p)| ≤ R ∧
      ∃ i j : ℕ, 1 ≤ i ∧ i < n ∧ 1 ≤ j ∧ j < n ∧
        IndexedInteriorStep (sigma n d) (lengths α h) (yyPacket p b q) i j
          (yyPacket b b' (b-2*p)) := by
  obtain ⟨z, hz, hshift, he⟩ := rounded_run_step n d hn α h β R hpos ha hh hβ hβn hβh hβa
    hR hR1 hβR p b q hstart
  have hz' : (z.natAbs : ℝ) < (radius p b : ℝ) := by linarith
  exact ⟨z, by exact_mod_cast hz', hshift, he⟩

/-- The rounded successor never increases the integer radius in the
contracting chamber, even when the strict decrease margin fails. -/
theorem run_preserves_radius (n d : ℕ) (hn : 2 ≤ n) (α h β R : ℝ)
    (hpos : ∀ a, 0 < lengths α h a) (ha : 0 ≤ α) (hh : 0 ≤ h) (hβ : 0 < β)
    (hβn : β = (n : ℝ)+2+α) (hβh : β*h = 1) (hβa : β*α = (d : ℝ)-n+1-2*h)
    (hR : 1/2 ≤ R) (hR1 : R < 1) (hβR : β*R = (n : ℝ)-2)
    (hγ : 0 ≤ 1-α-2*h) (p b q : ℤ) (hstart : |shift α h p b q| ≤ R) :
    ∃ z : ℤ, radius b z ≤ radius p b ∧ |shift α h b z (b-2*p)| ≤ R ∧
      InteriorStep (sigma n d) (lengths α h) (yyPacket p b q) (yyPacket b z (b-2*p)) := by
  obtain ⟨z, hz, hs, _, _, _, _, _, _, he⟩ := rounded_run_step n d hn α h β R hpos ha hh hβ
    hβn hβh hβa hR hR1 hβR p b q hstart
  have hnn := mul_nonneg hγ (Nat.cast_nonneg (α := ℝ) (radius p b))
  have hl : (z.natAbs : ℝ) < (radius p b : ℝ)+1 := by linarith
  have hz' : z.natAbs < radius p b + 1 := by exact_mod_cast hl
  exact ⟨z, max_le (le_max_right _ _) (by omega), hs, he.interiorStep⟩

/-- Every central run state reaches the residual radius strip through
selected actual RUN/RUN edges. The two-step induction keeps the full
packet and checks strictness at every chosen child. -/
theorem reaches_small_radius (n d : ℕ) (hn : 2 ≤ n) (α h β R : ℝ)
    (hpos : ∀ a, 0 < lengths α h a) (ha : 0 ≤ α) (hh : 0 ≤ h) (hβ : 0 < β)
    (hβn : β = (n : ℝ)+2+α) (hβh : β*h = 1) (hβa : β*α = (d : ℝ)-n+1-2*h)
    (hR : 1/2 ≤ R) (hR1 : R < 1) (hβR : β*R = (n : ℝ)-2)
    (p b q : ℤ) (hstart : |shift α h p b q| ≤ R) :
    ∃ u v w : ℤ, |shift α h u v w| ≤ R ∧ (1-α-2*h)*(radius u v : ℝ) ≤ 1-R ∧
      Relation.ReflTransGen (InteriorStep (sigma n d) (lengths α h))
        (yyPacket p b q) (yyPacket u v w) := by
  let m := radius p b
  have hm : radius p b = m := rfl
  clear_value m
  induction m using Nat.strong_induction_on generalizing p b q with
  | h m ih =>
    by_cases hsmall : (1-α-2*h)*(radius p b : ℝ) ≤ 1-R
    · exact ⟨p, b, q, hstart, hsmall, .refl⟩
    obtain ⟨b', hb', hs', i, j, _, _, _, _, e⟩ := shrinks_new_slot n d hn α h β R
      hpos ha hh hβ hβn hβh hβa hR hR1 hβR p b q hstart (lt_of_not_ge hsmall)
    have hm' : radius b b' ≤ m := by
      rw [← hm]
      exact max_le (le_max_right _ _) hb'.le
    by_cases hlt : radius b b' < m
    · obtain ⟨u, v, w, hs, hsmall', hp⟩ := ih _ hlt b b' (b-2*p) hs' rfl
      exact ⟨u, v, w, hs, hsmall', (Relation.ReflTransGen.single e.interiorStep).trans hp⟩
    have heq : radius b b' = m := le_antisymm hm' (le_of_not_gt hlt)
    have hmargin : 1-R < (1-α-2*h)*(radius b b' : ℝ) := by
      rw [heq, ← hm]
      exact lt_of_not_ge hsmall
    obtain ⟨b'', hb'', hs'', i', j', _, _, _, _, e'⟩ := shrinks_new_slot n d hn α h β R
      hpos ha hh hβ hβn hβh hβa hR hR1 hβR b b' (b-2*p) hs' hmargin
    have hlt' : radius b' b'' < m := max_lt (hm ▸ hb') (heq ▸ hb'')
    obtain ⟨u, v, w, hs, hsmall', hp⟩ := ih _ hlt' b' b'' (b'-2*b) hs'' rfl
    exact ⟨u, v, w, hs, hsmall', ((Relation.ReflTransGen.single e.interiorStep).tail e'.interiorStep).trans hp⟩

/-- The parameter identity turns the residual real margin into the small
integer strip `K * radius ≤ 5`, sharpened to `≤ 4` for `K ≥ 3`. -/
theorem parameter_residual_bound (n K m : ℕ) (α h β R : ℝ)
    (hh : 0 < h) (hβ : 0 < β) (ha : α < 1) (hR : 1/2 ≤ R)
    (hβn : β = (n : ℝ)+2+α) (hβh : β*h = 1) (hβR : β*R = (n : ℝ)-2)
    (hK : (1-α-2*h)*(β+1) = (K : ℝ))
    (hsmall : (1-α-2*h)*(m : ℝ) ≤ 1-R) :
    K*m ≤ 5 ∧ (3 ≤ K → K*m ≤ 4) := by
  have hk : (K : ℝ)*(m : ℝ) ≤ (1-R)*(β+1) := by
    have hm := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ β+1 by linarith)
    nlinarith only [hm, congrArg (fun z : ℝ => z*(m : ℝ)) hK]
  have hβδ : (1-R)*β = 4+α := by nlinarith only [hβR, hβn]
  constructor
  · have hm : (K : ℝ)*(m : ℝ) < 6 := by
      nlinarith only [hk, hβδ, hR, ha]
    have hm' : K*m < 6 := by exact_mod_cast hm
    omega
  · intro hK3
    have hkn : (3 : ℝ) ≤ K := by exact_mod_cast hK3
    have hαR : α < R := by
      apply (mul_lt_mul_iff_right₀ hβ).mp
      nlinarith only [hK, hβn, hβh, hβR, hkn, hh]
    have hm : (K : ℝ)*(m : ℝ) < 5 := by
      nlinarith only [hk, hβδ, hαR]
    have hm' : K*m < 5 := by exact_mod_cast hm
    omega

/-- In the Class-A chamber with `k+1 = K ≥ 5`, every central `y/y`
packet has a selected strict path to the typed zero coincidence. -/
theorem central_path_to_zero (n d K : ℕ) (hn : 7 ≤ n) (hK5 : 5 ≤ K)
    (α h β : ℝ) (hpos : ∀ a, 0 < lengths α h a) (ha0 : 0 ≤ α) (ha1 : α < 1)
    (hh : 0 < h) (hβ : 0 < β) (hβn : β = (n : ℝ)+2+α) (hβh : β*h = 1)
    (hβa : β*α = (d : ℝ)-n+1-2*h) (hK : (1-α-2*h)*(β+1) = (K : ℝ))
    (p b q : ℤ) (hstart : |β * shift α h p b q| ≤ (n : ℝ)-2) :
    Relation.ReflTransGen (InteriorStep (sigma n d) (lengths α h))
      (yyPacket p b q) zeroYy := by
  let R := ((n : ℝ)-2)/β
  have hn' : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hR : 1/2 ≤ R := by
    dsimp [R]
    exact (le_div_iff₀ hβ).mpr (by linarith)
  have hR1 : R < 1 := by
    dsimp [R]
    exact (div_lt_iff₀ hβ).mpr (by linarith)
  have hβR : β*R = (n : ℝ)-2 := by
    dsimp [R]
    rw [mul_div_cancel₀ _ hβ.ne']
  have hs : |shift α h p b q| ≤ R := by
    rw [abs_mul, abs_of_pos hβ, ← hβR] at hstart
    exact (mul_le_mul_iff_right₀ hβ).mp hstart
  obtain ⟨u, v, w, hsw, hm, hp⟩ := reaches_small_radius n d (by omega) α h β R hpos ha0
    hh.le hβ hβn hβh hβa hR hR1 hβR p b q hs
  have hm' := (parameter_residual_bound n K (radius u v) α h β R hh hβ ha1 hR
    hβn hβh hβR hK hm).2 (by omega)
  have huv : radius u v = 0 := by
    by_contra hu
    have hle : K ≤ K * radius u v := by
      simpa using Nat.mul_le_mul_left K (show 1 ≤ radius u v by omega)
    omega
  have hu : u = 0 := Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero ((le_max_left _ _).trans_eq huv))
  have hv : v = 0 := Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero ((le_max_right _ _).trans_eq huv))
  subst u v
  have hsw' : |β*shift α h 0 0 w| ≤ (n : ℝ)-2 := by
    rw [abs_mul, abs_of_pos hβ, ← hβR]
    exact mul_le_mul_of_nonneg_left hsw hβ.le
  obtain ⟨i, j, _, _, _, _, he⟩ := run_to n d (by omega) α h β hpos hβn hβh hβa
    0 0 w 0 hsw' (by norm_num [shift])
  have he' : InteriorStep (sigma n d) (lengths α h) (yyPacket 0 0 w) zeroYy :=
    he.interiorStep
  exact hp.tail he'

/-- Signed physical difference of the two inflated run origins. -/
def runOriginShift (ℓ : Fin 3 → ℝ) (β : ℝ) (w : Packet) : ℝ :=
  -(β * offset ℓ w.delta) + ℓ (first w.bottom) - ℓ (first w.top)

/-- For every oriented parent type, the closed interval of possible
RUN ordinal differences supplies a literal child with shift at most one
half of a `y` tile. -/
theorem enters_central_run (n d : ℕ) (hn : 2 ≤ n) (α h β : ℝ)
    (hpos : ∀ a, 0 < lengths α h a)
    (hscale : ∀ a, physicalLength (lengths α h) (sigma n d a) = β * lengths α h a)
    (source : Packet)
    (hlo : 1 - (runLength n d source.bottom : ℝ) ≤ runOriginShift (lengths α h) β source)
    (hhi : runOriginShift (lengths α h) β source ≤ (runLength n d source.top : ℝ)-1) :
    ∃ u v w : ℤ, |shift α h u v w| ≤ 1/2 ∧ ∃ i j : ℕ,
      1 ≤ i ∧ i ≤ runLength n d source.top ∧ 1 ≤ j ∧ j ≤ runLength n d source.bottom ∧
      IndexedInteriorStep (sigma n d) (lengths α h) source i j (yyPacket u v w) := by
  let D := runOriginShift (lengths α h) β source
  obtain ⟨g, hg, _⟩ := exists_round D (1/2) le_rfl (by norm_num)
  obtain ⟨hl, hu⟩ := abs_le.mp hg
  have hl' : (1 : ℤ) - (runLength n d source.bottom : ℤ) - 1 < g := by
    exact_mod_cast (show 1-(runLength n d source.bottom : ℝ)-1 < (g : ℝ) by linarith)
  have hu' : g < (runLength n d source.top : ℤ) := by
    exact_mod_cast (show (g : ℝ) < (runLength n d source.top : ℝ) by linarith)
  have ht0 := runLength_pos n d hn source.top
  have hb0 := runLength_pos n d hn source.bottom
  have ht : g.toNat < runLength n d source.top := by omega
  have hb : (-g).toNat < runLength n d source.bottom := by omega
  have hgap' : ((g.toNat : ℕ) : ℤ) - ((-g).toNat : ℤ) = g := by omega
  have hgap : ((g.toNat : ℕ) : ℝ) - ((-g).toNat : ℝ) = (g : ℝ) := by exact_mod_cast hgap'
  let dt := runMark n d source.top g.toNat ht
  let db := runMark n d source.bottom (-g).toNat hb
  let z := incidenceZ (sigma n d) *ᵥ source.delta + residual dt.before db.before
  let u := -z 0
  let w := -z 1
  let v := -z 2 + 2*u + w
  have hvec : (yyPacket u v w).delta = z := by
    funext a
    fin_cases a <;> simp [yyPacket, packet, u, v, w]
    ring
  have hoff : offset (lengths α h) z = (g : ℝ)-D := by
    dsimp [z]
    rw [offset_affine _ _ _ hscale]
    have hlen (a : Fin 3) (m : ℕ) :
        physicalLength (lengths α h) ([a] ++ List.replicate m 2) = lengths α h a + m := by
      rw [physicalLength_append, physicalLength_singleton]
      simp [physicalLength, dotProduct, List.count_replicate, lengths]
    have htlen : physicalLength (lengths α h) dt.before =
        lengths α h (first source.top) + g.toNat := hlen _ _
    have hblen : physicalLength (lengths α h) db.before =
        lengths α h (first source.bottom) + (-g).toNat := hlen _ _
    rw [htlen, hblen]
    dsimp [D, runOriginShift]
    linarith
  have hs : |shift α h u v w| ≤ 1/2 := by
    rw [← abs_neg, ← offset_yy, hvec, hoff]
    exact hg
  refine ⟨u, v, w, hs, g.toNat+1, (-g).toNat+1, by omega, by omega, by omega, by omega,
    ⟨⟨dt, db, runMark_index _ _ _ _ _, runMark_index _ _ _ _ _, ?_⟩,
      interior_of_abs_shift_lt_one hpos (hs.trans_lt (by norm_num))⟩⟩
  exact congrArg (Packet.mk 2 2) hvec

/-- The literal run-gap interval suffices for an ordered path to typed
coincidence from any of the nine parent-type pairs when `K ≥ 5`. -/
theorem run_gap_path_to_zero (n d K : ℕ) (hn : 7 ≤ n) (hK5 : 5 ≤ K)
    (α h β : ℝ) (hpos : ∀ a, 0 < lengths α h a) (ha0 : 0 ≤ α) (ha1 : α < 1)
    (hh : 0 < h) (hβ : 0 < β) (hβn : β = (n : ℝ)+2+α) (hβh : β*h = 1)
    (hβa : β*α = (d : ℝ)-n+1-2*h) (hK : (1-α-2*h)*(β+1) = (K : ℝ))
    (hscale : ∀ a, physicalLength (lengths α h) (sigma n d a) = β * lengths α h a)
    (source : Packet)
    (hlo : 1 - (runLength n d source.bottom : ℝ) ≤ runOriginShift (lengths α h) β source)
    (hhi : runOriginShift (lengths α h) β source ≤ (runLength n d source.top : ℝ)-1) :
    Relation.ReflTransGen (InteriorStep (sigma n d) (lengths α h)) source zeroYy := by
  obtain ⟨u, v, w, hnear, i, j, _, _, _, _, he⟩ := enters_central_run n d (by omega)
    α h β hpos hscale source hlo hhi
  have hβhalf : β*(1/2) ≤ (n : ℝ)-2 := by
    have hn' : (7 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hs : |β*shift α h u v w| ≤ (n : ℝ)-2 := by
    rw [abs_mul, abs_of_pos hβ]
    exact (mul_le_mul_of_nonneg_left hnear hβ.le).trans hβhalf
  exact (Relation.ReflTransGen.single he.interiorStep).trans
    (central_path_to_zero n d K hn hK5 α h β hpos ha0 ha1 hh hβ hβn hβh hβa hK u v w hs)

/-- Exact normalized length arithmetic for the literal minus-Class-A
words. Positivity and the three scaling equations determine these bounds. -/
theorem minus_class_a_length_arithmetic (k t : ℕ) (α h β : ℝ)
    (hpos : ∀ a, 0 < lengths α h a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength (lengths α h) (sigma (k+t+3) (k+2*t+5) a) =
      β * lengths α h a) :
    0 < h ∧ 0 ≤ α ∧ α < 1 ∧ β = ((k+t+3 : ℕ) : ℝ)+2+α ∧ β*h = 1 ∧
      β*α = ((k+2*t+5 : ℕ) : ℝ)-(k+t+3 : ℕ)+1-2*h ∧
      (1-α-2*h)*(β+1) = (k : ℝ)+1 := by
  let n := k+t+3
  let d := k+2*t+5
  have hn : 3 ≤ n := by dsimp [n]; omega
  have hn1 : 1 ≤ n := by omega
  have hd : (d : ℝ) = 2*(n : ℝ) - ((k : ℝ)+1) := by dsimp [n, d]; push_cast; ring
  have hdn : (n : ℝ)+2 ≤ (d : ℝ) := by
    dsimp [n, d]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) t]
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  change ∀ a, physicalLength (lengths α h) (sigma n d a) = β * lengths α h a at hscale
  have hrep (m : ℕ) : physicalLength (lengths α h) (List.replicate m 2) = (m : ℝ) := by
    simp [physicalLength, dotProduct, List.count_replicate, lengths]
  have hx := hscale 0
  have hc := hscale 1
  have hy := hscale 2
  simp [sigma, first, last, runLength, hrep] at hx hc hy
  simp [lengths, Nat.cast_sub hn1] at hx hc hy
  have hβn : β = (n : ℝ)+2+α := by linarith
  have hβh : β*h = 1 := by linarith
  have hh : 0 < h := by
    by_contra! hneg
    linarith [mul_nonpos_of_nonneg_of_nonpos hβ.le hneg]
  have hβa : β*α = (d : ℝ)-n+1-2*h := by linarith
  have hmargin : (1-α-2*h)*(β+1) = (k : ℝ)+1 := by
    nlinarith only [hβn, hβh, hβa, hd]
  have hxpos : 0 < 2+α-h := hpos 0
  have hh1 : h < 1 := by
    by_contra! hc
    linarith [mul_le_mul_of_nonneg_left hc hβ.le]
  have ha0 : 0 ≤ α := by
    by_contra! hbad
    linarith [mul_nonpos_of_nonneg_of_nonpos hβ.le hbad.le]
  have ha1 : α < 1 := by
    by_contra! hbad
    have hnonpos : 1-α-2*h ≤ 0 := by linarith
    have hk0 : 0 ≤ (k : ℝ) := by positivity
    linarith [mul_nonpos_of_nonpos_of_nonneg hnonpos (show 0 ≤ β+1 by linarith)]
  exact ⟨hh, ha0, ha1, hβn, hβh, hβa, hmargin⟩

/-- Literal minus-Class-A source theorem. The affine constants and the
contraction margin follow from the exact normalized length equations. -/
theorem minus_class_a_run_gap_path (k t : ℕ) (hk : 4 ≤ k) (α h β : ℝ)
    (hpos : ∀ a, 0 < lengths α h a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength (lengths α h) (sigma (k+t+3) (k+2*t+5) a) =
      β * lengths α h a) (source : Packet)
    (hlo : 1 - (runLength (k+t+3) (k+2*t+5) source.bottom : ℝ) ≤
      runOriginShift (lengths α h) β source)
    (hhi : runOriginShift (lengths α h) β source ≤
      (runLength (k+t+3) (k+2*t+5) source.top : ℝ)-1) :
    Relation.ReflTransGen (InteriorStep (sigma (k+t+3) (k+2*t+5)) (lengths α h))
      source zeroYy := by
  have hn : 7 ≤ k+t+3 := by omega
  obtain ⟨hh, ha0, ha1, hβn, hβh, hβa, hmargin⟩ :=
    minus_class_a_length_arithmetic k t α h β hpos hβ hscale
  refine run_gap_path_to_zero (k+t+3) (k+2*t+5) (k+1) hn (by omega) α h β hpos ha0 ha1 hh hβ hβn
    hβh hβa ?_ hscale source hlo hhi
  simpa only [Nat.cast_add, Nat.cast_one] using hmargin

end Psc.ClassARunDescent
