import PscVerif.ClassARunDescent
import PscVerif.OccurrenceWidth
import Mathlib.Topology.Order.IntermediateValue

/-! Entry into the literal run gap from every strict minus-Class-A packet
when `k ≥ 4`, followed by the selected run descent. -/
namespace Psc.ClassABoundaryEscape

open Psc.Descendants Psc.Reduction Psc.OccurrenceNewborn Psc.OccurrenceTransport Psc.OccurrenceMass
  Psc.OccurrenceWidth Psc.ClassAZeroDefectEscape Psc.ClassARunDescent Matrix

/-- The closed interval of possible signed differences between RUN indices. -/
def InRunGap (n d : ℕ) (ℓ : Fin 3 → ℝ) (β : ℝ) (p : Packet) : Prop :=
  1 - (runLength n d p.bottom : ℝ) ≤ runOriginShift ℓ β p ∧
    runOriginShift ℓ β p ≤ (runLength n d p.top : ℝ)-1

private theorem runOriginShift_swap (ℓ : Fin 3 → ℝ) (β : ℝ) (p : Packet) :
    runOriginShift ℓ β p.swap = -runOriginShift ℓ β p := by
  simp only [runOriginShift, Packet.swap, offset_neg]
  ring

private theorem edge_swap {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ} {p q : Packet}
    (he : InteriorStep s ℓ p.swap q) : InteriorStep s ℓ p q.swap := by
  have hs : p.swap.swap = p := by cases p; simp [Packet.swap]
  simpa only [hs] using (show InteriorStep s ℓ p.swap.swap q.swap from ⟨he.1.swap, he.2.swap⟩)

private theorem rep_y (α h : ℝ) (j : ℕ) :
    physicalLength (lengths α h) (List.replicate j 2) = (j : ℝ) := by
  simp [physicalLength, dotProduct, List.count_replicate, lengths]

private theorem image_length (n d : ℕ) (α h : ℝ) (a : Fin 3) :
    physicalLength (lengths α h) (sigma n d a) =
      lengths α h (first a) + (runLength n d a : ℝ) + lengths α h (last a) := by
  simp [sigma, rep_y, add_assoc]

private theorem upper_boundary_mass (n d : ℕ) (α h β : ℝ) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength (lengths α h) (sigma n d a) = β * lengths α h a)
    (p : Packet) (hp : p.Interior (lengths α h)) :
    β * packetMass (lengths α h) p ≤ lengths α h (first p.bottom) + lengths α h (last p.top) -
      (runOriginShift (lengths α h) β p - (runLength n d p.top : ℝ)) := by
  let ℓ := lengths α h
  let S := -β*offset ℓ p.delta
  let L := physicalLength ℓ (sigma n d p.top)
  let M := physicalLength ℓ (sigma n d p.bottom)
  have he : intervalMass 0 L S (S+M) = β*packetMass ℓ p :=
    inflated_mass (sigma n d) ℓ β hβ.le hscale p
  have hm : 0 < β*packetMass ℓ p := mul_pos hβ ((packetMass_pos_iff_interior ℓ p).mpr hp)
  have hm' : 0 < intervalMass 0 L S (S+M) := he.symm ▸ hm
  have hraw : 0 < min L (S+M)-max 0 S :=
    (lt_max_iff.mp hm').resolve_left (lt_irrefl _)
  have hb : β*packetMass ℓ p ≤ L-S := by
    rw [← he, intervalMass, max_eq_right hraw.le]
    linarith [min_le_left L (S+M), le_max_right 0 S]
  have hL : L = ℓ (first p.top) + (runLength n d p.top : ℝ) + ℓ (last p.top) :=
    image_length n d α h p.top
  dsimp [S, L, ℓ] at hb hL
  rw [hL] at hb
  dsimp [runOriginShift]
  linarith

/-- A wide upper-boundary overlap contains a whole bottom RUN tile in the
actual LAST tile on top. The choice uses the first or second RUN ordinal. -/
theorem upper_boundary_full_child (n d : ℕ) (hn : 7 ≤ n) (α h β : ℝ)
    (hβ : 0 < β) (hβ9 : 9 ≤ β) (hβn : β = (n : ℝ)+2+α)
    (ha1 : α < 1) (hx2 : 2 ≤ lengths α h 0) (hx3 : lengths α h 0 < 3)
    (hcx : lengths α h 1 ≤ lengths α h 0)
    (hscale : ∀ a, physicalLength (lengths α h) (sigma n d a) = β * lengths α h a)
    (p : Packet) (hwide : 1/2 ≤ packetMass (lengths α h) p)
    (hu : (runLength n d p.top : ℝ)-1 < runOriginShift (lengths α h) β p) :
    ∃ q, InteriorStep (sigma n d) (lengths α h) p q ∧ 1 ≤ packetMass (lengths α h) q := by
  let ℓ := lengths α h
  let F := ℓ (first p.bottom)
  let E := ℓ (last p.top)
  let X := runOriginShift ℓ β p - (runLength n d p.top : ℝ)
  have hp : p.Interior ℓ := (packetMass_pos_iff_interior ℓ p).mp (by linarith)
  have hmass := upper_boundary_mass n d α h β hβ hscale p hp
  change β * packetMass ℓ p ≤ F+E-X at hmass
  have hB : β/2 ≤ F+E-X := by
    have hb := mul_le_mul_of_nonneg_left hwide hβ.le
    change β*(1/2) ≤ β*packetMass ℓ p at hb
    linarith
  have hX : -1 < X := by dsimp [X]; linarith
  have hF : F = ℓ 0 ∨ F = ℓ 1 := by
    dsimp [F, first]
    split_ifs <;> simp
  have hE : E = ℓ 0 ∨ E = ℓ 1 := by
    dsimp [E, last]
    split_ifs <;> simp
  have hFl : F ≤ ℓ 0 := hF.elim (fun he => he.le) (fun he => he ▸ hcx)
  have hEl : E ≤ ℓ 0 := hE.elim (fun he => he.le) (fun he => he ▸ hcx)
  have hn' : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hFloor : ℓ 0 + ℓ 1 + 1 ≤ β/2 := by
    change (2+α-h)+(1+h)+1 ≤ β/2
    linarith
  have hEx : E = ℓ 0 := hE.elim id (fun he => by linarith)
  have hE2 : 2 ≤ E := hEx.symm ▸ hx2
  have hX' : X < E-1 := by linarith
  let j : ℕ := if X < 0 then 1 else 0
  have hj : j < runLength n d p.bottom := by
    have hmin : 2 ≤ runLength n d p.bottom := by
      generalize p.bottom = a
      fin_cases a <;> simp [runLength] <;> omega
    dsimp [j]
    split_ifs <;> omega
  have hjbounds : 0 ≤ X+(j : ℝ) ∧ X+(j : ℝ)+1 ≤ E := by
    dsimp [j]
    split_ifs <;> push_cast <;> constructor <;> linarith
  let dt := lastMark n d p.top
  let db := runMark n d p.bottom j hj
  let T := ℓ (first p.top) + (runLength n d p.top : ℝ)
  let S := -β*offset ℓ p.delta
  have ht : physicalLength ℓ dt.before = T := by
    simp [ℓ, dt, lastMark, rep_y, T]
  have hb : S+physicalLength ℓ db.before = T+X+(j : ℝ) := by
    simp [ℓ, db, runMark, rep_y, T, X, S, runOriginShift, add_assoc]
  have htl : ℓ dt.letter = E := rfl
  have hbl : ℓ db.letter = 1 := rfl
  apply child_of_marks (sigma n d) ℓ β hscale p dt db 1 (by norm_num)
  change 1 ≤ intervalMass (physicalLength ℓ dt.before) (physicalLength ℓ dt.before + ℓ dt.letter)
    (S+physicalLength ℓ db.before) (S+physicalLength ℓ db.before + ℓ db.letter)
  rw [ht, hb, htl, hbl]
  exact le_intervalMass_of_common _ _ _ _ (T+X+j) 1 (by linarith [hjbounds.1]) le_rfl
    (by linarith [hjbounds.2]) le_rfl

/-- A full unit of common length places the original packet inside the run
interval, since every boundary overlap is shorter than seven after inflation. -/
theorem unit_mass_in_run_gap (n d : ℕ) (α h β : ℝ) (hβ9 : 9 ≤ β)
    (hsmall : ∀ a, lengths α h a < 3)
    (hscale : ∀ a, physicalLength (lengths α h) (sigma n d a) = β * lengths α h a)
    (p : Packet) (hfull : 1 ≤ packetMass (lengths α h) p) :
    InRunGap n d (lengths α h) β p := by
  have hβ : 0 < β := by linarith
  have upper (q : Packet) (hq : 1 ≤ packetMass (lengths α h) q) :
      runOriginShift (lengths α h) β q ≤ (runLength n d q.top : ℝ)-1 := by
    have hi : q.Interior (lengths α h) := (packetMass_pos_iff_interior _ _).mp (by linarith)
    have hm := upper_boundary_mass n d α h β hβ hscale q hi
    have hb := mul_le_mul_of_nonneg_left hq hβ.le
    by_contra! hbad
    linarith [hsmall (first q.bottom), hsmall (last q.top)]
  have hr := upper p hfull
  have hl := upper p.swap (by rwa [packetMass_swap])
  rw [runOriginShift_swap] at hl
  exact ⟨by simpa [Packet.swap] using (show 1-(runLength n d p.swap.top : ℝ) ≤
    runOriginShift (lengths α h) β p by linarith), hr⟩

/-- Every strict packet enters the run gap when `n = k+t+3 ≥ 7`. -/
theorem minus_class_a_strict_enters_run_gap (k t : ℕ) (hn : 7 ≤ k+t+3) (α h β : ℝ)
    (hpos : ∀ a, 0 < lengths α h a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength (lengths α h) (sigma (k+t+3) (k+2*t+5) a) =
      β * lengths α h a) (p : Packet) (hp : p.Interior (lengths α h)) :
    ∃ q, Relation.ReflTransGen (InteriorStep (sigma (k+t+3) (k+2*t+5)) (lengths α h)) p q ∧
      InRunGap (k+t+3) (k+2*t+5) (lengths α h) β q := by
  let n := k+t+3
  let d := k+2*t+5
  let ℓ := lengths α h
  obtain ⟨hh, ha0, ha1, hβn, hβh, hβa, _⟩ :=
    minus_class_a_length_arithmetic k t α h β hpos hβ hscale
  change β = (n : ℝ)+2+α at hβn
  change β*α = (d : ℝ)-(n : ℝ)+1-2*h at hβa
  change 7 ≤ n at hn
  have hn' : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hβ9 : 9 ≤ β := by linarith
  have hhhalf : h < 1/2 := by
    by_contra! hb
    linarith [mul_le_mul_of_nonneg_left hb hβ.le]
  have hdn : (n : ℝ)+2 ≤ d := by
    dsimp [n, d]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) t]
  have hαh : h < α := by
    apply (mul_lt_mul_iff_right₀ hβ).mp
    linarith
  have hx2 : 2 ≤ ℓ 0 := by change 2 ≤ 2+α-h; linarith
  have hx3 : ℓ 0 < 3 := by change 2+α-h < 3; linarith
  have hcx : ℓ 1 ≤ ℓ 0 := by change 1+h ≤ 2+α-h; linarith
  have hunit : ∀ a, 1 ≤ ℓ a := by
    intro a
    fin_cases a
    · exact (show (1 : ℝ) ≤ 2 by norm_num).trans hx2
    · change 1 ≤ 1+h; linarith
    · norm_num [ℓ, lengths]
  have hsmall : ∀ a, ℓ a < 3 := by
    intro a
    fin_cases a
    · exact hx3
    · exact hcx.trans_lt hx3
    · norm_num [ℓ, lengths]
  obtain ⟨q, hpq, hwide⟩ := reaches_half_mass (sigma n d) ℓ β hunit (by linarith) hscale p hp
  by_cases hg : InRunGap n d ℓ β q
  · exact ⟨q, hpq, hg⟩
  have hchild : ∃ r, InteriorStep (sigma n d) ℓ q r ∧ 1 ≤ packetMass ℓ r := by
    by_cases hup : (runLength n d q.top : ℝ)-1 < runOriginShift ℓ β q
    · exact upper_boundary_full_child n d hn α h β hβ hβ9 hβn ha1 hx2 hx3 hcx hscale q hwide hup
    · have hlow : runOriginShift ℓ β q < 1-(runLength n d q.bottom : ℝ) := by
        by_contra! hlo
        exact hg ⟨hlo, le_of_not_gt hup⟩
      have hs : (runLength n d q.swap.top : ℝ)-1 < runOriginShift ℓ β q.swap := by
        rw [runOriginShift_swap]
        change (runLength n d q.bottom : ℝ)-1 < -runOriginShift ℓ β q
        linarith
      obtain ⟨r, he, hfull⟩ := upper_boundary_full_child n d hn α h β hβ hβ9 hβn ha1 hx2 hx3 hcx
        hscale q.swap (by rwa [packetMass_swap]) hs
      exact ⟨r.swap, edge_swap he, by rwa [packetMass_swap]⟩
  obtain ⟨r, hqr, hfull⟩ := hchild
  have hr := unit_mass_in_run_gap n d α h β hβ9 hsmall hscale r hfull
  exact ⟨r, hpq.tail hqr, hr⟩

/-- In every `n ≥ 7` chamber, arbitrary strict sources reach a central
`y/y` packet in a parameter-independent integer box. The extra rounded
step bounds the third coordinate without increasing the two-slot radius. -/
theorem minus_class_a_strict_reaches_residual (k t : ℕ) (hn : 7 ≤ k+t+3) (α h β : ℝ)
    (hpos : ∀ a, 0 < lengths α h a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength (lengths α h) (sigma (k+t+3) (k+2*t+5) a) =
      β * lengths α h a) (p : Packet) (hp : p.Interior (lengths α h)) :
    ∃ u v w : ℤ, (k+1)*radius u v ≤ 5 ∧ (2 ≤ k → (k+1)*radius u v ≤ 4) ∧
      w.natAbs ≤ 15 ∧ |β*shift α h u v w| ≤ ((k+t+3 : ℕ) : ℝ)-2 ∧
      Relation.ReflTransGen (InteriorStep (sigma (k+t+3) (k+2*t+5)) (lengths α h))
        p (yyPacket u v w) := by
  let n := k+t+3
  let d := k+2*t+5
  let R := ((n : ℝ)-2)/β
  change 7 ≤ n at hn
  obtain ⟨hh, ha0, ha1, hβn, hβh, hβa, hmargin⟩ :=
    minus_class_a_length_arithmetic k t α h β hpos hβ hscale
  change β = (n : ℝ)+2+α at hβn
  change β*α = (d : ℝ)-(n : ℝ)+1-2*h at hβa
  have hK : (1-α-2*h)*(β+1) = ((k+1 : ℕ) : ℝ) := by simpa using hmargin
  have hγ : 0 ≤ 1-α-2*h := by
    by_contra! hb
    linarith [mul_neg_of_neg_of_pos hb (show 0 < β+1 by linarith), Nat.cast_nonneg (α := ℝ) k]
  have hn' : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hR : 1/2 ≤ R := (le_div_iff₀ hβ).mpr (by linarith)
  have hR1 : R < 1 := (div_lt_iff₀ hβ).mpr (by linarith)
  have hβR : β*R = (n : ℝ)-2 := by dsimp [R]; rw [mul_div_cancel₀ _ hβ.ne']
  obtain ⟨q, hpq, hgap⟩ := minus_class_a_strict_enters_run_gap k t hn α h β hpos hβ hscale p hp
  obtain ⟨p₀, b₀, q₀, hnear, i, j, _, _, _, _, he⟩ :=
    enters_central_run n d (by omega) α h β hpos hscale q hgap.1 hgap.2
  obtain ⟨u, v, w, hsw, hres, hpw⟩ := reaches_small_radius n d (by omega) α h β R
    hpos ha0 hh.le hβ hβn hβh hβa hR hR1 hβR p₀ b₀ q₀ (hnear.trans hR)
  obtain ⟨hsize, hsize'⟩ := parameter_residual_bound n (k+1) (radius u v) α h β R
    hh hβ ha1 hR hβn hβh hβR hK hres
  obtain ⟨z, hrad, hnxt, hwz⟩ := run_preserves_radius n d (by omega) α h β R
    hpos ha0 hh.le hβ hβn hβh hβa hR hR1 hβR hγ u v w hsw
  have hm : radius u v ≤ 5 := by
    have ht := Nat.mul_le_mul_right (radius u v) (show 1 ≤ k+1 by omega)
    simpa only [one_mul] using ht.trans hsize
  have hu : u.natAbs ≤ 5 := (le_max_left _ _).trans hm
  have hv : v.natAbs ≤ 5 := (le_max_right _ _).trans hm
  have hbnd : (v-2*u).natAbs ≤ 15 := by omega
  have hclip : |β*shift α h v z (v-2*u)| ≤ (n : ℝ)-2 := by
    rw [abs_mul,abs_of_pos hβ,← hβR]
    exact mul_le_mul_of_nonneg_left hnxt hβ.le
  have hradk := Nat.mul_le_mul_left (k+1) hrad
  refine ⟨v, z, v-2*u, hradk.trans hsize, fun hk => hradk.trans (hsize' (by omega)),
    hbnd, hclip, ?_⟩
  exact ((hpq.tail he.interiorStep).trans hpw).tail hwz

/-- Every strict packet of the literal minus-Class-A words with `k ≥ 4`
reaches a typed coincidence by an actual ordered occurrence path. -/
theorem minus_class_a_strict_path (k t : ℕ) (hk : 4 ≤ k) (α h β : ℝ)
    (hpos : ∀ a, 0 < lengths α h a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength (lengths α h) (sigma (k+t+3) (k+2*t+5) a) =
      β * lengths α h a) (p : Packet) (hp : p.Interior (lengths α h)) :
    Relation.ReflTransGen (InteriorStep (sigma (k+t+3) (k+2*t+5)) (lengths α h))
      p zeroYy := by
  obtain ⟨q, hpq, hgap⟩ := minus_class_a_strict_enters_run_gap k t (by omega) α h β hpos hβ
    hscale p hp
  exact hpq.trans (minus_class_a_run_gap_path k t hk α h β hpos hβ hscale q hgap.1 hgap.2)

/-- The strict-packet route lifts to a literal balanced-pair child path
from any actual irreducible marked source carrying that overlap. -/
theorem minus_class_a_marked_path (k t : ℕ) (hk : 4 ≤ k) (α h β : ℝ)
    (hpos : ∀ a, 0 < lengths α h a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength (lengths α h) (sigma (k+t+3) (k+2*t+5) a) =
      β * lengths α h a) (m : MarkedPair) (hblock : IsBlock m.words)
    (hp : m.packet.Interior (lengths α h)) :
    ∃ U : WordPair, Relation.ReflTransGen (Child (sigma (k+t+3) (k+2*t+5))) m.words U ∧
      IsBlock U ∧ U.1 = U.2 := by
  apply packet_path_literal_target _ _ hpos m hblock
    (minus_class_a_strict_path k t hk α h β hpos hβ hscale m.packet hp)
  exact ⟨rfl, by funext a; fin_cases a <;> rfl⟩

private theorem stop_at_coincidence {s : Fin 3 → Word} {T U : WordPair}
    (hp : Relation.ReflTransGen (Child s) T U) (he : U.1 = U.2) :
    ∃ V : WordPair, Relation.ReflTransGen (ChildNC s) T V ∧ V.1 = V.2 := by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨_, .refl, he⟩
  | @head T W hTW _ ih =>
    by_cases hc : T.1 = T.2
    · exact ⟨T, .refl, hc⟩
    · obtain ⟨V, hw, hv⟩ := ih
      exact ⟨V, hw.head ⟨hc, hTW⟩, hv⟩

/-- Every nonempty irreducible balanced pair has a common interior of its
first tiles. The strict-packet result therefore gives a literal terminal
ChildNC path for every such block. -/
theorem minus_class_a_block_has_coincidence (k t : ℕ) (hk : 4 ≤ k) (α h β : ℝ)
    (hpos : ∀ a, 0 < lengths α h a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength (lengths α h) (sigma (k+t+3) (k+2*t+5) a) =
      β * lengths α h a) (T : WordPair) (hT : IsBlock T) :
    ∃ U : WordPair, Relation.ReflTransGen (ChildNC (sigma (k+t+3) (k+2*t+5))) T U ∧
      U.1 = U.2 := by
  rcases T with ⟨u, v⟩
  cases u with
  | nil => exact (hT.1 rfl).elim
  | cons a u =>
    cases v with
    | nil => simpa using hT.2.1.length_eq
    | cons b v =>
      let m : MarkedPair := ⟨(a::u,b::v), ⟨[],a,u,rfl⟩, ⟨[],b,v,rfl⟩⟩
      have hz : m.packet.delta = 0 := by
        simp [m, MarkedPair.packet, Psc.OccurrenceTransport.residual]
      have hm : m.packet.Interior (lengths α h) := by
        apply (Packet.interior_iff_bounds _ hpos _).mpr
        rw [hz]
        simpa [offset, dotProduct, m, MarkedPair.packet] using
          And.intro (hpos a) (hpos b)
      obtain ⟨U, hu, _, he⟩ := minus_class_a_marked_path k t hk α h β hpos hβ hscale m hT hm
      exact stop_at_coincidence hu he

/-- A positive normalized exact length solution follows from the positive
root of the literal incidence cubic. The bracketing argument is exact. -/
theorem minus_class_a_lengths_exist (k t : ℕ) :
    ∃ α h β : ℝ, 0 < β ∧ (∀ a, 0 < lengths α h a) ∧
      (∀ a, physicalLength (lengths α h) (sigma (k+t+3) (k+2*t+5) a) =
        β * lengths α h a) := by
  let n := k+t+3
  let d := k+2*t+5
  let a : ℝ := (n : ℝ)+2
  let b : ℝ := (n : ℝ)+3
  let f (z : ℝ) : ℝ := z^3-a*z^2-((t : ℝ)+3)*z+2
  have hn : 1 ≤ n := by dsimp [n]; omega
  have ha : 5 ≤ a := by
    dsimp [a, n]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) t]
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hb : b = a+1 := by dsimp [a,b]; ring
  have hab : a ≤ b := by linarith
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hfa : f a < 0 := by
    dsimp only [f]
    nlinarith [mul_nonneg (show 0 ≤ a by linarith) ht]
  have hfb : 0 < f b := by
    have hbt : b-((t : ℝ)+3) = (k : ℝ)+3 := by
      dsimp [b,n]
      push_cast
      ring
    have hbp : 0 ≤ b*((k : ℝ)+3) := mul_nonneg (by linarith) (by linarith)
    change 0 < b^3-a*b^2-((t : ℝ)+3)*b+2
    nlinarith only [congrArg (fun z : ℝ => z*b^2) hb,
      congrArg (fun z : ℝ => z*b) hbt, hbp]
  obtain ⟨β, ⟨hβa, hβb⟩, hroot⟩ := intermediate_value_Ioo hab hf.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (f a) (f b) from ⟨hfa,hfb⟩)
  let α := β-a
  let h := 1/β
  have hβ : 0 < β := by linarith
  have hα : 0 < α := sub_pos.mpr hβa
  have hh : 0 < h := div_pos (by norm_num) hβ
  have hh1 : h < 1 := (div_lt_iff₀ hβ).mpr (by linarith)
  have hβh : β*h = 1 := by dsimp [h]; rw [mul_div_cancel₀ _ hβ.ne']
  have hβeq : β = (n : ℝ)+2+α := by dsimp [α,a]; ring
  have hβalpha : β*α = (t : ℝ)+3-2*h := by
    apply (mul_left_cancel₀ hβ.ne')
    dsimp [f] at hroot
    dsimp [α]
    nlinarith only [hβh,hroot]
  have hdn : (d : ℝ)-(n : ℝ)+1 = (t : ℝ)+3 := by
    dsimp [d,n]; push_cast; ring
  refine ⟨α, h, β, hβ, ?_, ?_⟩
  · intro z
    fin_cases z
    · change 0 < 2+α-h; linarith
    · change 0 < 1+h; linarith
    · change (0 : ℝ) < 1; norm_num
  · intro z
    change physicalLength (lengths α h) (sigma n d z) = β*lengths α h z
    rw [image_length]
    fin_cases z <;> simp [first,last,runLength,lengths,Nat.cast_sub hn] <;>
      linarith [hβeq,hβh,hβalpha,hdn]

/-- Unconditional literal ChildNC productivity of every irreducible block
for every `k ≥ 4` and every `t ≥ 0` in this family. -/
theorem minus_class_a_all_blocks (k t : ℕ) (hk : 4 ≤ k)
    (T : WordPair) (hT : IsBlock T) :
    ∃ U : WordPair, Relation.ReflTransGen (ChildNC (sigma (k+t+3) (k+2*t+5))) T U ∧
      U.1 = U.2 := by
  obtain ⟨α,h,β,hβ,hpos,hscale⟩ := minus_class_a_lengths_exist k t
  exact minus_class_a_block_has_coincidence k t hk α h β hpos hβ hscale T hT

end Psc.ClassABoundaryEscape
