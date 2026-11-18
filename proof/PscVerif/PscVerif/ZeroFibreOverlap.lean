import PscVerif.GeometricFRank
import PscVerif.OccurrenceAddress
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Logic.Relation

/-!
# Literal overlap reachability for the zero-fibre criterion

The graph uses the bottom start minus the top start. Children are two
occurrences in the actual image words, with strictly overlapping projected
interiors. The target is equal labels and zero integral displacement.
The geometric realization of the zero fibre is an external input.
-/

namespace Psc.GeometricF

open Matrix Psc.Binomial Psc.Incidence Psc.OccurrenceAddress

variable {α : Type*} [DecidableEq α] [Fintype α]
variable {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ}

@[simp] theorem edgeDescendant_zero_iff {x y : IntegralEdge α} :
    EdgeDescendant s 0 x y ↔ x = y := by
  constructor
  · rintro ⟨P, Q, hw, hcoord⟩
    change [x.1] = P ++ y.1 :: Q at hw
    have hlen := congrArg List.length hw
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    have hP : P = [] := List.length_eq_zero_iff.mp (by omega)
    have hQ : Q = [] := List.length_eq_zero_iff.mp (by omega)
    exact Prod.ext (by simpa [hP, hQ] using hw) (by simpa [hP] using hcoord.symm)
  · rintro rfl
    exact ⟨[], [], rfl, by simp⟩

theorem edgeDescendant_one_iff {x y : IntegralEdge α} :
    EdgeDescendant s 1 x y ↔
      ∃ P Q : List α, s x.1 = P ++ y.1 :: Q ∧ y.2 = incZ s *ᵥ x.2 + pvec P := by
  simp [EdgeDescendant, power, subst]

/-- Desubstitute the selected letter by its actual occurrence address. -/
theorem edgeDescendant_succ_iff {n : ℕ} {x z : IntegralEdge α} :
    EdgeDescendant s (n + 1) x z ↔
      ∃ y, EdgeDescendant s n x y ∧ EdgeDescendant s 1 y z := by
  constructor
  · rintro ⟨U, V, hw, hz⟩
    let w := power s n x.1
    have hw' : subst s w = U ++ z.1 :: V := by
      simpa only [w, power, Function.iterate_succ_apply'] using hw
    have hk : U.length < (subst s w).length := by rw [hw']; simp
    let o := locateSubst s w U.length hk
    have hl : o.letter = z.1 := by
      have hselected : (subst s w)[U.length]? = some z.1 := by rw [hw']; simp
      exact Option.some.inj (o.selected.symm.trans hselected)
    have hU : U = subst s (w.take o.ordinal) ++ o.before := by
      calc
        U = (subst s w).take U.length := by rw [hw']; simp
        _ = _ := o.prefix_eq
    let y : IntegralEdge α := (o.factor, incZ s ^ n *ᵥ x.2 + pvec (w.take o.ordinal))
    refine ⟨y, ⟨w.take o.ordinal, w.drop (o.ordinal + 1), ?_, rfl⟩,
      edgeDescendant_one_iff.mpr ?_⟩
    · change w = w.take o.ordinal ++ o.factor :: w.drop (o.ordinal + 1)
      obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp o.atOrdinal
      rw [← he, List.getElem_cons_drop hi, List.take_append_drop]
    · refine ⟨o.before, o.after, by simpa only [y, hl] using o.split, ?_⟩
      change z.2 = incZ s *ᵥ (incZ s ^ n *ᵥ x.2 + pvec (w.take o.ordinal)) + pvec o.before
      rw [hz, congrArg pvec hU, pvec_append, pvec_subst, pow_succ', Matrix.mulVec_add,
        Matrix.mulVec_mulVec]
      abel
  · rintro ⟨y, hx, hz⟩
    exact edgeDescendant_comp hx hz

/-- The projected descendant interval is contained in the inflated parent. -/
theorem edgeDescendant_bounds (hL : LengthData s L β) {n : ℕ} {x y : IntegralEdge α}
    (h : EdgeDescendant s n x y) :
    β ^ n * L x.2 ≤ L y.2 ∧
      L y.2 + L (pvec [y.1]) ≤ β ^ n * (L x.2 + L (pvec [x.1])) := by
  obtain ⟨P, Q, hw, hy⟩ := h
  have hword := congrArg (fun w => L (pvec w)) hw
  change L (pvec ((subst s)^[n] [x.1])) = L (pvec (P ++ y.1 :: Q)) at hword
  rw [pvec_iterate, hL.eigen_pow, pvec_append P, pvec_cons y.1 Q, map_add, map_add] at hword
  have hy' : L y.2 = β ^ n * L x.2 + L (pvec P) := by rw [hy, map_add, hL.eigen_pow]
  rw [mul_add]
  exact ⟨by linarith [L_pvec_nonneg hL.pos P], by linarith [L_pvec_nonneg hL.pos Q]⟩

structure OverlapCoordinates (α : Type*) where
  top : α
  bottom : α
  shift : α → ℤ

def OverlapCoordinates.Interior (L : (α → ℤ) →+ ℝ) (u : OverlapCoordinates α) : Prop :=
  -L (pvec [u.bottom]) < L u.shift ∧ L u.shift < L (pvec [u.top])

def OverlapCoordinates.Diagonal (u : OverlapCoordinates α) : Prop :=
  u.top = u.bottom ∧ u.shift = 0

def overlapOf (x y : IntegralEdge α) : OverlapCoordinates α :=
  ⟨x.1, y.1, y.2 - x.2⟩

omit [DecidableEq α] [Fintype α] in
theorem overlapOf_diagonal_iff {x y : IntegralEdge α} :
    (overlapOf x y).Diagonal ↔ x = y := by
  cases x
  cases y
  simp [OverlapCoordinates.Diagonal, overlapOf, sub_eq_zero, eq_comm]

omit [Fintype α] in
theorem overlapOf_interior_iff {x y : IntegralEdge α} :
    (overlapOf x y).Interior L ↔
      L x.2 < L y.2 + L (pvec [y.1]) ∧ L y.2 < L x.2 + L (pvec [x.1]) := by
  simp only [OverlapCoordinates.Interior, overlapOf, map_sub]
  constructor <;> rintro ⟨ha, hb⟩ <;> exact ⟨by linarith, by linarith⟩

/-- A strict overlap of two descendants forces strict overlap of their parents. -/
theorem overlapOf_descendant_source (hL : LengthData s L β)
    {n : ℕ} {x y a b : IntegralEdge α} (ha : EdgeDescendant s n x a)
    (hb : EdgeDescendant s n y b) (hi : (overlapOf a b).Interior L) :
    (overlapOf x y).Interior L := by
  rw [overlapOf_interior_iff] at hi ⊢
  obtain ⟨hxa, hax⟩ := edgeDescendant_bounds hL ha
  obtain ⟨hyb, hby⟩ := edgeDescendant_bounds hL hb
  have hβn : 0 < β ^ n := pow_pos hL.beta_pos n
  exact ⟨lt_of_mul_lt_mul_left (hxa.trans_lt (hi.1.trans_le hby)) hβn.le,
    lt_of_mul_lt_mul_left (hyb.trans_lt (hi.2.trans_le hax)) hβn.le⟩

theorem overlapOf_self_interior (hL : LengthData s L β) (x : IntegralEdge α) :
    (overlapOf x x).Interior L := by
  rw [overlapOf_interior_iff]
  exact ⟨lt_add_of_pos_right _ (hL.pos x.1), lt_add_of_pos_right _ (hL.pos x.1)⟩

/-- Two literal source-image occurrences supply the labels and the next shift. -/
def LiteralOverlapChild (s : α → List α) (u v : OverlapCoordinates α) : Prop :=
  ∃ U U' V V' : List α,
    s u.top = U ++ v.top :: U' ∧ s u.bottom = V ++ v.bottom :: V' ∧
    v.shift = incZ s *ᵥ u.shift + pvec V - pvec U

theorem literalOverlapChild_iff {x y : IntegralEdge α} {v : OverlapCoordinates α} :
    LiteralOverlapChild s (overlapOf x y) v ↔
      ∃ a b, EdgeDescendant s 1 x a ∧ EdgeDescendant s 1 y b ∧ overlapOf a b = v := by
  constructor
  · rintro ⟨U, U', V, V', hU, hV, hz⟩
    refine ⟨(v.top, incZ s *ᵥ x.2 + pvec U), (v.bottom, incZ s *ᵥ y.2 + pvec V),
      edgeDescendant_one_iff.mpr ⟨U, U', hU, rfl⟩,
      edgeDescendant_one_iff.mpr ⟨V, V', hV, rfl⟩, ?_⟩
    cases v
    simp only [overlapOf, OverlapCoordinates.mk.injEq, true_and] at hz ⊢
    rw [hz, Matrix.mulVec_sub]
    abel
  · rintro ⟨a, b, ha, hb, rfl⟩
    obtain ⟨U, U', hU, hxa⟩ := edgeDescendant_one_iff.mp ha
    obtain ⟨V, V', hV, hyb⟩ := edgeDescendant_one_iff.mp hb
    refine ⟨U, U', V, V', hU, hV, ?_⟩
    change b.2 - a.2 = incZ s *ᵥ (y.2 - x.2) + pvec V - pvec U
    rw [hxa, hyb, Matrix.mulVec_sub]
    abel

abbrev StrictOverlap (L : (α → ℤ) →+ ℝ) := {u : OverlapCoordinates α // u.Interior L}

abbrev StrictOverlapChild (s : α → List α) (L : (α → ℤ) →+ ℝ)
    (u v : StrictOverlap L) : Prop :=
  LiteralOverlapChild s u.val v.val

abbrev OverlapReach (s : α → List α) (L : (α → ℤ) →+ ℝ) :=
  Relation.ReflTransGen (StrictOverlapChild s L)

abbrev OverlapBeforeDiagonal (s : α → List α) (L : (α → ℤ) →+ ℝ)
    (u v : StrictOverlap L) : Prop :=
  ¬ u.val.Diagonal ∧ StrictOverlapChild s L u v

def OverlapProductive (s : α → List α) (L : (α → ℤ) →+ ℝ) (u : StrictOverlap L) : Prop :=
  ∃ v, OverlapReach s L u v ∧ v.val.Diagonal

theorem edgeDescendants_of_overlap_reach {u v : StrictOverlap L}
    (h : OverlapReach s L u v) {x y : IntegralEdge α}
    (hu : overlapOf x y = u.val) :
    ∃ n a b, EdgeDescendant s n x a ∧ EdgeDescendant s n y b ∧ overlapOf a b = v.val := by
  induction h with
  | refl => exact ⟨0, x, y, edgeDescendant_zero_iff.mpr rfl, edgeDescendant_zero_iff.mpr rfl, hu⟩
  | @tail u' v' _ he ih =>
    obtain ⟨n, a, b, ha, hb, hpair⟩ := ih
    have hstep : LiteralOverlapChild s (overlapOf a b) v'.val := hpair.symm ▸ he
    obtain ⟨c, d, hc, hd, hcd⟩ := literalOverlapChild_iff.mp hstep
    exact ⟨n + 1, c, d, edgeDescendant_comp ha hc, edgeDescendant_comp hb hd, hcd⟩

theorem overlap_reach_of_edgeDescendants (hL : LengthData s L β) {n : ℕ}
    {x y a b : IntegralEdge α} (ha : EdgeDescendant s n x a) (hb : EdgeDescendant s n y b)
    (hab : (overlapOf a b).Interior L) :
    OverlapReach s L
      ⟨overlapOf x y, overlapOf_descendant_source hL ha hb hab⟩ ⟨overlapOf a b, hab⟩ := by
  induction n generalizing a b with
  | zero =>
    cases edgeDescendant_zero_iff.mp ha
    cases edgeDescendant_zero_iff.mp hb
    exact .refl
  | succ n ih =>
    obtain ⟨c, hc, hca⟩ := edgeDescendant_succ_iff.mp ha
    obtain ⟨d, hd, hdb⟩ := edgeDescendant_succ_iff.mp hb
    have hcd := overlapOf_descendant_source hL hca hdb hab
    exact (ih hc hd hcd).tail (literalOverlapChild_iff.mpr ⟨a, b, hca, hdb, rfl⟩)

theorem edgeCoincident_iff_overlap_productive (hL : LengthData s L β) {x y : IntegralEdge α} :
    EdgeCoincident s x y ↔
      ∃ h : (overlapOf x y).Interior L, OverlapProductive s L ⟨overlapOf x y, h⟩ := by
  constructor
  · rintro ⟨n, a, hxa, hya⟩
    have haa := overlapOf_self_interior hL a
    exact ⟨overlapOf_descendant_source hL hxa hya haa,
      ⟨overlapOf a a, haa⟩, overlap_reach_of_edgeDescendants hL hxa hya haa,
      overlapOf_diagonal_iff.mpr rfl⟩
  · rintro ⟨_, v, hv, hd⟩
    obtain ⟨n, a, b, ha, hb, hpair⟩ := edgeDescendants_of_overlap_reach hv rfl
    have hab := overlapOf_diagonal_iff.mp (hpair.symm ▸ hd : (overlapOf a b).Diagonal)
    exact ⟨n, a, ha, hab.symm ▸ hb⟩

/-- Stop expanding a path at the first diagonal, as in the executable graph. -/
theorem overlap_productive_iff_terminal_reach (u : StrictOverlap L) :
    OverlapProductive s L u ↔
      ∃ v, Relation.ReflTransGen (OverlapBeforeDiagonal s L) u v ∧ v.val.Diagonal := by
  constructor
  · rintro ⟨v, hreach, htarget⟩
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨v, .refl, htarget⟩
    | @head a b hab _ ih =>
      by_cases ha : a.val.Diagonal
      · exact ⟨a, .refl, ha⟩
      · obtain ⟨c, hbc, htarget⟩ := ih
        exact ⟨c, hbc.head ⟨ha, hab⟩, htarget⟩
  · rintro ⟨v, hv, hd⟩
    have hsub : OverlapBeforeDiagonal s L ≤ StrictOverlapChild s L := fun _ _ h => h.2
    exact ⟨v, Relation.ReflTransGen.mono hsub u v hv, hd⟩

def PatchCoincident (s : α → List α) (P Q : List (IntegralEdge α)) : Prop :=
  ∃ x ∈ P, ∃ y ∈ Q, EdgeCoincident s x y

theorem patchCoincident_iff_overlap_reach (hL : LengthData s L β)
    (P Q : List (IntegralEdge α)) :
    PatchCoincident s P Q ↔
      ∃ x ∈ P, ∃ y ∈ Q, ∃ hx : (overlapOf x y).Interior L,
        ∃ v, Relation.ReflTransGen (OverlapBeforeDiagonal s L)
          ⟨overlapOf x y, hx⟩ v ∧ v.val.Diagonal := by
  unfold PatchCoincident
  simp only [edgeCoincident_iff_overlap_productive hL, overlap_productive_iff_terminal_reach]

/-- The strict filter rules out endpoint-only contact at every depth. -/
theorem touching_edges_not_coincident (hL : LengthData s L β) {x y : IntegralEdge α}
    (h : L y.2 = L x.2 + L (pvec [x.1])) : ¬ EdgeCoincident s x y := by
  intro hc
  obtain ⟨hi, _⟩ := edgeCoincident_iff_overlap_productive hL |>.mp hc
  exact (ne_of_lt (overlapOf_interior_iff.mp hi).2) h

/-- A common half-open point in the inflated parents selects two overlapping children. -/
theorem strictOverlap_exists_child (hL : LengthData s L β) (u : StrictOverlap L) :
    ∃ v, StrictOverlapChild s L u v := by
  let δ := β * L u.val.shift
  let t := max 0 δ
  have hlength (a : α) : L (pvec (s a)) = β * L (pvec [a]) := by
    have h := hL.eigen (pvec [a])
    rw [← pvec_subst] at h
    simpa [subst] using h
  have ht : t < L (pvec (s u.val.top)) := by
    rw [hlength, show t = max 0 δ by rfl, max_lt_iff]
    exact ⟨mul_pos hL.beta_pos (hL.pos _), mul_lt_mul_of_pos_left u.property.2 hL.beta_pos⟩
  have hb : t - δ < L (pvec (s u.val.bottom)) := by
    rw [sub_lt_iff_lt_add, hlength, show t = max 0 δ by rfl, max_lt_iff]
    have hleft := mul_lt_mul_of_pos_left u.property.1 hL.beta_pos
    dsimp [δ]
    constructor <;> linarith [mul_pos hL.beta_pos (hL.pos u.val.bottom)]
  obtain ⟨U, a, U', hU, ha0, ha1⟩ := exists_split _ t (le_max_left _ _) ht
  obtain ⟨V, b, V', hV, hb0, hb1⟩ :=
    exists_split _ (t - δ) (sub_nonneg.mpr (le_max_right _ _)) hb
  let z := incZ s *ᵥ u.val.shift + pvec V - pvec U
  have hz : L z = δ + L (pvec V) - L (pvec U) := by rw [map_sub, map_add, hL.eigen]
  have hi : (OverlapCoordinates.mk a b z).Interior L := by
    change -L (pvec [b]) < L z ∧ L z < L (pvec [a])
    rw [hz]
    exact ⟨by linarith, by linarith⟩
  exact ⟨⟨⟨a, b, z⟩, hi⟩, ⟨U, U', V, V', hU, hV, rfl⟩⟩

section Finite

variable {ν : (α → ℤ) → ℝ} {ρ D B : ℝ}

theorem literalOverlapChild_stable_bound (hc : ContractionData s L ν ρ)
    (hD : ∀ a P, P <+: s a → ν (pvec P) ≤ D)
    {u v : OverlapCoordinates α} (h : LiteralOverlapChild s u v) :
    ν v.shift ≤ ρ * ν u.shift + 2 * D := by
  obtain ⟨U, U', V, V', hU, hV, hz⟩ := h
  rw [hz, sub_eq_add_neg]
  have h1 := hc.add_le (incZ s *ᵥ u.shift + pvec V) (-pvec U)
  have h2 := hc.add_le (incZ s *ᵥ u.shift) (pvec V)
  rw [hc.neg] at h1
  linarith [hc.contract u.shift, hD u.top U ⟨_, hU.symm⟩, hD u.bottom V ⟨_, hV.symm⟩]

theorem overlap_reach_stable_bound (hc : ContractionData s L ν ρ)
    (hD : ∀ a P, P <+: s a → ν (pvec P) ≤ D) (hB : 2 * D ≤ (1 - ρ) * B)
    {u v : StrictOverlap L} (hu : ν u.val.shift ≤ B) (h : OverlapReach s L u v) :
    ν v.val.shift ≤ B := by
  induction h with
  | refl => exact hu
  | tail _ hs ih =>
    have hstep := literalOverlapChild_stable_bound hc hD hs
    have hmul := mul_le_mul_of_nonneg_left ih hc.rho_nonneg
    linarith

theorem overlap_reach_finite (hc : ContractionData s L ν ρ) (u : StrictOverlap L) :
    {v | OverlapReach s L u v}.Finite := by
  obtain ⟨D, hD⟩ := exists_prefix_bound ν s
  let B := max (ν u.val.shift) (2 * D / (1 - ρ))
  have hB : 2 * D ≤ (1 - ρ) * B := by
    rw [mul_comm (1 - ρ) B]
    exact (div_le_iff₀ (sub_pos.mpr hc.rho_lt_one)).mp (le_max_right _ _)
  let : Nonempty α := ⟨u.val.top⟩
  obtain ⟨a, ha⟩ := Finite.exists_max fun a : α => L (pvec [a])
  let f (v : StrictOverlap L) : (α × α) × (α → ℤ) :=
    ((v.val.top, v.val.bottom), v.val.shift)
  have hf : Function.Injective f := by
    rintro ⟨⟨p, q, z⟩, _⟩ ⟨⟨p', q', z'⟩, _⟩ h
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl
  exact ((Set.finite_univ (α := α × α)).prod (hc.proper (L (pvec [a])) B)).preimage hf.injOn
    |>.subset (by
      intro v hv
      have hi := v.property
      change -L (pvec [v.val.bottom]) < L v.val.shift ∧ L v.val.shift < L (pvec [v.val.top]) at hi
      exact ⟨Set.mem_univ _,
        abs_le.mpr ⟨by linarith [hi.1, ha v.val.bottom], by linarith [hi.2, ha v.val.top]⟩,
        overlap_reach_stable_bound hc hD hB (le_max_left _ _) hv⟩)

/-- A nonproductive root has a finite set of descendants closed under all
literal children and containing no diagonal. Such a set also suffices. -/
theorem overlap_not_productive_iff_closed (hc : ContractionData s L ν ρ) (u : StrictOverlap L) :
    ¬ OverlapProductive s L u ↔
      ∃ C : Set (StrictOverlap L), C.Finite ∧ u ∈ C ∧
        (∀ v ∈ C, ¬ v.val.Diagonal) ∧
        (∀ v ∈ C, ∀ w, StrictOverlapChild s L v w → w ∈ C) := by
  constructor
  · intro h
    refine ⟨{v | OverlapReach s L u v}, overlap_reach_finite hc u, .refl, ?_, ?_⟩
    · intro v hv hd
      exact h ⟨v, hv, hd⟩
    · intro v hv w he
      exact (show OverlapReach s L u v from hv).tail he
  · rintro ⟨C, _, hu, hdiagonal, hclosed⟩ ⟨v, hpath, htarget⟩
    have hv : v ∈ C := by
      clear htarget
      induction hpath with
      | refl => exact hu
      | tail _ he ih => exact hclosed _ ih _ he
    exact hdiagonal v hv htarget

/-- The bound on a closed obstruction is uniform in the choice of root.
A minimizer of stable size in the original finite closed set has a child,
giving the bound. Intersecting with the invariant bound preserves closure. -/
theorem all_overlaps_productive_iff_no_bounded_closed (hL : LengthData s L β)
    (hc : ContractionData s L ν ρ) (hD : ∀ a P, P <+: s a → ν (pvec P) ≤ D) :
    (∀ u, OverlapProductive s L u) ↔
      ¬ ∃ C : Set (StrictOverlap L), C.Nonempty ∧ C.Finite ∧
        (∀ v ∈ C, ν v.val.shift ≤ 2 * D / (1 - ρ) ∧ ¬ v.val.Diagonal) ∧
        (∀ v ∈ C, ∀ w, StrictOverlapChild s L v w → w ∈ C) := by
  constructor
  · rintro hall ⟨C, ⟨u, hu⟩, hfin, hstates, hclosed⟩
    have hbad := (overlap_not_productive_iff_closed hc u).mpr
      ⟨C, hfin, hu, fun v hv => (hstates v hv).2, hclosed⟩
    exact hbad (hall u)
  · intro h u
    by_contra hu
    obtain ⟨C, hfin, hu, hdiagonal, hclosed⟩ := (overlap_not_productive_iff_closed hc u).mp hu
    obtain ⟨v, hv, hmin⟩ := Set.exists_min_image C (fun x => ν x.val.shift) hfin ⟨u, hu⟩
    obtain ⟨w, hw⟩ := strictOverlap_exists_child hL v
    have hle := hmin w (hclosed v hv w hw)
    have hstep := literalOverlapChild_stable_bound hc hD hw
    have hρ : 0 < 1 - ρ := sub_pos.mpr hc.rho_lt_one
    have hsmall : ν v.val.shift ≤ 2 * D / (1 - ρ) := (le_div_iff₀ hρ).mpr (by linarith)
    let C' := C ∩ {x : StrictOverlap L | ν x.val.shift ≤ 2 * D / (1 - ρ)}
    refine h ⟨C', ⟨v, hv, hsmall⟩, hfin.subset Set.inter_subset_left, ?_, ?_⟩
    · exact fun x hx => ⟨hx.2, hdiagonal x hx.1⟩
    · intro x hx y he
      refine ⟨hclosed x hx.1 y he, ?_⟩
      have hB : 2 * D ≤ (1 - ρ) * (2 * D / (1 - ρ)) := by
        rw [mul_comm (1 - ρ), div_mul_cancel₀ _ hρ.ne']
      exact overlap_reach_stable_bound hc hD hB hx.2 (.single he)

end Finite

end Psc.GeometricF
