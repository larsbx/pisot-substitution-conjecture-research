import PscVerif.GeometricFInclusion

/-!
# FC2: the integer edge-state transfer

The geometric input is a bound and an attaining family for the BBK rank in the
zero torus slice. The source proof of that input uses Remark 4.3 and the full
return lattice. The proof of rank invariance between the two BBK strand spaces
is a separate input. This module checks the word and edge identities behind
reflection, reversal of property (F), and the rank reduction to letter families.
-/

namespace Psc.GeometricF

open Matrix Psc.Binomial Psc.Incidence

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Reverse each substitution image. -/
def reverseSubstitution (s : α → List α) : α → List α := fun a => (s a).reverse

omit [DecidableEq α] [Fintype α] in
@[simp] theorem reverseSubstitution_reverse (s : α → List α) :
    reverseSubstitution (reverseSubstitution s) = s := by
  funext a
  simp [reverseSubstitution]

omit [DecidableEq α] [Fintype α] in
theorem subst_reverse (s : α → List α) (w : List α) :
    subst (reverseSubstitution s) w.reverse = (subst s w).reverse := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp [subst_cons, subst_append, reverseSubstitution, ih,
      show subst (reverseSubstitution s) [] = [] from rfl]

omit [DecidableEq α] [Fintype α] in
theorem power_reverseSubstitution (s : α → List α) (n : ℕ) (a : α) :
    power (reverseSubstitution s) n a = (power s n a).reverse := by
  have h (w : List α) :
      (subst (reverseSubstitution s))^[n] w.reverse = ((subst s)^[n] w).reverse := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', ih, subst_reverse]
  simpa [power] using h [a]

omit [Fintype α] in
@[simp] theorem pvec_reverse (w : List α) : pvec w.reverse = pvec w := by
  funext a
  simp [pvec]

omit [Fintype α] in
@[simp] theorem incZ_reverseSubstitution (s : α → List α) :
    incZ (reverseSubstitution s) = incZ s := by
  ext a b
  simp [incZ, inc, reverseSubstitution]

/-- The suffix witness uses the same substituted letter and equal suffix Parikh vectors. -/
def RightStrongCoincidenceWitness (s : α → List α) (a b : α) : Prop :=
  ∃ (n : ℕ) (P Q P' Q' : List α) (c : α), power s n a = P ++ c :: Q ∧
    power s n b = P' ++ c :: Q' ∧ Equiv1 Q Q'

/-- An edge is a label with its integer left endpoint. -/
abbrev IntegralEdge (α : Type*) := α × (α → ℤ)

/-- A labelled occurrence in the inflated edge, with its exact lattice coordinate. -/
def EdgeDescendant (s : α → List α) (n : ℕ) (x y : IntegralEdge α) : Prop :=
  ∃ P Q : List α, power s n x.1 = P ++ y.1 :: Q ∧
    y.2 = incZ s ^ n *ᵥ x.2 + pvec P

def EdgeCoincident (s : α → List α) (x y : IntegralEdge α) : Prop :=
  ∃ n z, EdgeDescendant s n x z ∧ EdgeDescendant s n y z

/-- Left strong coincidence represented by the two origin-anchored edges. -/
abbrev VertexCoincident (s : α → List α) (a b : α) : Prop :=
  EdgeCoincident s (a, 0) (b, 0)

/-- The vector is the left endpoint of the reflected edge, which was the right endpoint. -/
def reflectEdge (x : IntegralEdge α) : IntegralEdge α := (x.1, -x.2 - pvec [x.1])

omit [Fintype α] in
@[simp] theorem reflectEdge_reflectEdge (x : IntegralEdge α) : reflectEdge (reflectEdge x) = x := by
  apply Prod.ext
  · rfl
  · change -(-x.2 - pvec [x.1]) - pvec [x.1] = x.2
    abel

theorem edgeDescendant_reflect {s : α → List α} {n : ℕ} {x y : IntegralEdge α}
    (h : EdgeDescendant s n x y) :
    EdgeDescendant (reverseSubstitution s) n (reflectEdge x) (reflectEdge y) := by
  obtain ⟨P, Q, hw, hy⟩ := h
  refine ⟨Q.reverse, P.reverse, ?_, ?_⟩
  · change power (reverseSubstitution s) n x.1 = Q.reverse ++ y.1 :: P.reverse
    rw [power_reverseSubstitution, hw]
    simp
  · change -y.2 - pvec [y.1] =
      incZ (reverseSubstitution s) ^ n *ᵥ (-x.2 - pvec [x.1]) + pvec Q.reverse
    rw [incZ_reverseSubstitution, Matrix.mulVec_sub, Matrix.mulVec_neg, pvec_reverse,
      hy, ← pvec_iterate, show (subst s)^[n] [x.1] = _ from hw, pvec_append, pvec_cons y.1 Q]
    abel

theorem edgeCoincident_reflect_iff {s : α → List α} {x y : IntegralEdge α} :
    EdgeCoincident (reverseSubstitution s) (reflectEdge x) (reflectEdge y) ↔
      EdgeCoincident s x y := by
  constructor <;> rintro ⟨n, z, hx, hy⟩
  · exact ⟨n, reflectEdge z, by simpa using edgeDescendant_reflect hx,
      by simpa using edgeDescendant_reflect hy⟩
  · exact ⟨n, reflectEdge z, edgeDescendant_reflect hx, edgeDescendant_reflect hy⟩

theorem edgeDescendant_comp {s : α → List α} {m n : ℕ} {x y z : IntegralEdge α}
    (hxy : EdgeDescendant s m x y) (hyz : EdgeDescendant s n y z) :
    EdgeDescendant s (m + n) x z := by
  obtain ⟨P, Q, hw, hy⟩ := hxy
  obtain ⟨U, V, hv, hz⟩ := hyz
  refine ⟨(subst s)^[n] P ++ U, V ++ (subst s)^[n] Q, ?_, ?_⟩
  · rw [power, Nat.add_comm m n, Function.iterate_add_apply]
    change (subst s)^[n] (power s m x.1) = _
    rw [hw, iterate_subst_append, show y.1 :: Q = [y.1] ++ Q from rfl, iterate_subst_append]
    change (subst s)^[n] P ++ (power s n y.1 ++ (subst s)^[n] Q) = _
    simp [hv]
  · rw [hz, hy, Matrix.mulVec_add, Matrix.mulVec_mulVec, pvec_append, pvec_iterate,
      Nat.add_comm m n, pow_add]
    abel

/-- The right-hand proposition unfolds the existing StrongCoincidenceWitness.
Writing it here keeps the integer edge layer independent of the strict-system proof. -/
theorem edgeCoincident_zero_iff {s : α → List α} {a b : α} :
    VertexCoincident s a b ↔
      ∃ (n : ℕ) (P Q P' Q' : List α) (c : α),
        power s n a = P ++ c :: Q ∧ power s n b = P' ++ c :: Q' ∧ Equiv1 P P' := by
  constructor
  · rintro ⟨n, ⟨c, v⟩, ⟨P, Q, ha, hp⟩, ⟨P', Q', hb, hp'⟩⟩
    simp at hp hp'
    exact ⟨n, P, Q, P', Q', c, ha, hb, pvec_eq_iff.mp (hp.symm.trans hp')⟩
  · rintro ⟨n, P, Q, P', Q', c, ha, hb, hp⟩
    refine ⟨n, (c, pvec P), ⟨P, Q, ha, by simp⟩, P', Q', hb, ?_⟩
    simpa using pvec_eq_iff.mpr hp

theorem vertexCoincident_reverse_iff {s : α → List α} {a b : α} :
    VertexCoincident (reverseSubstitution s) a b ↔ RightStrongCoincidenceWitness s a b := by
  rw [edgeCoincident_zero_iff]
  constructor <;> rintro ⟨n, P, Q, P', Q', c, ha, hb, he⟩
  · rw [power_reverseSubstitution] at ha hb
    refine ⟨n, Q.reverse, P.reverse, Q'.reverse, P'.reverse, c, ?_, ?_, ?_⟩
    · simpa using congrArg List.reverse ha
    · simpa using congrArg List.reverse hb
    · simpa only [← pvec_eq_iff, pvec_reverse] using he
  · refine ⟨n, Q.reverse, P.reverse, Q'.reverse, P'.reverse, c, ?_, ?_, ?_⟩
    · rw [power_reverseSubstitution, ha]
      simp
    · rw [power_reverseSubstitution, hb]
      simp
    · simpa only [← pvec_eq_iff, pvec_reverse] using he

def edgeOfState (x : IntegralEdge α) : IntegralEdge α := (x.1, -x.2)

theorem stepN_iff_edgeDescendant {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ}
    {n : ℕ} {x y : IntegralEdge α} (hL : LengthData s L β)
    (hx : IsState L x) (hy : IsState L y) :
    StepN s L n x y ↔ EdgeDescendant s n (edgeOfState x) (edgeOfState y) := by
  rw [← step_power_iff hL hx]
  constructor
  · rintro ⟨P, Q, hw, h, -⟩
    refine ⟨P, Q, hw, ?_⟩
    change -y.2 = incZ s ^ n *ᵥ (-x.2) + pvec P
    rw [incZ_power] at h
    rw [h, Matrix.mulVec_neg]
    abel
  · rintro ⟨P, Q, hw, h⟩
    refine ⟨P, Q, hw, ?_, hy⟩
    change -y.2 = incZ s ^ n *ᵥ (-x.2) + pvec P at h
    rw [Matrix.mulVec_neg] at h
    rw [incZ_power]
    calc
      y.2 = -(-y.2) := by simp
      _ = incZ s ^ n *ᵥ x.2 - pvec P := by rw [h]; abel

def reflectState (x : IntegralEdge α) : IntegralEdge α := (x.1, pvec [x.1] - x.2)

omit [Fintype α] in
theorem reflect_left_vertex_not_state (L : (α → ℤ) →+ ℝ) (a : α) :
    ¬ IsState L (reflectState (a, 0)) := by
  intro h
  exact (lt_irrefl (L (pvec [a]))) (by simpa [reflectState] using h.2)

omit [Fintype α] in
theorem edgeOfState_reflectState (x : IntegralEdge α) :
    edgeOfState (reflectState x) = reflectEdge (edgeOfState x) := by
  apply Prod.ext
  · rfl
  · change -(pvec [x.1] - x.2) = -(-x.2) - pvec [x.1]
    abel

theorem LengthData.reverseSubstitution {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ}
    (hL : LengthData s L β) : LengthData (reverseSubstitution s) L β :=
  ⟨hL.beta_pos, fun v => by simpa using hL.eigen v, hL.pos⟩

theorem ContractionData.reverseSubstitution {s : α → List α} {L : (α → ℤ) →+ ℝ}
    {ν : (α → ℤ) → ℝ} {ρ : ℝ} (h : ContractionData s L ν ρ) :
    ContractionData (reverseSubstitution s) L ν ρ :=
  ⟨h.rho_nonneg, h.rho_lt_one, h.add_le, h.neg, fun v => by simpa using h.contract v, h.proper⟩

/-- A nonzero periodic state on the reversed substitution reflects to an interior periodic
state. The zero-kernel condition supplies strict positivity of its length coordinate. -/
theorem propertyF_reverse_of_propertyF {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ}
    (hL : LengthData s L β) (hzero : ∀ v, L v = 0 → v = 0) (hF : PropertyF s L) :
    PropertyF (reverseSubstitution s) L := by
  intro x hx n hn hperiod
  by_contra hnonzero
  have hpos : 0 < L x.2 := lt_of_le_of_ne hx.1 (fun h => hnonzero (hzero _ h.symm))
  have hlength : L (reflectState x).2 = L (pvec [x.1]) - L x.2 := map_sub L _ _
  have hpos' : 0 < L (reflectState x).2 := by rw [hlength]; exact sub_pos.mpr hx.2
  have hx' : IsState L (reflectState x) :=
    ⟨hpos'.le, by rw [hlength]; exact sub_lt_self _ hpos⟩
  have he := (stepN_iff_edgeDescendant hL.reverseSubstitution hx hx).mp hperiod
  have he' := edgeDescendant_reflect he
  rw [reverseSubstitution_reverse, ← edgeOfState_reflectState] at he'
  have hperiod' := (stepN_iff_edgeDescendant hL hx' hx').mpr he'
  have hz := hF _ hx' n hn hperiod'
  rw [hz, map_zero] at hpos'
  exact lt_irrefl _ hpos'

theorem propertyF_reverse_iff {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ}
    (hL : LengthData s L β) (hzero : ∀ v, L v = 0 → v = 0) :
    PropertyF (reverseSubstitution s) L ↔ PropertyF s L :=
  ⟨fun h => by simpa using propertyF_reverse_of_propertyF hL.reverseSubstitution hzero h,
    propertyF_reverse_of_propertyF hL hzero⟩

/-- A family in the zero torus slice, once the full return lattice identifies it with
the integral left-closed, right-open states. -/
def StateFamily (s : α → List α) (L : (α → ℤ) →+ ℝ) (n : ℕ) : Prop :=
  ∃ x : Fin n → IntegralEdge α, (∀ i, IsState L (x i)) ∧
    Pairwise fun i j => ¬ EdgeCoincident s (edgeOfState (x i)) (edgeOfState (x j))

def LetterFamily (C : α → α → Prop) (n : ℕ) : Prop :=
  ∃ a : Fin n → α, Pairwise fun i j => ¬ C (a i) (a j)

/-- The finite rank interface: attainment and an upper bound on all family sizes. -/
def IsMaximumSize (family : ℕ → Prop) (rank : ℕ) : Prop :=
  family rank ∧ ∀ ⦃n⦄, family n → n ≤ rank

theorem stateFamily_of_leftLetterFamily {s : α → List α} {L : (α → ℤ) →+ ℝ} {n : ℕ}
    (hpos : ∀ a, 0 < L (pvec [a])) (h : LetterFamily (VertexCoincident s) n) :
    StateFamily s L n := by
  obtain ⟨a, ha⟩ := h
  refine ⟨fun i => (a i, 0), fun i => by simpa [IsState] using hpos (a i), ?_⟩
  intro i j hij hc
  exact ha hij (by simpa [VertexCoincident, edgeOfState] using hc)

theorem leftLetterFamily_of_stateFamily {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ}
    {ν : (α → ℤ) → ℝ} {ρ : ℝ} {n : ℕ}
    (hL : LengthData s L β) (hC : ContractionData s L ν ρ) (hF : PropertyF s L)
    (h : StateFamily s L n) : LetterFamily (VertexCoincident s) n := by
  obtain ⟨x, hx, hsep⟩ := h
  choose time a ha using fun i => reaches_vertex_of_propertyF hL hC hF (hx i)
  let N := Finset.univ.sup time
  have hdesc (i : Fin n) : ∃ c : α, EdgeDescendant s N (edgeOfState (x i)) (c, 0) := by
    obtain ⟨y, hy⟩ := stepN_total hL (hx i) N
    have hbound : time i ≤ N := Finset.le_sup (f := time) (Finset.mem_univ i)
    have hzero := stepN_absorb hL.pos (ha i) hbound hy
    have hd := (stepN_iff_edgeDescendant hL (hx i) (stepN_isState (hx i) N hy)).mp hy
    exact ⟨y.1, by simpa [edgeOfState, hzero] using hd⟩
  choose c hc using hdesc
  refine ⟨c, ?_⟩
  intro i j hij hw
  obtain ⟨k, z, hi, hj⟩ := hw
  exact hsep hij ⟨N + k, z, edgeDescendant_comp (hc i) hi, edgeDescendant_comp (hc j) hj⟩

theorem leftRank_of_stateRank {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ}
    {ν : (α → ℤ) → ℝ} {ρ : ℝ} {rank : ℕ}
    (hL : LengthData s L β) (hC : ContractionData s L ν ρ) (hF : PropertyF s L)
    (hRank : IsMaximumSize (StateFamily s L) rank) :
    IsMaximumSize (LetterFamily (VertexCoincident s)) rank := by
  refine ⟨leftLetterFamily_of_stateFamily hL hC hF hRank.1, ?_⟩
  intro n h
  exact hRank.2 (stateFamily_of_leftLetterFamily hL.pos h)

theorem rightLetterFamily_iff_reverse {s : α → List α} {n : ℕ} :
    LetterFamily (RightStrongCoincidenceWitness s) n ↔
      LetterFamily (VertexCoincident (reverseSubstitution s)) n := by
  simp only [LetterFamily, vertexCoincident_reverse_iff]

/-- The lower bounds use the two zero-slice rank bounds and no absorption. -/
theorem fc2_rank_lower_bounds {s : α → List α} {L : (α → ℤ) →+ ℝ}
    {rank l r : ℕ} (hpos : ∀ a, 0 < L (pvec [a]))
    (hRank : IsMaximumSize (StateFamily s L) rank)
    (hRankRev : IsMaximumSize (StateFamily (reverseSubstitution s) L) rank)
    (hl : LetterFamily (VertexCoincident s) l)
    (hr : LetterFamily (RightStrongCoincidenceWitness s) r) : l ≤ rank ∧ r ≤ rank :=
  ⟨hRank.2 (stateFamily_of_leftLetterFamily hpos hl),
    hRankRev.2 (stateFamily_of_leftLetterFamily hpos (rightLetterFamily_iff_reverse.mp hr))⟩

/-- FC2 on (F), conditional on the two zero-slice rank realizations. The common rank
parameter comes from reflection of the full geometric strand spaces. -/
theorem fc2_rank_transfer {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ}
    {ν : (α → ℤ) → ℝ} {ρ : ℝ} {rank : ℕ}
    (hL : LengthData s L β) (hC : ContractionData s L ν ρ)
    (hzero : ∀ v, L v = 0 → v = 0) (hF : PropertyF s L)
    (hRank : IsMaximumSize (StateFamily s L) rank)
    (hRankRev : IsMaximumSize (StateFamily (reverseSubstitution s) L) rank) :
    IsMaximumSize (LetterFamily (VertexCoincident s)) rank ∧
      IsMaximumSize (LetterFamily (RightStrongCoincidenceWitness s)) rank := by
  have hr := leftRank_of_stateRank hL.reverseSubstitution hC.reverseSubstitution
    ((propertyF_reverse_iff hL hzero).mpr hF) hRankRev
  refine ⟨leftRank_of_stateRank hL hC hF hRank, rightLetterFamily_iff_reverse.mpr hr.1, ?_⟩
  intro n h
  exact hr.2 (rightLetterFamily_iff_reverse.mp h)

end Psc.GeometricF
