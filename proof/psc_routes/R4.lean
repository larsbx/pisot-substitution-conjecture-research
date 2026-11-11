import Mathlib
import Lean.Util.CollectAxioms

/-!
# Route R4: conditional separation certificates

This proves only that an offset inside a **certified separating radius**
must be zero. Actual Rauzy overlap offsets, the common vertex-to-common
tile bridge, and a uniform window separation radius are open bindings.
-/
namespace PscRoutes.R4

variable {Offset : Type*} [Zero Offset]

/-- Exact abstract separation interface. Never infer its premise
from Pisot contraction alone. -/
theorem separated_window_forces_zero
    (distance : Offset → ℝ) (radius : ℝ)
    (hseparation : ∀ x : Offset, x ≠ 0 → radius ≤ distance x)
    (x : Offset) (hinside : distance x < radius) : x = 0 := by
  by_contra hx
  have hfar := hseparation x hx
  linarith

/-- Integer toy control: a nonzero integral scalar offset cannot have
absolute value less than one. This says nothing about nonintegral
physical offsets in the Pisot embedding without an independent
trace-dual coordinate certificate. -/
theorem integer_offset_small_implies_zero (z : ℤ)
    (hsmall : |(z : ℝ)| < 1) : z = 0 := by
  have hbounds := abs_lt.mp hsmall
  have hlow : (-1 : ℤ) < z := by exact_mod_cast hbounds.1
  have hhigh : z < (1 : ℤ) := by exact_mod_cast hbounds.2
  omega


/-- A genuine, dimension-independent integer-coordinate separation bound.
It applies to a canonically decoded **integral address vector**, not to
unbounded physical translations or floating-point embeddings. -/
theorem integral_address_small_implies_zero
    {d : ℕ} (address : Fin d → ℤ)
    (hsmall : ∀ i, |((address i : ℤ) : ℝ)| < 1) :
    address = 0 := by
  funext i
  exact integer_offset_small_implies_zero (address i) (hsmall i)


/-- A finite set of independently certified positive *rational*
separations has a common positive rational lower bound. The hard
geometric burden is proving positivity and exhaustiveness of the
actual exact-address candidate set, not this finite minimum lemma. -/
theorem finite_positive_separation_radius
    {Address : Type*} [DecidableEq Address] (distance : Address → ℚ) :
    ∀ S : Finset Address,
      (∀ x ∈ S, 0 < distance x) →
      ∃ delta : ℚ, 0 < delta ∧ ∀ x ∈ S, delta ≤ distance x := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨1, by norm_num, ?_⟩
      simp
  | @insert a s ha ih =>
      intro hpos
      have hapos : 0 < distance a := hpos a (Finset.mem_insert_self a s)
      have hspos : ∀ x ∈ s, 0 < distance x := by
        intro x hx
        exact hpos x (Finset.mem_insert_of_mem hx)
      obtain ⟨delta, hdpos, hmin⟩ := ih hspos
      refine ⟨min delta (distance a), lt_min hdpos hapos, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with hxa | hxs
      · subst x
        exact min_le_right _ _
      · exact (min_le_left _ _).trans (hmin x hxs)


/-- Minimal typed overlap evidence: a canonical integral address and
two explicitly ordered tile labels. No point, geometric angle, physical
embedding, or Rauzy cover is smuggled into this model. -/
structure LabeledOverlapPacket (d : ℕ) (Letter : Type*) where
  address : Fin d → ℤ
  topLabel : Letter
  bottomLabel : Letter

def IsCommonVertex {d : ℕ} {Letter : Type*}
    (packet : LabeledOverlapPacket d Letter) : Prop :=
  packet.address = 0

def IsLabeledCoincidence {d : ℕ} {Letter : Type*}
    (packet : LabeledOverlapPacket d Letter) : Prop :=
  IsCommonVertex packet ∧ packet.topLabel = packet.bottomLabel

/-- Exact small counterexample: a common canonical address with
different labels does not amount to a tile coincidence. -/
theorem zero_address_not_enough_for_labeled_coincidence :
    ∃ packet : LabeledOverlapPacket 1 Bool,
      IsCommonVertex packet ∧ ¬ IsLabeledCoincidence packet := by
  refine ⟨⟨fun _ => 0, true, false⟩, ?_, ?_⟩
  · change (fun _ : Fin 1 => (0 : ℤ)) = (0 : Fin 1 → ℤ)
    funext i
    rfl
  · simp [IsLabeledCoincidence]


/-- Exact trace-dual interface: independently supplied rational encoding
and decoding matrices with a checked left-inverse identity make the
encoded address injective. This is not an assertion that a geometric
projection alone has such a left inverse. -/
theorem trace_dual_matrix_injective
    {d : ℕ} (encode decode : Matrix (Fin d) (Fin d) ℚ)
    (hleft : decode * encode = 1)
    (address : Fin d → ℚ)
    (hzero : encode.mulVec address = 0) : address = 0 := by
  have h := congrArg (fun v => decode.mulVec v) hzero
  rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec,
      Matrix.mulVec_zero] at h
  exact h

/-- Bind an actual integral address to a checked *rational*
trace-dual encoding. The certificate is the exact matrix equation
`decode * encode = I`, not a floating-point singular-value bound. -/
theorem integral_address_of_trace_dual_zero
    {d : ℕ} (encode decode : Matrix (Fin d) (Fin d) ℚ)
    (hleft : decode * encode = 1)
    (address : Fin d → ℤ)
    (hzero : encode.mulVec (fun i => (address i : ℚ)) = 0) :
    address = 0 := by
  have hc : (fun i => (address i : ℚ)) = 0 :=
    trace_dual_matrix_injective encode decode hleft
      (fun i => (address i : ℚ)) hzero
  funext i
  have hi : (address i : ℚ) = 0 := congrFun hc i
  exact_mod_cast hi

end PscRoutes.R4

#print axioms PscRoutes.R4.separated_window_forces_zero
#print axioms PscRoutes.R4.integer_offset_small_implies_zero
#print axioms PscRoutes.R4.integral_address_small_implies_zero
#print axioms PscRoutes.R4.finite_positive_separation_radius
#print axioms PscRoutes.R4.zero_address_not_enough_for_labeled_coincidence
#print axioms PscRoutes.R4.trace_dual_matrix_injective
#print axioms PscRoutes.R4.integral_address_of_trace_dual_zero

/- Fail-closed exact-declaration axiom audit for this standalone branch.
   All declared helper theorems must use only the standard Lean axioms.
   This does not establish a full substitution-to-Lemma refinement. -/
open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`PscRoutes.R4.separated_window_forces_zero, `PscRoutes.R4.integer_offset_small_implies_zero, `PscRoutes.R4.integral_address_small_implies_zero, `PscRoutes.R4.finite_positive_separation_radius, `PscRoutes.R4.zero_address_not_enough_for_labeled_coincidence, `PscRoutes.R4.trace_dual_matrix_injective, `PscRoutes.R4.integral_address_of_trace_dual_zero] do
    let axioms ← collectAxioms name
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Nonstandard axiom in {name}: {ax}"
    liftIO <| IO.println s!"PSC_ROUTE_AXIOMS_OK\t{name}"
