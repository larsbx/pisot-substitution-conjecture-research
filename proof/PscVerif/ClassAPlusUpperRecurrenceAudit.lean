/- Independently restated endpoint types and transitive owned-declaration
axiom audit for the actual upper plus-Class-A central recurrence. -/
import PscVerif.ClassAPlusUpperRecurrence
import Lean.Util.CollectAxioms

namespace Psc.ClassAPlusUpperRecurrenceAudit

open Psc.OccurrenceNewborn Psc.OccurrenceTransport Matrix

def literalNearest (A C : ℝ) (a b c : ℤ) : Prop :=
  |(c : ℝ)-(-A*(a : ℝ)+C*(b : ℝ))| < 1/2
def literalOriginal (A C : ℝ) (a b c : ℤ) : Prop :=
  |(c : ℝ)+A*(a : ℝ)+C*(b : ℝ)| < 1/2
def literalTwist (u : ℕ → ℤ) (k : ℕ) : ℤ := (-1)^k*u k
def literalSigma (n d : ℕ) (a : Fin 3) : Word :=
  [if a=1 then 1 else 0] ++
    List.replicate (if a=0 then n+d else if a=1 then n else n+1) 2 ++
    [if a=2 then 1 else 0]
def literalPacket (a b : Fin 3) (p q r : ℤ) : Packet := ⟨a,b,![-p,-q,-r]⟩
def literalReconstruction (a b c : ℤ) : Packet :=
  literalPacket 2 2 b (b-2*a) (c-3*b+2*a)

def CoefficientsType : Prop :=
  ∀ (n J : ℕ) (β : ℝ), 7 ≤ n → 1 ≤ J → J ≤ n+7 →
    (n : ℝ)+4 < β → β < (n : ℝ)+6 →
    β^3-((n : ℝ)+4)*β^2+((J : ℝ)-(n : ℝ)-7)*β-2 = 0 →
    0 < 2/β ∧ 2/β < 1/4 ∧ 0 < β-((n : ℝ)+4) ∧
    0 < (J : ℝ)/(β+1) ∧
    1+2/β-(β-((n : ℝ)+4)) = (J : ℝ)/(β+1) ∧
    (5 ≤ J → 2/β+(β-((n : ℝ)+4)) < 1) ∧
    (J ≤ 4 → 1/2+2*(2/β) < β-((n : ℝ)+4))

def BoundType : Prop :=
  ∀ (n J : ℕ) (β : ℝ), 7 ≤ n → 1 ≤ J → J ≤ n+7 →
    (n : ℝ)+4 < β → β < (n : ℝ)+6 →
    β^3-((n : ℝ)+4)*β^2+((J : ℝ)-(n : ℝ)-7)*β-2 = 0 →
    ∀ u : ℕ → ℤ,
    (∀ k, |(u (k+2) : ℝ)+(2/β)*(u k : ℝ)+
      (β-((n : ℝ)+4))*(u (k+1) : ℝ)| < 1/2) →
    ∀ k, |u k| ≤ ((n : ℤ)+7)*(|u 0|+|u 1|+1)

def ConstantTailType : Prop :=
  ∀ (n J : ℕ) (β : ℝ), 7 ≤ n → 1 ≤ J → J ≤ n+7 →
    (n : ℝ)+4 < β → β < (n : ℝ)+6 →
    β^3-((n : ℝ)+4)*β^2+((J : ℝ)-(n : ℝ)-7)*β-2 = 0 →
    ∀ u : ℕ → ℤ,
    (∀ k, |(u (k+2) : ℝ)-(-(2/β)*(u k : ℝ)+
      (β-((n : ℝ)+4))*(u (k+1) : ℝ))| < 1/2) →
    ∃ N : ℕ, ∃ H : ℤ, |(J : ℝ)/(β+1)*(H : ℝ)| < 1/2 ∧
      ∀ m, u (N+m) = H

def AlternatingTailType : Prop :=
  ∀ (n J : ℕ) (β : ℝ), 7 ≤ n → 1 ≤ J → J ≤ n+7 →
    (n : ℝ)+4 < β → β < (n : ℝ)+6 →
    β^3-((n : ℝ)+4)*β^2+((J : ℝ)-(n : ℝ)-7)*β-2 = 0 →
    ∀ u : ℕ → ℤ,
    (∀ k, |(u (k+2) : ℝ)+(2/β)*(u k : ℝ)+
      (β-((n : ℝ)+4))*(u (k+1) : ℝ)| < 1/2) →
    ∃ N : ℕ, ∃ H : ℤ, 0 ≤ H ∧ (J : ℝ)/(β+1)*(H : ℝ) < 1/2 ∧
      (∀ m, |u (N+m)| = H) ∧ (∀ m, u (N+m+1) = -u (N+m))

def EnergyType : Prop :=
  ∀ A C : ℝ, 0 ≤ A → 3*A ≤ C → ∀ (u : ℕ → ℤ) (T : ℕ),
    0 < T → Function.Periodic u T →
    (∀ k, literalNearest A C (u k) (u (k+1)) (u (k+2))) →
    ∃ H : ℤ, |(1+A-C)*(H : ℝ)| < 1/2 ∧ ∀ k, u k = H

def ShearType : Prop :=
  ∀ A C B : ℝ, 0 ≤ A → 1/2+2*A ≤ C → 1 ≤ 2*(1+A-C)*B →
    ∀ u : ℕ → ℤ,
    (∀ k, literalNearest A C (u k) (u (k+1)) (u (k+2))) →
    |(u 0 : ℝ)| ≤ B → |2*(u 1 : ℝ)-(u 0 : ℝ)| ≤ B →
    ∀ k, |(u k : ℝ)| ≤ B

def ParityType : Prop :=
  ∀ (A C : ℝ) (u : ℕ → ℤ),
    (∀ k, literalOriginal A C (u k) (u (k+1)) (u (k+2))) →
    ∀ k, literalNearest A C (literalTwist u k) (literalTwist u (k+1))
      (literalTwist u (k+2))

def DelayType : Prop :=
  ∀ (u : ℕ → ℤ) (w : ℕ → Packet) (N : ℕ),
    (∀ k, w (k+1) = literalReconstruction (u k) (u (k+1)) (u (k+2))) →
    (∀ m, u (N+m+1) = -u (N+m)) →
    ∀ m, w (N+m+1) = literalPacket 2 2 (u (N+m+1))
      (3*u (N+m+1)) (-6*u (N+m+1))

def CentralCoordinateType : Prop :=
  ∀ (A C : ℝ) (a b r : ℤ),
    |(2+C+A/2)*(b : ℝ)+(1-A/2)*((b-2*a : ℤ) : ℝ)+(r : ℝ)| < 1/2 →
    literalOriginal A C a b (3*b-2*a+r)

def GapRangeType : Prop :=
  ∀ n : ℕ, 7 ≤ n → ∀ β θ : ℝ, 0 < β → β < (n : ℝ)+6 →
    |θ| < 1/2 → ∀ e : ℤ, |β*θ-(e : ℝ)| < 1/2 →
    -(n : ℤ) ≤ e ∧ e ≤ (n : ℤ)

def RunStepType : Prop :=
  ∀ (n d : ℕ) (p q r e : ℤ), -(n : ℤ) ≤ e → e ≤ (n : ℤ) →
    Psc.ClassAZeroDefectEscape.IndexedDigitStep (literalSigma n d) (literalPacket 2 2 p q r)
      (e.toNat+1) ((-e).toNat+1)
      (literalPacket 2 2 (2*p+q+r) (q+r)
        (((n+d : ℕ) : ℤ)*p+(n : ℤ)*q+((n+1 : ℕ) : ℤ)*r-e))

def NonzeroControlType : Prop :=
  (1 : ℝ) < 1/8+1 ∧ literalNearest (1/8) 1 1 1 1 ∧
    literalOriginal (1/8) 1 1 (-1) 1 ∧ (1 : ℤ) ≠ 0

def HalfTieControlType : Prop := ¬literalNearest (1/8) 1 4 0 0

example : CoefficientsType := ClassAPlusUpperRecurrence.family_coefficients
example : BoundType := ClassAPlusUpperRecurrence.forward_integer_bound
example : ConstantTailType := ClassAPlusUpperRecurrence.eventual_constant_tail
example : AlternatingTailType := ClassAPlusUpperRecurrence.eventual_alternating_tail
example : EnergyType := ClassAPlusUpperRecurrence.energy_periodic_constant
example : ShearType := ClassAPlusUpperRecurrence.shear_bound
example : ParityType := ClassAPlusUpperRecurrence.twist_recurrence
example : DelayType := ClassAPlusUpperRecurrence.reconstruction_delay
example : CentralCoordinateType := ClassAPlusUpperRecurrence.central_coordinate_recurrence
example : GapRangeType := ClassAPlusUpperRecurrence.central_gap_in_run
example : RunStepType := ClassAPlusUpperRecurrence.run_gap_digit_step
example : NonzeroControlType := ClassAPlusUpperRecurrence.nonzero_upper_cycle_control
example : HalfTieControlType := ClassAPlusUpperRecurrence.half_tie_control

theorem wrongTypeControl : True := True.intro
theorem extraCoefficients : True → CoefficientsType := fun _ => ClassAPlusUpperRecurrence.family_coefficients
theorem extraBound : True → BoundType := fun _ => ClassAPlusUpperRecurrence.forward_integer_bound
theorem extraConstant : True → ConstantTailType := fun _ => ClassAPlusUpperRecurrence.eventual_constant_tail
theorem extraAlternating : True → AlternatingTailType := fun _ => ClassAPlusUpperRecurrence.eventual_alternating_tail
theorem extraEnergy : True → EnergyType := fun _ => ClassAPlusUpperRecurrence.energy_periodic_constant
theorem extraShear : True → ShearType := fun _ => ClassAPlusUpperRecurrence.shear_bound
theorem extraParity : True → ParityType := fun _ => ClassAPlusUpperRecurrence.twist_recurrence
theorem extraDelay : True → DelayType := fun _ => ClassAPlusUpperRecurrence.reconstruction_delay
theorem extraCentralCoordinate : True → CentralCoordinateType := fun _ => ClassAPlusUpperRecurrence.central_coordinate_recurrence
theorem extraGapRange : True → GapRangeType := fun _ => ClassAPlusUpperRecurrence.central_gap_in_run
theorem extraRunStep : True → RunStepType := fun _ => ClassAPlusUpperRecurrence.run_gap_digit_step
theorem extraNonzero : True → NonzeroControlType := fun _ => ClassAPlusUpperRecurrence.nonzero_upper_cycle_control
theorem extraHalfTie : True → HalfTieControlType := fun _ => ClassAPlusUpperRecurrence.half_tie_control

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let endpoints : Array (Name × Name × Name) := #[
      (``ClassAPlusUpperRecurrence.family_coefficients, ``CoefficientsType, ``extraCoefficients),
      (``ClassAPlusUpperRecurrence.forward_integer_bound, ``BoundType, ``extraBound),
      (``ClassAPlusUpperRecurrence.eventual_constant_tail, ``ConstantTailType, ``extraConstant),
      (``ClassAPlusUpperRecurrence.eventual_alternating_tail, ``AlternatingTailType, ``extraAlternating),
      (``ClassAPlusUpperRecurrence.energy_periodic_constant, ``EnergyType, ``extraEnergy),
      (``ClassAPlusUpperRecurrence.shear_bound, ``ShearType, ``extraShear),
      (``ClassAPlusUpperRecurrence.twist_recurrence, ``ParityType, ``extraParity),
      (``ClassAPlusUpperRecurrence.reconstruction_delay, ``DelayType, ``extraDelay),
      (``ClassAPlusUpperRecurrence.central_coordinate_recurrence, ``CentralCoordinateType, ``extraCentralCoordinate),
      (``ClassAPlusUpperRecurrence.central_gap_in_run, ``GapRangeType, ``extraGapRange),
      (``ClassAPlusUpperRecurrence.run_gap_digit_step, ``RunStepType, ``extraRunStep),
      (``ClassAPlusUpperRecurrence.nonzero_upper_cycle_control, ``NonzeroControlType, ``extraNonzero),
      (``ClassAPlusUpperRecurrence.half_tie_control, ``HalfTieControlType, ``extraHalfTie)]
    let env ← getEnv
    let matchesType (name expected : Name) : Term.TermElabM Bool := do
      let some info := env.find? name | return false
      if !info.isTheorem then return false
      let some expectedInfo := env.find? expected | return false
      if info.levelParams.length != expectedInfo.levelParams.length then return false
      withNewMCtxDepth do
        let declaration ← mkConstWithFreshMVarLevels name
        let declarationType ← inferType declaration
        let expectedType := mkConst expected (expectedInfo.levelParams.map Level.param)
        withTransparency .all <| isDefEq declarationType expectedType
    let allowed := #[`propext, `Classical.choice, `Quot.sound]
    let mod := `PscVerif.ClassAPlusUpperRecurrence
    let some index := env.getModuleIdx? mod
      | throwError "Missing compiled upper-recurrence module"
    let data := env.header.moduleData[index.toNat]!
    let mut declarations := 0
    let mut proofs := 0
    for info in data.constants do
      let some owner := env.getModuleIdxFor? info.name | continue
      if owner != index then continue
      if info.isAxiom then throwError "Local upper-recurrence axiom: {info.name}"
      let axioms ← collectAxioms info.name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Nonstandard upper-recurrence axiom in {info.name}: {ax}"
      declarations := declarations+1
      if info.isTheorem then proofs := proofs+1
    if declarations == 0 then throwError "Empty upper-recurrence module"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_CLASS_A_PLUS_UPPER_RECURRENCE_MODULE\t{mod}\t{declarations}\t{proofs}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_CLASS_A_PLUS_UPPER_RECURRENCE_DECLARATIONS\t1\t{declarations}\t{proofs}"
    for (name, expected, _) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed upper-recurrence endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "Upper-recurrence endpoint has no compiled owner: {name}"
      unless owner == index do throwError "Wrong upper-recurrence endpoint owner: {name}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_CLASS_A_PLUS_UPPER_RECURRENCE_ENDPOINT\t{name}"
    let missing := `Psc.ClassAPlusUpperRecurrenceAudit.absentEndpoint
    if (env.find? missing).isSome then throwError "Missing control name collision"
    for (_, expected, extra) in endpoints do
      if ← matchesType ``wrongTypeControl expected then
        throwError "Upper-recurrence audit accepted a wrong-type theorem"
      if ← matchesType missing expected then
        throwError "Upper-recurrence audit accepted a missing declaration"
      if ← matchesType extra expected then
        throwError "Upper-recurrence audit accepted an extra premise"
    Lean.Core.liftIOCore <| IO.println "PSC_CLASS_A_PLUS_UPPER_RECURRENCE_AUDIT_COMPLETE\t13\t39"

end Psc.ClassAPlusUpperRecurrenceAudit
