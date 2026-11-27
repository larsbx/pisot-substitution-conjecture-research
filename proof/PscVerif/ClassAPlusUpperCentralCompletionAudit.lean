/-
Independent literal contracts for upper central and all-source completion.
Expected types restate the words, complete offsets, both original marked
tracks, the one-step reconstruction delay, and both quantitative budgets.
They are not inferred from the implementation declarations under audit.
Altered-type refusals check exact API identity, not logical inequivalence.
-/
import PscVerif.ClassAPlusUpperCentralCompletion
import PscVerif.ClassAPlusUpperCentralControls
import Lean.Util.CollectAxioms

namespace Psc.ClassAPlusUpperCentralCompletionAudit

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn Psc.OccurrenceTransport
open Psc.ClassAZeroDefectEscape Psc.ClassAMinusPrefixAssembly Matrix

def literalSigma (n d : ℕ) (a : Fin 3) : Word :=
  [if a=1 then 1 else 0] ++
    List.replicate (if a=0 then n+d else if a=1 then n else n+1) 2 ++
    [if a=2 then 1 else 0]

noncomputable def literalLengths (n : ℕ) (β : ℝ) (a : Fin 3) : ℝ :=
  if a=0 then β-(n : ℝ)-2+1/β else if a=1 then 1-1/β else 1

noncomputable def literalShift (n : ℕ) (β : ℝ) (p : Packet) : ℝ :=
  -(literalLengths n β ⬝ᵥ (fun a => (p.delta a : ℝ)))

noncomputable def literalMargin (n : ℕ) (β : ℝ) (p : Packet) : ℝ :=
  if 0 ≤ literalShift n β p then literalLengths n β p.top-literalShift n β p
  else literalLengths n β p.bottom+literalShift n β p

def literalCentral (n : ℕ) (β : ℝ) (p : Packet) : Prop :=
  p.top=2 ∧ p.bottom=2 ∧ |literalShift n β p| < 1/2

def literalPacket (a b : Fin 3) (p q r : ℤ) : Packet := ⟨a,b,![-p,-q,-r]⟩
def literalZero : Packet := literalPacket 2 2 0 0 0
def literalReconstruction (a b c : ℤ) : Packet :=
  literalPacket 2 2 b (b-2*a) (c-3*b+2*a)
def literalOriginal (A C : ℝ) (a b c : ℤ) : Prop :=
  |(c : ℝ)+A*(a : ℝ)+C*(b : ℝ)| < 1/2
def literalNearest (A C : ℝ) (a b c : ℤ) : Prop :=
  |(c : ℝ)-(-A*(a : ℝ)+C*(b : ℝ))| < 1/2

def literalTraces (s : Fin 3 → Word) (source : Packet)
    (xs : List (ℕ × ℕ)) (target : Packet) : Prop :=
  ∃ (top : Mark ((subst s)^[xs.length] [source.top]))
    (bottom : Mark ((subst s)^[xs.length] [source.bottom])),
    MarkTrace s source.top (xs.map Prod.fst) top.before top.letter top.after ∧
    MarkTrace s source.bottom (xs.map Prod.snd) bottom.before bottom.letter bottom.after ∧
    top.letter=target.top ∧ bottom.letter=target.bottom ∧
    target.delta=incidenceZ s^xs.length *ᵥ source.delta+
      (parikhZ top.before-parikhZ bottom.before)

def literalZeroTraces (s : Fin 3 → Word) (source : Packet)
    (xs : List (ℕ × ℕ)) : Prop :=
  ∃ (top : Mark ((subst s)^[xs.length] [source.top]))
    (bottom : Mark ((subst s)^[xs.length] [source.bottom])),
    MarkTrace s source.top (xs.map Prod.fst) top.before top.letter top.after ∧
    MarkTrace s source.bottom (xs.map Prod.snd) bottom.before bottom.letter bottom.after ∧
    top.letter=2 ∧ bottom.letter=2 ∧
    incidenceZ s^xs.length *ᵥ (-source.delta)=parikhZ top.before-parikhZ bottom.before

def literalCompletion (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (source : Packet) (xs : List (ℕ × ℕ)) : Prop :=
  OrderedInteriorPath s ℓ source xs literalZero ∧
  literalTraces s source xs literalZero ∧ literalZeroTraces s source xs

def literalPairs (n : ℕ) (a b : ℤ) : ℕ :=
  (2*(((n : ℤ)+7)*(|a|+|b|+1)).toNat+1)^2

def literalBudget (dropSecond : Bool) (n : ℕ) (p : Packet) : ℕ :=
  literalPairs n (-p.delta 0)
    (if dropSecond then 0 else 2*(-p.delta 0)+(-p.delta 1)+(-p.delta 2)) + 2*n-1

def InflatedNoHalfType : Prop :=
  ∀ {n J : ℕ} {β : ℝ}, ClassAPlusUpperRecurrence.Family n J β →
    ∀ (p : Packet) (z : ℤ), β*literalShift n β p ≠ (z : ℝ)+1/2

def OrbitContract (delay : ℕ) : Prop :=
  ∀ {n J : ℕ} {β : ℝ}, ClassAPlusUpperRecurrence.Family n J β →
    ∀ source : Packet, literalCentral n β source →
    ∃ (u : ℕ → ℤ) (w : ℕ → Packet) (marks : ℕ → ℕ × ℕ),
      w 0=source ∧ (∀ k, literalCentral n β (w k)) ∧
      (∀ k, IndexedDigitStep (literalSigma n (2*n+12-J)) (w k)
        (marks k).1 (marks k).2 (w (k+1))) ∧
      (∀ k, u k = -(w k).delta 0) ∧
      (∀ k, u (k+1)=2*(-(w k).delta 0)+(-(w k).delta 1)+(-(w k).delta 2)) ∧
      (∀ k, w (k+delay)=literalReconstruction (u k) (u (k+1)) (u (k+2))) ∧
      (∀ k, literalOriginal (2/β) (β-((n : ℝ)+4)) (u k) (u (k+1)) (u (k+2)))
def OrbitType : Prop := OrbitContract 1
def OmittedDelayType : Prop := OrbitContract 0

def BoundedTailType : Prop :=
  ∀ (n J : ℕ) (β : ℝ), ClassAPlusUpperRecurrence.Family n J β →
    ∀ u : ℕ → ℤ,
    (∀ k, literalOriginal (2/β) (β-((n : ℝ)+4)) (u k) (u (k+1)) (u (k+2))) →
    ∃ N : ℕ, ∃ H : ℤ, N < literalPairs n (u 0) (u 1) ∧ 0 ≤ H ∧
      (1+2/β-(β-((n : ℝ)+4)))*(H : ℝ) < 1/2 ∧
      (∀ m, |u (N+m)|=H) ∧ (∀ m, u (N+m+1)=-u (N+m))

def literalCycleIndices (n J H : ℕ) : List (ℕ × ℕ) :=
  Nat.rec [] (fun k path =>
    if 3 ≤ J*(k+1) then [(0,J*(k+1)-2),(J*(k+1-1)+4,1)] ++ path
    else if J=1 then [(0,0),(1,1+(n+4)*(k+1)),(1,2*(k+1)+1)]
    else [(0,0),(0,2*n+6),(1,2)]) H

def SignedLengthType : Prop :=
  ∀ (rev : Bool) (n J H : ℕ),
    (if rev then (literalCycleIndices n J H).map Prod.swap
      else literalCycleIndices n J H).length ≤ 2*H+1

def CentralContract (dropSecond omitOriginal : Bool) : Prop :=
  ∀ {n J : ℕ} {β : ℝ}, ClassAPlusUpperRecurrence.Family n J β →
    ∀ source : Packet, literalCentral n β source →
    ∃ xs : List (ℕ × ℕ), xs.length ≤ literalBudget dropSecond n source ∧
      (if omitOriginal then
        OrderedInteriorPath (literalSigma n (2*n+12-J)) (literalLengths n β) source xs literalZero
      else literalCompletion (literalSigma n (2*n+12-J)) (literalLengths n β) source xs)
def CentralType : Prop := CentralContract false false
def DroppedSecondCoordinateType : Prop := CentralContract true false
def DroppedOriginalTracesType : Prop := CentralContract false true

def ClosedCentralType : Prop :=
  ∀ {n J : ℕ} {β : ℝ}, ClassAPlusUpperRecurrence.Family n J β →
    ∀ source : Packet, source.top=2 → source.bottom=2 → |literalShift n β source| ≤ 1/2 →
    ∃ xs : List (ℕ × ℕ), xs.length ≤ literalBudget false n source ∧
      literalCompletion (literalSigma n (2*n+12-J)) (literalLengths n β) source xs

def AllSourceConclusion (slack : ℕ) (omitMinimality : Bool)
    (n d : ℕ) (β : ℝ) (source : Packet) : Prop :=
  ∃ (k : ℕ) (entry : List (ℕ × ℕ)) (middle : Packet) (suffix : List (ℕ × ℕ)),
    4 ≤ β^k*literalMargin n β source ∧
    (if omitMinimality then True else ∀ j < k, β^j*literalMargin n β source < 4) ∧
    entry.length ≤ k+slack ∧ literalCentral n β middle ∧
    OrderedInteriorPath (literalSigma n d) (literalLengths n β) source entry middle ∧
    literalTraces (literalSigma n d) source entry middle ∧
    suffix.length ≤ literalBudget false n middle ∧
    literalCompletion (literalSigma n d) (literalLengths n β) middle suffix ∧
    literalCompletion (literalSigma n d) (literalLengths n β) source (entry++suffix)

def FixedRootContract (slack : ℕ) (omitMinimality : Bool) : Prop :=
  ∀ (n d : ℕ) (β : ℝ), 7 ≤ n → n+5 ≤ d → d ≤ 2*n+11 →
    (n : ℝ)+4 < β → β < (n : ℝ)+6 →
    β^3-((n : ℝ)+4)*β^2+((n : ℝ)+5-(d : ℝ))*β-2=0 →
    ∀ source : Packet, source.Interior (literalLengths n β) →
      AllSourceConclusion slack omitMinimality n d β source
def FixedRootType : Prop := FixedRootContract 1 false
def WeakenedEntryBoundType : Prop := FixedRootContract 2 false
def DroppedMinimalityType : Prop := FixedRootContract 1 true

def RootExistenceType : Prop :=
  ∀ n d : ℕ, 7 ≤ n → n+5 ≤ d → d ≤ 2*n+11 →
    ∃ β : ℝ, (n : ℝ)+4 < β ∧ β < (n : ℝ)+6 ∧
      β^3-((n : ℝ)+4)*β^2+((n : ℝ)+5-(d : ℝ))*β-2=0 ∧
      (∀ a, 0 < literalLengths n β a) ∧
      (∀ a, physicalLength (literalLengths n β) (literalSigma n d a)=β*literalLengths n β a) ∧
      ∀ source : Packet, source.Interior (literalLengths n β) →
        AllSourceConclusion 1 false n d β source

def EmptyZeroType : Prop :=
  ∀ {n J : ℕ} {β : ℝ}, ClassAPlusUpperRecurrence.Family n J β →
    literalCompletion (literalSigma n (2*n+12-J)) (literalLengths n β) literalZero []

def literalDelaySource : Packet := literalPacket 2 2 1 2 (-5)
def literalCycle (H : ℕ) : Packet := literalPacket 2 2 (H : ℤ) (3*(H : ℤ)) (-6*(H : ℤ))
def DelayControlType : Prop :=
  ∀ {n : ℕ} {β : ℝ}, ClassAPlusUpperRecurrence.Family n 1 β →
    literalCentral n β literalDelaySource ∧ literalDelaySource ≠ literalCycle 1 ∧
      (-literalDelaySource.delta 0,
        2*literalDelaySource.delta 0+literalDelaySource.delta 1+literalDelaySource.delta 2)=(1,1) ∧
      IndexedDigitStep (literalSigma n (2*n+12-1)) literalDelaySource 1 1 (literalCycle 1).swap ∧
      literalCentral n β (literalCycle 1).swap

def NotAnyCycleType : Prop :=
  ∀ H : ℤ, literalDelaySource ≠ literalPacket 2 2 H (3*H) (-6*H)

def NonzeroControlType : Prop :=
  (1 : ℝ) < 1/8+1 ∧
    literalNearest (1/8) 1 1 1 1 ∧
    literalOriginal (1/8) 1 1 (-1) 1 ∧ (1 : ℤ) ≠ 0

def HalfTieControlType : Prop := ¬literalNearest (1/8) 1 4 0 0

example : InflatedNoHalfType := ClassAPlusUpperCentralOrbit.inflated_shift_no_half
example : OrbitType := ClassAPlusUpperCentralOrbit.exists_literal_central_orbit
example : BoundedTailType := ClassAPlusUpperCentralBound.bounded_alternating_tail
example : SignedLengthType := ClassAPlusUpperCentralBound.signed_indices_length_le
example : CentralType := ClassAPlusUpperCentralCompletion.central_completion
example : ClosedCentralType := ClassAPlusUpperCentralCompletion.central_completion_closed
example : FixedRootType := ClassAPlusUpperCentralCompletion.all_source_completion_nd
example : RootExistenceType := ClassAPlusUpperCentralCompletion.exists_root_all_source_completion
example : EmptyZeroType := ClassAPlusUpperCentralCompletion.zero_empty_completion
example : DelayControlType := ClassAPlusUpperCentralControls.reconstruction_delay_control
example : NotAnyCycleType := ClassAPlusUpperCentralControls.source_not_full_cycle
example : NonzeroControlType := ClassAPlusUpperCentralControls.retained_nonzero_cycle_control
example : HalfTieControlType := ClassAPlusUpperCentralControls.retained_half_tie_control

theorem wrongTypeControl : True := True.intro
theorem extraInflated : True → InflatedNoHalfType := fun _ => ClassAPlusUpperCentralOrbit.inflated_shift_no_half
theorem extraOrbit : True → OrbitType := fun _ => ClassAPlusUpperCentralOrbit.exists_literal_central_orbit
theorem extraTail : True → BoundedTailType := fun _ => ClassAPlusUpperCentralBound.bounded_alternating_tail
theorem extraLength : True → SignedLengthType := fun _ => ClassAPlusUpperCentralBound.signed_indices_length_le
theorem extraCentral : True → CentralType := fun _ => ClassAPlusUpperCentralCompletion.central_completion
theorem extraClosed : True → ClosedCentralType := fun _ => ClassAPlusUpperCentralCompletion.central_completion_closed
theorem extraFixed : True → FixedRootType := fun _ => ClassAPlusUpperCentralCompletion.all_source_completion_nd
theorem extraRoot : True → RootExistenceType := fun _ => ClassAPlusUpperCentralCompletion.exists_root_all_source_completion
theorem extraZero : True → EmptyZeroType := fun _ => ClassAPlusUpperCentralCompletion.zero_empty_completion
theorem extraDelay : True → DelayControlType := fun _ => ClassAPlusUpperCentralControls.reconstruction_delay_control
theorem extraNotCycle : True → NotAnyCycleType := fun _ => ClassAPlusUpperCentralControls.source_not_full_cycle
theorem extraNonzero : True → NonzeroControlType := fun _ => ClassAPlusUpperCentralControls.retained_nonzero_cycle_control
theorem extraHalfTie : True → HalfTieControlType := fun _ => ClassAPlusUpperCentralControls.retained_half_tie_control

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let orbit := `PscVerif.ClassAPlusUpperCentralOrbit
    let bound := `PscVerif.ClassAPlusUpperCentralBound
    let completion := `PscVerif.ClassAPlusUpperCentralCompletion
    let controls := `PscVerif.ClassAPlusUpperCentralControls
    let modules := #[orbit, bound, completion, controls]
    let endpoints : Array (Name × Name × Name × Name) := #[
      (``ClassAPlusUpperCentralOrbit.inflated_shift_no_half, ``InflatedNoHalfType, ``extraInflated, orbit),
      (``ClassAPlusUpperCentralOrbit.exists_literal_central_orbit, ``OrbitType, ``extraOrbit, orbit),
      (``ClassAPlusUpperCentralBound.bounded_alternating_tail, ``BoundedTailType, ``extraTail, bound),
      (``ClassAPlusUpperCentralBound.signed_indices_length_le, ``SignedLengthType, ``extraLength, bound),
      (``ClassAPlusUpperCentralCompletion.central_completion, ``CentralType, ``extraCentral, completion),
      (``ClassAPlusUpperCentralCompletion.central_completion_closed, ``ClosedCentralType, ``extraClosed, completion),
      (``ClassAPlusUpperCentralCompletion.all_source_completion_nd, ``FixedRootType, ``extraFixed, completion),
      (``ClassAPlusUpperCentralCompletion.exists_root_all_source_completion, ``RootExistenceType, ``extraRoot, completion),
      (``ClassAPlusUpperCentralCompletion.zero_empty_completion, ``EmptyZeroType, ``extraZero, completion),
      (``ClassAPlusUpperCentralControls.reconstruction_delay_control, ``DelayControlType, ``extraDelay, controls),
      (``ClassAPlusUpperCentralControls.source_not_full_cycle, ``NotAnyCycleType, ``extraNotCycle, controls),
      (``ClassAPlusUpperCentralControls.retained_nonzero_cycle_control, ``NonzeroControlType, ``extraNonzero, controls),
      (``ClassAPlusUpperCentralControls.retained_half_tie_control, ``HalfTieControlType, ``extraHalfTie, controls)]
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
    let mut declarations := 0
    let mut proofs := 0
    for mod in modules do
      let some index := env.getModuleIdx? mod
        | throwError "Missing compiled central-completion module: {mod}"
      let mut owned := 0
      let mut ownedProofs := 0
      for info in env.header.moduleData[index.toNat]!.constants do
        if env.getModuleIdxFor? info.name != some index then continue
        if info.isAxiom then throwError "Local central-completion axiom: {info.name}"
        for ax in ← collectAxioms info.name do
          unless allowed.contains ax do
            throwError "Nonstandard central-completion axiom in {info.name}: {ax}"
        owned := owned+1
        if info.isTheorem then ownedProofs := ownedProofs+1
      if owned == 0 then throwError "Empty central-completion module: {mod}"
      declarations := declarations+owned
      proofs := proofs+ownedProofs
      Lean.Core.liftIOCore <| IO.println s!"PSC_UPPER_CENTRAL_MODULE\t{mod}\t{owned}\t{ownedProofs}"
    let missing := `Psc.ClassAPlusUpperCentralCompletionAudit.absentEndpoint
    if (env.find? missing).isSome then throwError "Missing-declaration control collision"
    for (name, expected, extra, mod) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed central-completion endpoint: {name}"
      unless env.getModuleIdxFor? name == env.getModuleIdx? mod do
        throwError "Wrong central-completion endpoint owner: {name}"
      if ← matchesType missing expected then throwError "Matcher accepted a missing declaration"
      if ← matchesType ``wrongTypeControl expected then throwError "Matcher accepted a wrong-type theorem"
      if ← matchesType extra expected then throwError "Matcher accepted an extra premise"
      Lean.Core.liftIOCore <| IO.println s!"PSC_UPPER_CENTRAL_ENDPOINT\t{name}"
    let refusals := #[
      (``ClassAPlusUpperCentralOrbit.exists_literal_central_orbit, ``OmittedDelayType),
      (``ClassAPlusUpperCentralCompletion.central_completion, ``DroppedSecondCoordinateType),
      (``ClassAPlusUpperCentralCompletion.central_completion, ``DroppedOriginalTracesType),
      (``ClassAPlusUpperCentralCompletion.all_source_completion_nd, ``WeakenedEntryBoundType),
      (``ClassAPlusUpperCentralCompletion.all_source_completion_nd, ``DroppedMinimalityType)]
    for (name, wrong) in refusals do
      if ← matchesType name wrong then throwError "Matcher accepted altered contract: {wrong}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_UPPER_CENTRAL_CONTRACT_REFUSED\t{wrong}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_UPPER_CENTRAL_AUDIT_COMPLETE\t{modules.size}\t{declarations}\t{proofs}\t{endpoints.size}\t{3*endpoints.size+refusals.size}"

end Psc.ClassAPlusUpperCentralCompletionAudit
