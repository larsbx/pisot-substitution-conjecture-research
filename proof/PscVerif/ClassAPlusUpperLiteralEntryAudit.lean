/-
Independent literal contracts and recursive axiom audit for upper plus-Class-A
entry. Expected theorem types are written here from words, lengths, full
packet coordinates, both original traces, and the least-power bound. They
are not inferred from the declarations under audit.

Altered-contract refusals check exact API identity; a refused weaker type
is not being asserted mathematically false.
-/
import PscVerif.ClassAPlusUpperEntryBound
import PscVerif.ClassAPlusUpperEntryControls
import Lean.Util.CollectAxioms

namespace Psc.ClassAPlusUpperLiteralEntryAudit

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn
open Psc.OccurrenceTransport Psc.ClassAZeroDefectEscape
open Psc.ClassAMinusPrefixAssembly Matrix Polynomial

/-- Original words in the untruncated n,d parameterization. -/
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

def closedCentral (n : ℕ) (β : ℝ) (p : Packet) : Prop :=
  p.top=2 ∧ p.bottom=2 ∧ |literalShift n β p| ≤ 1/2

def literalSwap (p : Packet) : Packet := ⟨p.bottom,p.top,-p.delta⟩

def literalTraces (s : Fin 3 → Word) (p : Packet)
    (xs : List (ℕ × ℕ)) (q : Packet) : Prop :=
  ∃ (top : Mark ((subst s)^[xs.length] [p.top]))
    (bottom : Mark ((subst s)^[xs.length] [p.bottom])),
    MarkTrace s p.top (xs.map Prod.fst) top.before top.letter top.after ∧
    MarkTrace s p.bottom (xs.map Prod.snd) bottom.before bottom.letter bottom.after ∧
    top.letter=q.top ∧ bottom.letter=q.bottom ∧
    q.delta=incidenceZ s^xs.length *ᵥ p.delta+
      (parikhZ top.before-parikhZ bottom.before)

noncomputable def literalPolynomial (n J : ℕ) : ℚ[X] :=
  X^3-C ((n : ℚ)+4)*X^2+C ((J : ℚ)-(n : ℚ)-7)*X-C 2

def IrreducibilityType : Prop :=
  ∀ n J : ℕ, 7 ≤ n → 1 ≤ J → J ≤ n+7 → Irreducible (literalPolynomial n J)

def NoHalfType : Prop :=
  ∀ (n d : ℕ) (β : ℝ), 7 ≤ n → n+5 ≤ d → d ≤ 2*n+11 →
    (n : ℝ)+4 < β → β < (n : ℝ)+6 →
    β^3-((n : ℝ)+4)*β^2+((n : ℝ)-(d : ℝ)+5)*β-2=0 →
    ∀ (w : Fin 3 → ℤ) (z : ℤ),
    (β-(n : ℝ)-2+1/β)*(w 0 : ℝ)+(1-1/β)*(w 1 : ℝ)+(w 2 : ℝ) ≠
      (z : ℝ)+1/2

def DirectEntryType : Prop :=
  ∀ {n J : ℕ} {β : ℝ}, ClassAPlusUpperRecurrence.Family n J β →
    ∀ p : Packet, 0 ≤ literalShift n β p →
    (literalLengths n β (if p.top=2 then 1 else 0)+
      literalLengths n β (if p.bottom=1 then 1 else 0)+1/2)/β <
      literalLengths n β p.top-literalShift n β p →
    ∃ (i j : ℕ) (q : Packet),
      IndexedDigitStep (literalSigma n (2*n+12-J)) p i j q ∧ literalCentral n β q

/-- The flags are used only to expose independently specified malformed
contracts to the type matcher. The accepted contract uses 1,false,false. -/
def EntryConclusion (slack : ℕ) (closed omitTraces : Bool)
    (n d : ℕ) (β : ℝ) (source : Packet) : Prop :=
  ∃ (k : ℕ) (xs : List (ℕ × ℕ)) (target : Packet),
    4 ≤ β^k*literalMargin n β source ∧
    (∀ j < k, β^j*literalMargin n β source < 4) ∧
    xs.length ≤ k+slack ∧
    (if closed then closedCentral n β target else literalCentral n β target) ∧
    OrderedInteriorPath (literalSigma n d) (literalLengths n β) source xs target ∧
    (if omitTraces then True else literalTraces (literalSigma n d) source xs target)

def FixedRootContract (slack : ℕ) (closed omitTraces : Bool) : Prop :=
  ∀ (n d : ℕ) (β : ℝ), 7 ≤ n → n+5 ≤ d → d ≤ 2*n+11 →
    (n : ℝ)+4 < β → β < (n : ℝ)+6 →
    β^3-((n : ℝ)+4)*β^2+((n : ℝ)+5-(d : ℝ))*β-2=0 →
    ∀ source : Packet, source.Interior (literalLengths n β) →
      EntryConclusion slack closed omitTraces n d β source

def FixedRootType : Prop := FixedRootContract 1 false false

def RootExistenceType : Prop :=
  ∀ n d : ℕ, 7 ≤ n → n+5 ≤ d → d ≤ 2*n+11 →
    ∃ β : ℝ, (n : ℝ)+4 < β ∧ β < (n : ℝ)+6 ∧
      β^3-((n : ℝ)+4)*β^2+((n : ℝ)+5-(d : ℝ))*β-2=0 ∧
      (∀ a, 0 < literalLengths n β a) ∧
      (∀ a, physicalLength (literalLengths n β) (literalSigma n d a)=β*literalLengths n β a) ∧
      ∀ source : Packet, source.Interior (literalLengths n β) →
        EntryConclusion 1 false false n d β source

def SwapTracksType : Prop :=
  ∀ {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ} {p q : Packet} {xs : List (ℕ × ℕ)},
    OrderedInteriorPath s ℓ p xs q → literalTraces s p xs q →
    (xs.map Prod.swap).length=xs.length ∧
    OrderedInteriorPath s ℓ (literalSwap p) (xs.map Prod.swap) (literalSwap q) ∧
    literalTraces s (literalSwap p) (xs.map Prod.swap) (literalSwap q)

def FullOffsetType : Prop :=
  ∀ {s : Fin 3 → Word} {p q : Packet} {xs : List (ℕ × ℕ)},
    literalTraces s p xs q →
    ∃ (top : Mark ((subst s)^[xs.length] [p.top]))
      (bottom : Mark ((subst s)^[xs.length] [p.bottom])),
      MarkTrace s p.top (xs.map Prod.fst) top.before top.letter top.after ∧
      MarkTrace s p.bottom (xs.map Prod.snd) bottom.before bottom.letter bottom.after ∧
      top.letter=q.top ∧ bottom.letter=q.bottom ∧
      -q.delta=incidenceZ s^xs.length *ᵥ (-p.delta)+
        (parikhZ bottom.before-parikhZ top.before)

def literalSource : Packet := ⟨2,1,![0,-1,0]⟩
def literalTarget : Packet := ⟨2,2,![0,0,0]⟩
def literalTopPrefix (n d : ℕ) : Word :=
  subst (literalSigma n d) ([0] ++ List.replicate (n+1) 2) ++ [1]

def OneEdgeImpossibleType : Prop :=
  ∀ {n J : ℕ} {β : ℝ}, ClassAPlusUpperRecurrence.Family n J β →
    ∀ (i j : ℕ) (q : Packet),
    IndexedDigitStep (literalSigma n (2*n+12-J)) literalSource i j q →
      ¬literalCentral n β q

def TwoEdgeStrictType : Prop :=
  ∀ {n J : ℕ} {β : ℝ}, ClassAPlusUpperRecurrence.Family n J β →
    OrderedInteriorPath (literalSigma n (2*n+12-J)) (literalLengths n β)
      literalSource [(n+2,0),(1,2)] literalTarget

def WrongIndexType : Prop :=
  ∀ (n d : ℕ) (q : Packet), q.top=1 →
    ¬IndexedDigitStep (literalSigma n d) literalSource (n+1) 0 q

def PrefixCoordinatesType : Prop :=
  ∀ n d : ℕ, parikhZ (literalTopPrefix n d)=
    ![(n : ℤ)+3,(n : ℤ)+2,(n : ℤ)+(d : ℤ)+((n : ℤ)+1)^2]

def ComposedOffsetType : Prop :=
  ∀ n d : ℕ, incidenceZ (literalSigma n d)^2 *ᵥ ![0,1,0]=
    parikhZ (literalTopPrefix n d)-parikhZ [1,2]

example : IrreducibilityType := ClassAPlusUpperNoHalfTies.polyQ_irreducible
example : NoHalfType := ClassAPlusUpperNoHalfTies.literal_shift_ne_half_integer
example : DirectEntryType := ClassAPlusUpperLiteralEntry.direct_entry
example : FixedRootType := ClassAPlusUpperEntryBound.all_source_entry_nd
example : RootExistenceType := ClassAPlusUpperEntryBound.exists_root_all_source_entry
example : SwapTracksType := ClassAPlusUpperEntryTransport.swap_preserves_count_and_tracks
example : FullOffsetType := ClassAPlusUpperEntryTransport.original_traces_bottom_minus_top
example : OneEdgeImpossibleType := ClassAPlusUpperEntryControls.one_edge_central_impossible
example : TwoEdgeStrictType := ClassAPlusUpperEntryControls.two_edge_strict_path
example : WrongIndexType := ClassAPlusUpperEntryControls.wrong_last_index_rejected
example : PrefixCoordinatesType := ClassAPlusUpperEntryControls.top_prefix_coordinates
example : ComposedOffsetType := ClassAPlusUpperEntryControls.composed_offset_identity

theorem wrongTypeControl : True := True.intro

theorem extraIrreducibility : True → IrreducibilityType :=
  fun _ => ClassAPlusUpperNoHalfTies.polyQ_irreducible
theorem extraNoHalf : True → NoHalfType :=
  fun _ => ClassAPlusUpperNoHalfTies.literal_shift_ne_half_integer
theorem extraDirectEntry : True → DirectEntryType :=
  fun _ => ClassAPlusUpperLiteralEntry.direct_entry
theorem extraFixedRoot : True → FixedRootType :=
  fun _ => ClassAPlusUpperEntryBound.all_source_entry_nd
theorem extraRootExistence : True → RootExistenceType :=
  fun _ => ClassAPlusUpperEntryBound.exists_root_all_source_entry
theorem extraSwapTracks : True → SwapTracksType :=
  fun _ => ClassAPlusUpperEntryTransport.swap_preserves_count_and_tracks
theorem extraFullOffset : True → FullOffsetType :=
  fun _ => ClassAPlusUpperEntryTransport.original_traces_bottom_minus_top
theorem extraOneEdgeImpossible : True → OneEdgeImpossibleType :=
  fun _ => ClassAPlusUpperEntryControls.one_edge_central_impossible
theorem extraTwoEdgeStrict : True → TwoEdgeStrictType :=
  fun _ => ClassAPlusUpperEntryControls.two_edge_strict_path
theorem extraWrongIndex : True → WrongIndexType :=
  fun _ => ClassAPlusUpperEntryControls.wrong_last_index_rejected
theorem extraPrefixCoordinates : True → PrefixCoordinatesType :=
  fun _ => ClassAPlusUpperEntryControls.top_prefix_coordinates
theorem extraComposedOffset : True → ComposedOffsetType :=
  fun _ => ClassAPlusUpperEntryControls.composed_offset_identity

def WeakerDepthBoundType : Prop := FixedRootContract 2 false false
def DroppedOriginalTracesType : Prop := FixedRootContract 1 false true
def ClosedCentralType : Prop := FixedRootContract 1 true false

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let noHalf := `PscVerif.ClassAPlusUpperNoHalfTies
    let transport := `PscVerif.ClassAPlusUpperEntryTransport
    let literal := `PscVerif.ClassAPlusUpperLiteralEntry
    let bound := `PscVerif.ClassAPlusUpperEntryBound
    let controls := `PscVerif.ClassAPlusUpperEntryControls
    let modules := #[noHalf, transport, literal, bound, controls]
    let endpoints : Array (Name × Name × Name × Name) := #[
      (``ClassAPlusUpperNoHalfTies.polyQ_irreducible, ``IrreducibilityType, ``extraIrreducibility, noHalf),
      (``ClassAPlusUpperNoHalfTies.literal_shift_ne_half_integer, ``NoHalfType, ``extraNoHalf, noHalf),
      (``ClassAPlusUpperLiteralEntry.direct_entry, ``DirectEntryType, ``extraDirectEntry, literal),
      (``ClassAPlusUpperEntryBound.all_source_entry_nd, ``FixedRootType, ``extraFixedRoot, bound),
      (``ClassAPlusUpperEntryBound.exists_root_all_source_entry, ``RootExistenceType, ``extraRootExistence, bound),
      (``ClassAPlusUpperEntryTransport.swap_preserves_count_and_tracks, ``SwapTracksType, ``extraSwapTracks, transport),
      (``ClassAPlusUpperEntryTransport.original_traces_bottom_minus_top, ``FullOffsetType, ``extraFullOffset, transport),
      (``ClassAPlusUpperEntryControls.one_edge_central_impossible, ``OneEdgeImpossibleType, ``extraOneEdgeImpossible, controls),
      (``ClassAPlusUpperEntryControls.two_edge_strict_path, ``TwoEdgeStrictType, ``extraTwoEdgeStrict, controls),
      (``ClassAPlusUpperEntryControls.wrong_last_index_rejected, ``WrongIndexType, ``extraWrongIndex, controls),
      (``ClassAPlusUpperEntryControls.top_prefix_coordinates, ``PrefixCoordinatesType, ``extraPrefixCoordinates, controls),
      (``ClassAPlusUpperEntryControls.composed_offset_identity, ``ComposedOffsetType, ``extraComposedOffset, controls)]
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
        | throwError "Missing compiled literal-entry module: {mod}"
      let mut owned := 0
      let mut ownedProofs := 0
      for info in env.header.moduleData[index.toNat]!.constants do
        if env.getModuleIdxFor? info.name != some index then continue
        if info.isAxiom then throwError "Local literal-entry axiom: {info.name}"
        for ax in ← collectAxioms info.name do
          unless allowed.contains ax do
            throwError "Nonstandard literal-entry axiom in {info.name}: {ax}"
        owned := owned+1
        if info.isTheorem then ownedProofs := ownedProofs+1
      if owned == 0 then throwError "Empty literal-entry module: {mod}"
      declarations := declarations+owned
      proofs := proofs+ownedProofs
      Lean.Core.liftIOCore <| IO.println
        s!"PSC_UPPER_LITERAL_MODULE\t{mod}\t{owned}\t{ownedProofs}"
    let missing := `Psc.ClassAPlusUpperLiteralEntryAudit.absentEndpoint
    if (env.find? missing).isSome then throwError "Missing-declaration control collision"
    for (name, expected, extra, mod) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed literal-entry endpoint: {name}"
      unless env.getModuleIdxFor? name == env.getModuleIdx? mod do
        throwError "Wrong literal-entry endpoint owner: {name}"
      if ← matchesType missing expected then
        throwError "Literal-entry matcher accepted a missing declaration"
      if ← matchesType ``wrongTypeControl expected then
        throwError "Literal-entry matcher accepted a wrong-type theorem"
      if ← matchesType extra expected then
        throwError "Literal-entry matcher accepted an extra premise"
      Lean.Core.liftIOCore <| IO.println s!"PSC_UPPER_LITERAL_ENDPOINT\t{name}"
    let refusals := #[``WeakerDepthBoundType, ``DroppedOriginalTracesType, ``ClosedCentralType]
    for wrong in refusals do
      if ← matchesType ``ClassAPlusUpperEntryBound.all_source_entry_nd wrong then
        throwError "Literal-entry matcher accepted altered contract: {wrong}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_UPPER_LITERAL_CONTRACT_REFUSED\t{wrong}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_UPPER_LITERAL_AUDIT_COMPLETE\t{modules.size}\t{declarations}\t{proofs}\t{endpoints.size}\t{3*endpoints.size+refusals.size}"

end Psc.ClassAPlusUpperLiteralEntryAudit
