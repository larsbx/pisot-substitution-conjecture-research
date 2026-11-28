/- Independent acceptance types for the beta-numeration route.
Each endpoint must have exactly the stated type, be owned by its compiled
module, and depend only on the standard axioms. Every local constant of every
beta module is audited. Weakened or altered contracts must be refused. -/
import PscVerif.BetaGoldenEndpoint
import PscVerif.BetaMetallicUnique
import PscVerif.BetaMetallicNormalForm
import PscVerif.BetaFamilyFixedWord
import PscVerif.BetaFamilyComplexity
import PscVerif.BetaFamilyXi
import PscVerif.BetaFactorBounded
import PscVerif.BetaGoldenCoding
import PscVerif.BetaGoldenMultiplicity
import PscVerif.BetaMetallicCarry
import PscVerif.BetaMetallicSchmidt
import Lean.Util.CollectAxioms

set_option autoImplicit false

namespace Psc.BetaNumerationAudit

open scoped goldenRatio
open Psc.BetaMetallicUnique (Base EndpointsInitial NormalForm carryPair)
open Psc.BetaFamilyFixedWord (word EventuallyPeriodic)
open Psc.BetaFamilyComplexity (factors E)

def GoldenUniqueType : Prop :=
  ∀ d : ℕ → Bool, Psc.BetaGoldenEndpoint.IsUnique d ↔ d = (fun _ => false) ∨ d = (fun _ => true)

def MetallicUniqueType : Prop :=
  ∀ {m : ℕ} {B : Base m} (d : ℕ → Fin (m + 1)), B.IsUnique d ↔ EndpointsInitial d

def NormalFormType : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → ∀ d : ℕ → Fin (m + 1), EndpointsInitial d ↔ NormalForm d

def UncountableType : Prop := ∀ {m : ℕ}, 3 ≤ m → ∀ B : Base m, ¬ B.uniqueSet.Countable

def CountableTwoType : Prop := ∀ B : Base 2, B.uniqueSet.Countable

def InfiniteTwoType : Prop := ∀ B : Base 2, B.uniqueSet.Infinite

def AperiodicType : Prop := ∀ k : ℕ, 1 ≤ k → ¬ EventuallyPeriodic (word k)

def LinearType : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 1 ≤ n →
    (factors (word k) n).Finite ∧ (factors (word k) n).ncard ≤ 27 * E k ^ 2 * n

universe u in
def BoundedType : Prop :=
  ∀ {β : Type u} (x : ℕ → β) {C : ℕ},
    (∀ n, (factors x n).Finite ∧ (factors x n).ncard ≤ C) → EventuallyPeriodic x

def CodeGreedyType : Prop :=
  ∀ k n : ℕ,
    0 ≤ Psc.BetaGoldenEndpoint.value (Psc.BetaGoldenCoding.gshift (Psc.BetaGoldenCoding.code k) n) ∧
      Psc.BetaGoldenEndpoint.value (Psc.BetaGoldenCoding.gshift (Psc.BetaGoldenCoding.code k) n) < 1 ∧
      ((Psc.BetaGoldenCoding.code k n).toNat : ℤ) =
        ⌊φ * Psc.BetaGoldenEndpoint.value (Psc.BetaGoldenCoding.gshift (Psc.BetaGoldenCoding.code k) n)⌋

def GoldenClassType : Prop :=
  ∀ {x : ℝ}, 0 < x → x < φ →
    ((∃ a b : ℤ, x = a + b * φ) →
        {d : ℕ → Bool | Psc.BetaGoldenEndpoint.value d = x}.Countable ∧
          {d : ℕ → Bool | Psc.BetaGoldenEndpoint.value d = x}.Infinite) ∧
      (¬ (∃ a b : ℤ, x = a + b * φ) →
        ¬ {d : ℕ → Bool | Psc.BetaGoldenEndpoint.value d = x}.Countable)

def SevenType : Prop :=
  ∀ {m : ℕ} (B : Base m) (d e : ℕ → Fin (m + 1)),
    B.value d = B.value e ↔ ∀ n, carryPair d e n ∈ Base.seven m

def ReachType : Prop :=
  ∀ {m : ℕ} (B : Base m), 1 ≤ m → ∀ {q : ℤ × ℤ}, q ∈ Base.seven m →
    ∃ d e : ℕ → Fin (m + 1), B.value d = B.value e ∧ ∃ n, carryPair d e n = q

def SchmidtType : Prop :=
  ∀ {m : ℕ} (B : Base m) (d : ℕ → Fin (m + 1)), (∀ n, B.rem d n < 1) →
    ∀ {a₀ b₀ q : ℤ}, 0 < q → (q : ℝ) * B.value d = a₀ + b₀ * B.beta → EventuallyPeriodic d

def XiNotMemType : Prop :=
  ∀ k m : ℕ, 1 ≤ k → ∀ (hm : 4 ≤ m) (B : Base m),
    ¬ ∃ a b q : ℤ, 0 < q ∧ (q : ℝ) * Psc.BetaFamilyXi.xi k hm B = a + b * B.beta

def XiIrrationalType : Prop :=
  ∀ k m : ℕ, 1 ≤ k → ∀ (hm : 4 ≤ m) (B : Base m), Irrational (Psc.BetaFamilyXi.xi k hm B)

def CodeNotMemType : Prop :=
  ∀ k : ℕ, 1 ≤ k → ¬ ∃ a b q : ℤ, 0 < q ∧
    (q : ℝ) * Psc.BetaGoldenEndpoint.value (Psc.BetaGoldenCoding.code k) = a + b * φ

/-! Altered contracts that the matcher must refuse. -/

def GoldenUniqueFalseOnlyType : Prop :=
  ∀ d : ℕ → Bool, Psc.BetaGoldenEndpoint.IsUnique d ↔ d = (fun _ => false)

def UncountableFromTwoType : Prop := ∀ {m : ℕ}, 2 ≤ m → ∀ B : Base m, ¬ B.uniqueSet.Countable

def AperiodicAllKType : Prop := ∀ k : ℕ, ¬ EventuallyPeriodic (word k)

def SchmidtNonGreedyType : Prop :=
  ∀ {m : ℕ} (B : Base m) (d : ℕ → Fin (m + 1)),
    ∀ {a₀ b₀ q : ℤ}, 0 < q → (q : ℝ) * B.value d = a₀ + b₀ * B.beta → EventuallyPeriodic d

def SevenSomeTimeType : Prop :=
  ∀ {m : ℕ} (B : Base m) (d e : ℕ → Fin (m + 1)),
    B.value d = B.value e ↔ ∃ n, carryPair d e n ∈ Base.seven m

def GoldenClassSwappedType : Prop :=
  ∀ {x : ℝ}, 0 < x → x < φ →
    ((∃ a b : ℤ, x = a + b * φ) → ¬ {d : ℕ → Bool | Psc.BetaGoldenEndpoint.value d = x}.Countable) ∧
      (¬ (∃ a b : ℤ, x = a + b * φ) →
        {d : ℕ → Bool | Psc.BetaGoldenEndpoint.value d = x}.Countable)

theorem wrongTypeControl : True := trivial

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let env ← getEnv
    let modules : Array Name := #[
      `PscVerif.BetaGoldenEndpoint, `PscVerif.BetaMetallicUnique,
      `PscVerif.BetaMetallicNormalForm, `PscVerif.BetaFamilyFixedWord,
      `PscVerif.BetaFamilyComplexity, `PscVerif.BetaFamilyXi, `PscVerif.BetaFactorBounded,
      `PscVerif.BetaGoldenCoding, `PscVerif.BetaGoldenMultiplicity,
      `PscVerif.BetaMetallicCarry, `PscVerif.BetaMetallicSchmidt]
    let endpoints : Array (Name × Name × Name) := #[
      (`Psc.BetaGoldenEndpoint.isUnique_iff, ``GoldenUniqueType, `PscVerif.BetaGoldenEndpoint),
      (`Psc.BetaMetallicUnique.Base.isUnique_iff, ``MetallicUniqueType,
        `PscVerif.BetaMetallicUnique),
      (`Psc.BetaMetallicUnique.endpointsInitial_iff, ``NormalFormType,
        `PscVerif.BetaMetallicNormalForm),
      (`Psc.BetaMetallicUnique.unique_not_countable, ``UncountableType,
        `PscVerif.BetaMetallicNormalForm),
      (`Psc.BetaMetallicUnique.unique_two_countable, ``CountableTwoType,
        `PscVerif.BetaMetallicNormalForm),
      (`Psc.BetaMetallicUnique.unique_two_infinite, ``InfiniteTwoType,
        `PscVerif.BetaMetallicNormalForm),
      (`Psc.BetaFamilyFixedWord.word_not_eventuallyPeriodic, ``AperiodicType,
        `PscVerif.BetaFamilyFixedWord),
      (`Psc.BetaFamilyComplexity.factors_finite_and_linear, ``LinearType,
        `PscVerif.BetaFamilyComplexity),
      (`Psc.BetaFactorBounded.eventuallyPeriodic_of_bounded, ``BoundedType,
        `PscVerif.BetaFactorBounded),
      (`Psc.BetaGoldenCoding.code_greedy, ``CodeGreedyType, `PscVerif.BetaGoldenCoding),
      (`Psc.BetaGoldenMultiplicity.golden_classification, ``GoldenClassType,
        `PscVerif.BetaGoldenMultiplicity),
      (`Psc.BetaMetallicUnique.Base.value_eq_iff_seven, ``SevenType,
        `PscVerif.BetaMetallicCarry),
      (`Psc.BetaMetallicUnique.Base.seven_reachable, ``ReachType, `PscVerif.BetaMetallicCarry),
      (`Psc.BetaMetallicUnique.Base.eventuallyPeriodic_of_mem, ``SchmidtType,
        `PscVerif.BetaMetallicSchmidt),
      (`Psc.BetaMetallicUnique.xi_not_mem, ``XiNotMemType, `PscVerif.BetaMetallicSchmidt),
      (`Psc.BetaMetallicUnique.xi_irrational, ``XiIrrationalType, `PscVerif.BetaMetallicSchmidt),
      (`Psc.BetaMetallicUnique.golden_code_not_mem, ``CodeNotMemType,
        `PscVerif.BetaMetallicSchmidt)]
    let semanticRefusals : Array (Name × Name) := #[
      (`Psc.BetaGoldenEndpoint.isUnique_iff, ``GoldenUniqueFalseOnlyType),
      (`Psc.BetaMetallicUnique.unique_not_countable, ``UncountableFromTwoType),
      (`Psc.BetaFamilyFixedWord.word_not_eventuallyPeriodic, ``AperiodicAllKType),
      (`Psc.BetaMetallicUnique.Base.eventuallyPeriodic_of_mem, ``SchmidtNonGreedyType),
      (`Psc.BetaMetallicUnique.Base.value_eq_iff_seven, ``SevenSomeTimeType),
      (`Psc.BetaGoldenMultiplicity.golden_classification, ``GoldenClassSwappedType)]
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
    let mut totalDeclarations := 0
    let mut totalProofs := 0
    for mod in modules do
      let some index := env.getModuleIdx? mod | throwError "Missing compiled beta module {mod}"
      let data := env.header.moduleData[index.toNat]!
      let mut declarations := 0
      let mut proofs := 0
      for info in data.constants do
        let some owner := env.getModuleIdxFor? info.name | continue
        if owner != index then continue
        if info.isAxiom then throwError "Local beta axiom: {info.name}"
        for ax in ← collectAxioms info.name do
          unless allowed.contains ax do
            throwError "Nonstandard beta axiom in {info.name}: {ax}"
        declarations := declarations + 1
        if info.isTheorem then proofs := proofs + 1
      if declarations == 0 || proofs == 0 then throwError "Empty beta module {mod}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_BETA_MODULE\t{mod}\t{declarations}\t{proofs}"
      totalDeclarations := totalDeclarations + declarations
      totalProofs := totalProofs + proofs
    for (name, expected, mod) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed beta endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "Beta endpoint has no compiled owner: {name}"
      let some index := env.getModuleIdx? mod | throwError "Missing owner module {mod}"
      unless owner == index do throwError "Wrong beta endpoint owner: {name}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_BETA_ENDPOINT\t{name}"
    let missing := `Psc.BetaNumerationAudit.absentEndpoint
    if (env.find? missing).isSome then throwError "Missing-declaration control collision"
    for (_, expected, _) in endpoints do
      if ← matchesType ``wrongTypeControl expected then
        throwError "Beta matcher accepted a wrong-typed theorem"
      if ← matchesType missing expected then
        throwError "Beta matcher accepted a missing declaration"
    for (name, wrong) in semanticRefusals do
      if ← matchesType name wrong then
        throwError "Beta matcher accepted altered contract {wrong} for {name}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_BETA_CONTRACT_REFUSED\t{name}\t{wrong}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_BETA_REFUSAL_CONTROLS\t{2 * endpoints.size + semanticRefusals.size}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_BETA_AUDIT_COMPLETE\t{endpoints.size}\t{totalDeclarations}\t{totalProofs}"

end Psc.BetaNumerationAudit
