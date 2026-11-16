/-
Exact semantic acceptance for the lower minus-Class-A literal entry increment.
The audit reconstructs image words, packet signs, lengths, strict interiors,
full original-prefix equalities and all public source quantifiers. RootData
and coefficient-parameter structures are checked in both directions against
independently written arithmetic propositions. Actual all-source central
entry is not supplied by this audit or by the conditional assembly endpoint.
-/
import PscVerif.ClassAMinusCentralBridge
import PscVerif.ClassAMinusDensity
import PscVerif.ClassAMinusRootSpectrum
import Lean.Util.CollectAxioms

namespace Psc.ClassAMinusLiteralEntryAudit

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn Psc.OccurrenceTransport Matrix
open Psc.ClassAMinusLiteralArithmetic Psc.ClassAMinusPrefixAssembly

def literalSigma (n d : ℕ) (a : Fin 3) : Word :=
  [if a = 1 then 1 else 0] ++
    List.replicate (if a = 0 then n+d else if a = 1 then n else n-1) 2 ++
    [if a = 2 then 1 else 0]

def literalPacket (a b : Fin 3) (p q r : ℤ) : Packet := ⟨a,b,![-p,-q,-r]⟩

noncomputable def literalLengths (n : ℕ) (β : ℝ) : Fin 3 → ℝ :=
  ![β-(n:ℝ)-1/β, 1+1/β, 1]

def LiteralInterior (ℓ : Fin 3 → ℝ) (p : Packet) : Prop :=
  ∃ x : ℝ, 0 < x ∧ x < ℓ p.top ∧
    0 < x+(ℓ ⬝ᵥ fun a => (p.delta a : ℝ)) ∧
    x+(ℓ ⬝ᵥ fun a => (p.delta a : ℝ)) < ℓ p.bottom

def LiteralInteriorStep (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (p q : Packet) : Prop :=
  (∃ (dt : Mark (s p.top)) (db : Mark (s p.bottom)),
    q = ⟨dt.letter,db.letter,
      incidenceZ s *ᵥ p.delta + (parikhZ dt.before-parikhZ db.before)⟩) ∧
    LiteralInterior ℓ q

/-- Both directions prevent a vacuous or strengthened root interface from
silently preserving downstream expected-type aliases. -/
theorem rootData_semantics (n d : ℕ) (β : ℝ) :
    RootData n d β ↔
      β^3-((n:ℝ)+2)*β^2+((n:ℝ)-(d:ℝ)-1)*β+2 = 0 ∧
        (n:ℝ)+1 < β ∧ β < (n:ℝ)+2 := by
  constructor
  · intro h
    exact ⟨h.cubic_eq_zero,h.lower,h.upper⟩
  · rintro ⟨hc,hl,hu⟩
    exact ⟨hc,hl,hu⟩

theorem coefficient_semantics (A B : ℝ) :
    ClassAMinusConstantRecurrence.Parameters A B ↔
      0 ≤ A ∧ A < 1/2 ∧ 0 < B ∧ A+B < 1 := by
  constructor
  · intro h
    exact ⟨h.anonneg,h.asmall,h.bpos,h.contraction⟩
  · rintro ⟨ha,has,hb,hc⟩
    exact ⟨ha,has,hb,hc⟩

def RootExistsType : Prop :=
  ∀ n d : ℕ, 5 ≤ d → d+1 ≤ n → ∃ β : ℝ, RootData n d β

def ScalingType : Prop :=
  ∀ n d : ℕ, 5 ≤ d → d+1 ≤ n → ∀ β : ℝ, RootData n d β →
    ∀ a, physicalLength (literalLengths n β) (literalSigma n d a) = β*literalLengths n β a

def CoefficientsType : Prop :=
  ∀ n d : ℕ, 5 ≤ d → d+1 ≤ n → ∀ β : ℝ, RootData n d β →
    ClassAMinusConstantRecurrence.Parameters (2/β) ((n:ℝ)+2-β)

def AmplitudeBoundType : Prop :=
  ∀ n d : ℕ, 5 ≤ d → d+1 ≤ n → ∀ β : ℝ, RootData n d β →
    ∀ H : ℤ, |(1-2/β-((n:ℝ)+2-β))*(H:ℝ)| < 1/2 →
      2*(d:ℤ)*|H| ≤ (n:ℤ)

def NoHalfType : Prop :=
  ∀ n d : ℕ, 5 ≤ d → d+1 ≤ n → ∀ β : ℝ, RootData n d β →
    ∀ p q r : ℤ, |(β-(n:ℝ)-1/β)*(p:ℝ)+(1+1/β)*(q:ℝ)+(r:ℝ)| ≠ 1/2

def LiteralCountsType : Prop :=
  ∀ n d : ℕ,
    (∀ b, (literalSigma n d 0).count b = ![2,0,n+d] b) ∧
    (∀ b, (literalSigma n d 1).count b = ![1,1,n] b) ∧
    (∀ b, (literalSigma n d 2).count b = ![1,1,n-1] b)

def DensityType : Prop :=
  ∀ n d : ℕ, 5 ≤ d → d+1 ≤ n → ∀ β : ℝ, RootData n d β → ∀ a,
    (((n:ℝ)-1)/β)*physicalLength (literalLengths n β) (literalSigma n d a) ≤
      ((literalSigma n d a).count 2 : ℝ) ∧
    ((literalSigma n d a).count 0 : ℝ) ≤
      (2/(β*literalLengths n β 0))*physicalLength (literalLengths n β) (literalSigma n d a) ∧
    ((literalSigma n d a).count 1 : ℝ) ≤
      (1/β)*physicalLength (literalLengths n β) (literalSigma n d a)

def DensityReserveType : Prop :=
  ∀ n d : ℕ, 5 ≤ d → d+1 ≤ n → ∀ β : ℝ, RootData n d β →
    1/12 < ((n:ℝ)-1)/β-2*(2/(β*literalLengths n β 0))-2*(1/β)

def PackingType.{u} : Prop :=
  ∀ {α : Type u} (s : Finset α) (pos : α → ℝ) (lo len : ℝ), len < 2 →
    (∀ a ∈ s, lo ≤ pos a ∧ pos a ≤ lo+len) →
    (∀ a ∈ s, ∀ b ∈ s, a ≠ b → 1 ≤ |pos a-pos b|) → s.card ≤ 2

def CountContradictionType : Prop :=
  ∀ n d : ℕ, 5 ≤ d → d+1 ≤ n → ∀ β : ℝ, RootData n d β →
    ∀ J : ℝ, 240*((n:ℝ)+1) ≤ J → ∀ ny nx nc : ℕ,
      (((n:ℝ)-1)/β)*J-2*(β*literalLengths n β 0) ≤ ny →
      (nx:ℝ) ≤ (2/(β*literalLengths n β 0))*J+2*(n+d+2:ℕ) →
      (nc:ℝ) ≤ (1/β)*J+2*(n+d+2:ℕ) →
      ny ≤ 2*nx+2*nc+4 → False

def ThresholdType : Prop :=
  ∀ (n : ℕ) (β ell : ℝ), 1 < β → 0 < ell →
    ∃ m : ℕ, 1 ≤ m ∧ 240*((n:ℝ)+1) ≤ β^m*ell

def PrefixType : Prop :=
  ∀ {s : Fin 3 → Word} {p q : Packet} {xs : List (ℕ × ℕ)},
    OrderedPath s p xs q →
      ∃ (top : Mark ((subst s)^[xs.length] [p.top]))
        (bottom : Mark ((subst s)^[xs.length] [p.bottom])),
        top.letter = q.top ∧ bottom.letter = q.bottom ∧
        q.delta = incidenceZ s^xs.length *ᵥ p.delta +
          (parikhZ top.before-parikhZ bottom.before)

def ZeroPrefixType : Prop :=
  ∀ {s : Fin 3 → Word} {p q : Packet} {xs : List (ℕ × ℕ)},
    OrderedPath s p xs q → q.delta = 0 →
      ∃ (top : Mark ((subst s)^[xs.length] [p.top]))
        (bottom : Mark ((subst s)^[xs.length] [p.bottom])),
        top.letter = q.top ∧ bottom.letter = q.bottom ∧
        incidenceZ s^xs.length *ᵥ (-p.delta) =
          parikhZ top.before-parikhZ bottom.before

def CompositionType : Prop :=
  ∀ {s : Fin 3 → Word} {p q r : Packet} {xs ys : List (ℕ × ℕ)},
    OrderedPath s p xs q → OrderedPath s q ys r → OrderedPath s p (xs++ys) r

def CentralPathType : Prop :=
  ∀ n d : ℕ, 5 ≤ d → d+1 ≤ n → ∀ β : ℝ, RootData n d β → ∀ p q r : ℤ,
    |(β-(n:ℝ)-1/β)*(p:ℝ)+(1+1/β)*(q:ℝ)+(r:ℝ)| ≤ 1/2 →
      LiteralInterior (literalLengths n β) (literalPacket 2 2 p q r) ∧
      Relation.ReflTransGen (LiteralInteriorStep (literalSigma n d) (literalLengths n β))
        (literalPacket 2 2 p q r) (literalPacket 2 2 0 0 0)

def CentralPrefixType : Prop :=
  ∀ n d : ℕ, 5 ≤ d → d+1 ≤ n → ∀ β : ℝ, RootData n d β → ∀ p q r : ℤ,
    |(β-(n:ℝ)-1/β)*(p:ℝ)+(1+1/β)*(q:ℝ)+(r:ℝ)| ≤ 1/2 →
    ∃ xs, OrderedPath (literalSigma n d) (literalPacket 2 2 p q r) xs
        (literalPacket 2 2 0 0 0) ∧
      LiteralInterior (literalLengths n β) (literalPacket 2 2 p q r) ∧
      Relation.ReflTransGen (LiteralInteriorStep (literalSigma n d) (literalLengths n β))
        (literalPacket 2 2 p q r) (literalPacket 2 2 0 0 0) ∧
      ∃ (top : Mark ((subst (literalSigma n d))^[xs.length] [2]))
        (bottom : Mark ((subst (literalSigma n d))^[xs.length] [2])),
        top.letter = 2 ∧ bottom.letter = 2 ∧
        incidenceZ (literalSigma n d)^xs.length *ᵥ ![p,q,r] =
          parikhZ top.before-parikhZ bottom.before

def SourceAssemblyType : Prop :=
  ∀ n d : ℕ, 5 ≤ d → d+1 ≤ n → ∀ β : ℝ, RootData n d β →
    ∀ (source : Packet) (p q r : ℤ) (entry : List (ℕ × ℕ)),
      OrderedPath (literalSigma n d) source entry (literalPacket 2 2 p q r) →
      |(β-(n:ℝ)-1/β)*(p:ℝ)+(1+1/β)*(q:ℝ)+(r:ℝ)| ≤ 1/2 →
      ∃ tail, OrderedPath (literalSigma n d) source (entry++tail) (literalPacket 2 2 0 0 0) ∧
        LiteralInterior (literalLengths n β) source ∧
        Relation.ReflTransGen (LiteralInteriorStep (literalSigma n d) (literalLengths n β))
          source (literalPacket 2 2 0 0 0) ∧
        ∃ (top : Mark ((subst (literalSigma n d))^[(entry++tail).length] [source.top]))
          (bottom : Mark ((subst (literalSigma n d))^[(entry++tail).length] [source.bottom])),
          top.letter = 2 ∧ bottom.letter = 2 ∧
          incidenceZ (literalSigma n d)^(entry++tail).length *ᵥ (-source.delta) =
            parikhZ top.before-parikhZ bottom.before

def InvalidParametersType : Prop :=
  ¬ (5 ≤ (4:ℕ) ∧ 4+1 ≤ (6:ℕ)) ∧
  ¬ (5 ≤ (5:ℕ) ∧ 5+1 ≤ (5:ℕ)) ∧
  ¬ (5 ≤ (7:ℕ) ∧ 7+1 ≤ (6:ℕ))

def IncompletePrefixType : Prop :=
  ∃ (top : Mark ([0,2] : Word)) (bottom : Mark ([1,2] : Word)),
    top.letter = bottom.letter ∧ top.before.length = bottom.before.length ∧
    parikhZ top.before-parikhZ bottom.before ≠ 0

def LiteralIndexedStep (s : Fin 3 → Word) (p : Packet) (i j : ℕ) (q : Packet) : Prop :=
  ∃ (dt : Mark (s p.top)) (db : Mark (s p.bottom)),
    dt.before.length = i ∧ db.before.length = j ∧
    q = ⟨dt.letter,db.letter,incidenceZ s *ᵥ p.delta +
      (parikhZ dt.before-parikhZ db.before)⟩

def NoncomposableType : Prop :=
  LiteralIndexedStep (fun a => [a]) (literalPacket 2 2 0 0 0) 0 0
    (literalPacket 2 2 0 0 0) ∧
  LiteralIndexedStep (fun a => [a]) (literalPacket 2 2 0 1 (-1)) 0 0
    (literalPacket 2 2 0 1 (-1)) ∧
  ¬ OrderedPath (fun a => [a]) (literalPacket 2 2 0 0 0) [(0,0),(0,0)]
    (literalPacket 2 2 0 1 (-1))

def EmptyTranscriptType : Prop :=
  ∀ s : Fin 3 → Word,
    ¬ OrderedPath s (literalPacket 2 2 0 1 (-1)) [] (literalPacket 2 2 0 0 0)

def MixedLetterZeroType : Prop :=
  (literalPacket 0 1 0 0 0).delta = 0 ∧
    ¬ ((literalPacket 0 1 0 0 0).top = (literalPacket 0 1 0 0 0).bottom ∧
       (literalPacket 0 1 0 0 0).delta = 0)

def LengthTwoType : Prop :=
  (0:ℝ) ∈ Set.Icc 0 2 ∧ 1 ∈ Set.Icc (0:ℝ) 2 ∧ 2 ∈ Set.Icc (0:ℝ) 2 ∧
  1 ≤ |(0:ℝ)-1| ∧ 1 ≤ |(0:ℝ)-2| ∧ 1 ≤ |(1:ℝ)-2|

def TracedPrefixType : Prop :=
  ∀ {s : Fin 3 → Word} {p q : Packet} {xs : List (ℕ × ℕ)},
    OrderedPath s p xs q →
      ∃ (top : Mark ((subst s)^[xs.length] [p.top]))
        (bottom : Mark ((subst s)^[xs.length] [p.bottom])),
        MarkTrace s p.top (xs.map Prod.fst) top.before top.letter top.after ∧
        MarkTrace s p.bottom (xs.map Prod.snd) bottom.before bottom.letter bottom.after ∧
        top.letter = q.top ∧ bottom.letter = q.bottom ∧
        q.delta = incidenceZ s^xs.length *ᵥ p.delta +
          (parikhZ top.before-parikhZ bottom.before)

def TracedZeroPrefixType : Prop :=
  ∀ {s : Fin 3 → Word} {p q : Packet} {xs : List (ℕ × ℕ)},
    OrderedPath s p xs q → q.delta = 0 →
      ∃ (top : Mark ((subst s)^[xs.length] [p.top]))
        (bottom : Mark ((subst s)^[xs.length] [p.bottom])),
        MarkTrace s p.top (xs.map Prod.fst) top.before top.letter top.after ∧
        MarkTrace s p.bottom (xs.map Prod.snd) bottom.before bottom.letter bottom.after ∧
        top.letter = q.top ∧ bottom.letter = q.bottom ∧
        incidenceZ s^xs.length *ᵥ (-p.delta) =
          parikhZ top.before-parikhZ bottom.before

def IndexedInteriorType : Prop :=
  ∀ (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ),
    (∀ a, 0 < ℓ a) → 0 < β →
    (∀ a, physicalLength ℓ (s a) = β*ℓ a) →
    ∀ {p q : Packet} {xs : List (ℕ × ℕ)}, OrderedPath s p xs q →
      LiteralInterior ℓ q → OrderedInteriorPath s ℓ p xs q

def WrongTranscriptType : Prop :=
  MarkTrace (fun a => [a]) 2 [0] [] 2 [] ∧
    incidenceZ (fun a => [a])^1 *ᵥ (0 : Fin 3 → ℤ) = parikhZ []-parikhZ [] ∧
    ([0] : List ℕ).length = ([1] : List ℕ).length ∧
    ¬ MarkTrace (fun a => [a]) 2 [1] [] 2 []

def TracedCentralType : Prop :=
  ∀ n d : ℕ, 5 ≤ d → d+1 ≤ n → ∀ β : ℝ, RootData n d β → ∀ p q r : ℤ,
    |(β-(n:ℝ)-1/β)*(p:ℝ)+(1+1/β)*(q:ℝ)+(r:ℝ)| ≤ 1/2 →
    ∃ xs, OrderedInteriorPath (literalSigma n d) (literalLengths n β)
        (literalPacket 2 2 p q r) xs (literalPacket 2 2 0 0 0) ∧
      ∃ (top : Mark ((subst (literalSigma n d))^[xs.length] [2]))
        (bottom : Mark ((subst (literalSigma n d))^[xs.length] [2])),
        MarkTrace (literalSigma n d) 2 (xs.map Prod.fst) top.before top.letter top.after ∧
        MarkTrace (literalSigma n d) 2 (xs.map Prod.snd) bottom.before bottom.letter bottom.after ∧
        top.letter = 2 ∧ bottom.letter = 2 ∧
        incidenceZ (literalSigma n d)^xs.length *ᵥ ![p,q,r] =
          parikhZ top.before-parikhZ bottom.before

def TracedSourceAssemblyType : Prop :=
  ∀ n d : ℕ, 5 ≤ d → d+1 ≤ n → ∀ β : ℝ, RootData n d β →
    ∀ (source : Packet) (p q r : ℤ) (entry : List (ℕ × ℕ)),
      OrderedPath (literalSigma n d) source entry (literalPacket 2 2 p q r) →
      |(β-(n:ℝ)-1/β)*(p:ℝ)+(1+1/β)*(q:ℝ)+(r:ℝ)| ≤ 1/2 →
      ∃ tail, OrderedInteriorPath (literalSigma n d) (literalLengths n β)
          source (entry++tail) (literalPacket 2 2 0 0 0) ∧
        ∃ (top : Mark ((subst (literalSigma n d))^[(entry++tail).length] [source.top]))
          (bottom : Mark ((subst (literalSigma n d))^[(entry++tail).length] [source.bottom])),
          MarkTrace (literalSigma n d) source.top ((entry++tail).map Prod.fst)
            top.before top.letter top.after ∧
          MarkTrace (literalSigma n d) source.bottom ((entry++tail).map Prod.snd)
            bottom.before bottom.letter bottom.after ∧
          top.letter = 2 ∧ bottom.letter = 2 ∧
          incidenceZ (literalSigma n d)^(entry++tail).length *ᵥ (-source.delta) =
            parikhZ top.before-parikhZ bottom.before

def literalRationalMatrix (n d : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  (incidenceZ (literalSigma n d)).map (fun z => (z:ℚ))

noncomputable def literalRationalPolynomial (n d : ℕ) : Polynomial ℚ :=
  Polynomial.X^3-Polynomial.C ((n:ℚ)+2)*Polynomial.X^2+
    Polynomial.C ((n:ℚ)-(d:ℚ)-1)*Polynomial.X+Polynomial.C 2

def CharpolyType : Prop :=
  ∀ n d : ℕ, 1 ≤ n →
    (literalRationalMatrix n d).charpoly = literalRationalPolynomial n d

def EigenrowType : Prop :=
  ∀ n d : ℕ, 5 ≤ d → d+1 ≤ n → ∀ β : ℝ, RootData n d β →
    (∀ a, 0 < literalLengths n β a) ∧
    literalLengths n β ᵥ* (literalRationalMatrix n d).map (fun z => (z:ℝ)) =
      β • literalLengths n β

def OtherRootsType : Prop :=
  ∀ n d : ℕ, 5 ≤ d → d+1 ≤ n → ∀ β : ℝ, RootData n d β →
    1 < β ∧ Polynomial.aeval (β:ℂ) (literalRationalMatrix n d).charpoly = 0 ∧
      ∀ z : ℂ, Polynomial.aeval z (literalRationalMatrix n d).charpoly = 0 →
        z ≠ (β:ℂ) → ‖z‖ < 1

def PisotRootType : Prop :=
  ∀ n d : ℕ, 5 ≤ d → d+1 ≤ n →
    ∃ β : ℝ, RootData n d β ∧ (∀ a, 0 < literalLengths n β a) ∧
      literalLengths n β ᵥ* (literalRationalMatrix n d).map (fun z => (z:ℝ)) =
        β • literalLengths n β ∧
      1 < β ∧ Polynomial.aeval (β:ℂ) (literalRationalMatrix n d).charpoly = 0 ∧
      ∀ z : ℂ, Polynomial.aeval z (literalRationalMatrix n d).charpoly = 0 →
        z ≠ (β:ℂ) → ‖z‖ < 1

example : RootExistsType := ClassAMinusLiteralArithmetic.root_exists
example : ScalingType := ClassAMinusLiteralArithmetic.literal_length_scaling
example : CoefficientsType := ClassAMinusLiteralArithmetic.root_coefficient_parameters
example : AmplitudeBoundType := ClassAMinusLiteralArithmetic.constant_amplitude_run_bound
example : NoHalfType := ClassAMinusNoHalfUnit.physical_abs_ne_half
example : LiteralCountsType := ClassAMinusDensity.literal_counts
example : DensityType := ClassAMinusDensity.literal_one_level_density
example : DensityReserveType := ClassAMinusDensity.literal_density_reserve
example : PackingType := ClassAMinusDensity.short_interval_packing
example : CountContradictionType := ClassAMinusDensity.literal_center_count_contradiction
example : ThresholdType := ClassAMinusDensity.density_threshold_exists
example : PrefixType := ClassAMinusPrefixAssembly.ordered_path_original_prefixes
example : ZeroPrefixType := ClassAMinusPrefixAssembly.ordered_path_zero_original_prefixes
example : CompositionType := ClassAMinusPrefixAssembly.OrderedPath.trans
example : CentralPathType := ClassAMinusCentralBridge.literal_central_composable_path
example : CentralPrefixType := ClassAMinusCentralBridge.literal_central_original_prefixes
example : SourceAssemblyType := ClassAMinusCentralBridge.source_with_central_descendant
example : InvalidParametersType := ClassAMinusCentralBridge.invalid_parameters_control
example : IncompletePrefixType := ClassAMinusPrefixAssembly.incomplete_prefix_control
example : NoncomposableType := ClassAMinusPrefixAssembly.noncomposable_paths_control
example : EmptyTranscriptType := ClassAMinusPrefixAssembly.empty_transcript_control
example : MixedLetterZeroType := ClassAMinusPrefixAssembly.mixed_letter_zero_control
example : LengthTwoType := ClassAMinusDensity.length_two_packing_control
example : CharpolyType := ClassAMinusRootSpectrum.literal_charpoly
example : EigenrowType := ClassAMinusRootSpectrum.literal_positive_eigenrow
example : OtherRootsType := ClassAMinusRootSpectrum.literal_other_roots
example : PisotRootType := ClassAMinusRootSpectrum.literal_pisot_root_exists
example : TracedPrefixType := ClassAMinusPrefixAssembly.ordered_path_traced_original_prefixes
example : TracedZeroPrefixType := ClassAMinusPrefixAssembly.ordered_path_traced_zero_original_prefixes
example : IndexedInteriorType := ClassAMinusPrefixAssembly.ordered_path_indexed_interior
example : WrongTranscriptType := ClassAMinusPrefixAssembly.wrong_transcript_control
example : TracedCentralType := ClassAMinusCentralBridge.literal_central_traced_prefixes
example : TracedSourceAssemblyType := ClassAMinusCentralBridge.source_with_traced_central_descendant

theorem wrongTypeControl : True := True.intro
theorem extraRootExistsType : True → RootExistsType := fun _ => ClassAMinusLiteralArithmetic.root_exists
theorem extraScalingType : True → ScalingType := fun _ => ClassAMinusLiteralArithmetic.literal_length_scaling
theorem extraCoefficientsType : True → CoefficientsType := fun _ => ClassAMinusLiteralArithmetic.root_coefficient_parameters
theorem extraAmplitudeBoundType : True → AmplitudeBoundType := fun _ => ClassAMinusLiteralArithmetic.constant_amplitude_run_bound
theorem extraNoHalfType : True → NoHalfType := fun _ => ClassAMinusNoHalfUnit.physical_abs_ne_half
theorem extraLiteralCountsType : True → LiteralCountsType := fun _ => ClassAMinusDensity.literal_counts
theorem extraDensityType : True → DensityType := fun _ => ClassAMinusDensity.literal_one_level_density
theorem extraDensityReserveType : True → DensityReserveType := fun _ => ClassAMinusDensity.literal_density_reserve
theorem extraPackingType : True → PackingType := fun _ => ClassAMinusDensity.short_interval_packing
theorem extraCountContradictionType : True → CountContradictionType := fun _ => ClassAMinusDensity.literal_center_count_contradiction
theorem extraThresholdType : True → ThresholdType := fun _ => ClassAMinusDensity.density_threshold_exists
theorem extraPrefixType : True → PrefixType := fun _ => ClassAMinusPrefixAssembly.ordered_path_original_prefixes
theorem extraZeroPrefixType : True → ZeroPrefixType := fun _ => ClassAMinusPrefixAssembly.ordered_path_zero_original_prefixes
theorem extraCompositionType : True → CompositionType := fun _ => ClassAMinusPrefixAssembly.OrderedPath.trans
theorem extraCentralPathType : True → CentralPathType := fun _ => ClassAMinusCentralBridge.literal_central_composable_path
theorem extraCentralPrefixType : True → CentralPrefixType := fun _ => ClassAMinusCentralBridge.literal_central_original_prefixes
theorem extraSourceAssemblyType : True → SourceAssemblyType := fun _ => ClassAMinusCentralBridge.source_with_central_descendant
theorem extraInvalidParametersType : True → InvalidParametersType := fun _ => ClassAMinusCentralBridge.invalid_parameters_control
theorem extraIncompletePrefixType : True → IncompletePrefixType := fun _ => ClassAMinusPrefixAssembly.incomplete_prefix_control
theorem extraNoncomposableType : True → NoncomposableType := fun _ => ClassAMinusPrefixAssembly.noncomposable_paths_control
theorem extraEmptyTranscriptType : True → EmptyTranscriptType := fun _ => ClassAMinusPrefixAssembly.empty_transcript_control
theorem extraMixedLetterZeroType : True → MixedLetterZeroType := fun _ => ClassAMinusPrefixAssembly.mixed_letter_zero_control
theorem extraLengthTwoType : True → LengthTwoType := fun _ => ClassAMinusDensity.length_two_packing_control
theorem extraCharpolyType : True → CharpolyType := fun _ => ClassAMinusRootSpectrum.literal_charpoly
theorem extraEigenrowType : True → EigenrowType := fun _ => ClassAMinusRootSpectrum.literal_positive_eigenrow
theorem extraOtherRootsType : True → OtherRootsType := fun _ => ClassAMinusRootSpectrum.literal_other_roots
theorem extraPisotRootType : True → PisotRootType := fun _ => ClassAMinusRootSpectrum.literal_pisot_root_exists
theorem extraTracedPrefixType : True → TracedPrefixType :=
  fun _ => ClassAMinusPrefixAssembly.ordered_path_traced_original_prefixes
theorem extraTracedZeroPrefixType : True → TracedZeroPrefixType :=
  fun _ => ClassAMinusPrefixAssembly.ordered_path_traced_zero_original_prefixes
theorem extraIndexedInteriorType : True → IndexedInteriorType :=
  fun _ => ClassAMinusPrefixAssembly.ordered_path_indexed_interior
theorem extraWrongTranscriptType : True → WrongTranscriptType :=
  fun _ => ClassAMinusPrefixAssembly.wrong_transcript_control
theorem extraTracedCentralType : True → TracedCentralType :=
  fun _ => ClassAMinusCentralBridge.literal_central_traced_prefixes
theorem extraTracedSourceAssemblyType : True → TracedSourceAssemblyType :=
  fun _ => ClassAMinusCentralBridge.source_with_traced_central_descendant

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let endpoints : Array (Name × Name × Name × Name) := #[
      (``ClassAMinusLiteralArithmetic.root_exists, ``RootExistsType, ``extraRootExistsType, `PscVerif.ClassAMinusLiteralArithmetic),
      (``ClassAMinusLiteralArithmetic.literal_length_scaling, ``ScalingType, ``extraScalingType, `PscVerif.ClassAMinusLiteralArithmetic),
      (``ClassAMinusLiteralArithmetic.root_coefficient_parameters, ``CoefficientsType, ``extraCoefficientsType, `PscVerif.ClassAMinusLiteralArithmetic),
      (``ClassAMinusLiteralArithmetic.constant_amplitude_run_bound, ``AmplitudeBoundType, ``extraAmplitudeBoundType, `PscVerif.ClassAMinusLiteralArithmetic),
      (``ClassAMinusNoHalfUnit.physical_abs_ne_half, ``NoHalfType, ``extraNoHalfType, `PscVerif.ClassAMinusNoHalfUnit),
      (``ClassAMinusDensity.literal_counts, ``LiteralCountsType, ``extraLiteralCountsType, `PscVerif.ClassAMinusDensity),
      (``ClassAMinusDensity.literal_one_level_density, ``DensityType, ``extraDensityType, `PscVerif.ClassAMinusDensity),
      (``ClassAMinusDensity.literal_density_reserve, ``DensityReserveType, ``extraDensityReserveType, `PscVerif.ClassAMinusDensity),
      (``ClassAMinusDensity.short_interval_packing, ``PackingType, ``extraPackingType, `PscVerif.ClassAMinusDensity),
      (``ClassAMinusDensity.literal_center_count_contradiction, ``CountContradictionType, ``extraCountContradictionType, `PscVerif.ClassAMinusDensity),
      (``ClassAMinusDensity.density_threshold_exists, ``ThresholdType, ``extraThresholdType, `PscVerif.ClassAMinusDensity),
      (``ClassAMinusPrefixAssembly.ordered_path_original_prefixes, ``PrefixType, ``extraPrefixType, `PscVerif.ClassAMinusPrefixAssembly),
      (``ClassAMinusPrefixAssembly.ordered_path_zero_original_prefixes, ``ZeroPrefixType, ``extraZeroPrefixType, `PscVerif.ClassAMinusPrefixAssembly),
      (``ClassAMinusPrefixAssembly.OrderedPath.trans, ``CompositionType, ``extraCompositionType, `PscVerif.ClassAMinusPrefixAssembly),
      (``ClassAMinusCentralBridge.literal_central_composable_path, ``CentralPathType, ``extraCentralPathType, `PscVerif.ClassAMinusCentralBridge),
      (``ClassAMinusCentralBridge.literal_central_original_prefixes, ``CentralPrefixType, ``extraCentralPrefixType, `PscVerif.ClassAMinusCentralBridge),
      (``ClassAMinusCentralBridge.source_with_central_descendant, ``SourceAssemblyType, ``extraSourceAssemblyType, `PscVerif.ClassAMinusCentralBridge),
      (``ClassAMinusCentralBridge.invalid_parameters_control, ``InvalidParametersType, ``extraInvalidParametersType, `PscVerif.ClassAMinusCentralBridge),
      (``ClassAMinusPrefixAssembly.incomplete_prefix_control, ``IncompletePrefixType, ``extraIncompletePrefixType, `PscVerif.ClassAMinusPrefixAssembly),
      (``ClassAMinusPrefixAssembly.noncomposable_paths_control, ``NoncomposableType, ``extraNoncomposableType, `PscVerif.ClassAMinusPrefixAssembly),
      (``ClassAMinusPrefixAssembly.empty_transcript_control, ``EmptyTranscriptType, ``extraEmptyTranscriptType, `PscVerif.ClassAMinusPrefixAssembly),
      (``ClassAMinusPrefixAssembly.mixed_letter_zero_control, ``MixedLetterZeroType, ``extraMixedLetterZeroType, `PscVerif.ClassAMinusPrefixAssembly),
      (``ClassAMinusDensity.length_two_packing_control, ``LengthTwoType, ``extraLengthTwoType, `PscVerif.ClassAMinusDensity),
      (``ClassAMinusRootSpectrum.literal_charpoly, ``CharpolyType, ``extraCharpolyType, `PscVerif.ClassAMinusRootSpectrum),
      (``ClassAMinusRootSpectrum.literal_positive_eigenrow, ``EigenrowType, ``extraEigenrowType, `PscVerif.ClassAMinusRootSpectrum),
      (``ClassAMinusRootSpectrum.literal_other_roots, ``OtherRootsType, ``extraOtherRootsType, `PscVerif.ClassAMinusRootSpectrum),
      (``ClassAMinusRootSpectrum.literal_pisot_root_exists, ``PisotRootType, ``extraPisotRootType, `PscVerif.ClassAMinusRootSpectrum),
      (``ClassAMinusPrefixAssembly.ordered_path_traced_original_prefixes, ``TracedPrefixType, ``extraTracedPrefixType, `PscVerif.ClassAMinusPrefixAssembly),
      (``ClassAMinusPrefixAssembly.ordered_path_traced_zero_original_prefixes, ``TracedZeroPrefixType, ``extraTracedZeroPrefixType, `PscVerif.ClassAMinusPrefixAssembly),
      (``ClassAMinusPrefixAssembly.ordered_path_indexed_interior, ``IndexedInteriorType, ``extraIndexedInteriorType, `PscVerif.ClassAMinusPrefixAssembly),
      (``ClassAMinusPrefixAssembly.wrong_transcript_control, ``WrongTranscriptType, ``extraWrongTranscriptType, `PscVerif.ClassAMinusPrefixAssembly),
      (``ClassAMinusCentralBridge.literal_central_traced_prefixes, ``TracedCentralType, ``extraTracedCentralType, `PscVerif.ClassAMinusCentralBridge),
      (``ClassAMinusCentralBridge.source_with_traced_central_descendant, ``TracedSourceAssemblyType, ``extraTracedSourceAssemblyType, `PscVerif.ClassAMinusCentralBridge)]
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
    let modules := #[`PscVerif.ClassAMinusLiteralArithmetic,
      `PscVerif.ClassAMinusNoHalfUnit, `PscVerif.ClassAMinusDensity,
      `PscVerif.ClassAMinusPrefixAssembly, `PscVerif.ClassAMinusCentralBridge,
      `PscVerif.ClassAMinusRootSpectrum]
    let mut totalDeclarations := 0
    let mut totalProofs := 0
    for mod in modules do
      let some index := env.getModuleIdx? mod
        | throwError "Missing compiled literal-entry module: {mod}"
      let data := env.header.moduleData[index.toNat]!
      let mut declarations := 0
      let mut proofs := 0
      for info in data.constants do
        let some owner := env.getModuleIdxFor? info.name | continue
        if owner != index then continue
        if info.isAxiom then throwError "Local literal-entry axiom: {info.name}"
        let axioms ← collectAxioms info.name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Nonstandard literal-entry axiom in {info.name}: {ax}"
        declarations := declarations + 1
        if info.isTheorem then proofs := proofs + 1
      if declarations == 0 then throwError "Empty compiled literal-entry module: {mod}"
      totalDeclarations := totalDeclarations + declarations
      totalProofs := totalProofs + proofs
      Lean.Core.liftIOCore <| IO.println
        s!"PSC_CLASS_A_LITERAL_ENTRY_MODULE\t{mod}\t{declarations}\t{proofs}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_CLASS_A_LITERAL_ENTRY_DECLARATIONS\t{modules.size}\t{totalDeclarations}\t{totalProofs}"
    for (name, expected, _, mod) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed literal-entry endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "Literal-entry endpoint has no imported owner: {name}"
      let some expectedOwner := env.getModuleIdx? mod
        | throwError "Literal-entry endpoint module missing: {mod}"
      unless owner == expectedOwner do
        throwError "Wrong literal-entry endpoint owner: {name}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_CLASS_A_LITERAL_ENTRY_ENDPOINT\t{name}"
    let missing := `Psc.ClassAMinusLiteralEntryAudit.absentEndpoint
    if (env.find? missing).isSome then throwError "Missing control name collision"
    for (_, expected, extra, _) in endpoints do
      if ← matchesType ``wrongTypeControl expected then
        throwError "Literal-entry audit accepted a wrong-type theorem: {expected}"
      if ← matchesType missing expected then
        throwError "Literal-entry audit accepted a missing declaration: {expected}"
      if ← matchesType extra expected then
        throwError "Literal-entry audit accepted an extra premise: {expected}"
      for name in #[extra, ``wrongTypeControl] do
        let axioms ← collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Nonstandard literal-entry control axiom in {name}: {ax}"
    for name in #[``rootData_semantics, ``coefficient_semantics] do
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Nonstandard semantic-interface axiom in {name}: {ax}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_CLASS_A_LITERAL_ENTRY_AUDIT_COMPLETE\t{endpoints.size}\t{3*endpoints.size}"


end Psc.ClassAMinusLiteralEntryAudit
