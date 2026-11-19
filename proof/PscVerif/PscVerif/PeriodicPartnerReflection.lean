/-
# Reflection of the periodic-partner branch criterion

This module checks the left/right orientation change in Lemma E.  Physical
positions are reflected by `y ↦ -y`; consequently the translated action is
`t ↦ translate (-t)`.  A starting label on the original line becomes an
ending label in the reflected coordinates.  The endpoint map `g` is supplied
for that starting-label dynamics (the first-letter map in the tiling use).

Only the conditional local contracts are transferred.  No legal tiling hull,
geometric reflection map, or geometric realization is asserted as an axiom.
The external BDS and R4 inputs remain explicit after orientation transfer.
See `docs/c4-periodic-partner-formalization-stop-go-2026-11-19.md`.
-/
import PscVerif.PeriodicPartnerDynamics

namespace Psc.PeriodicPartnerReflection

open Function Psc.PeriodicPartnerDynamics

/-- Translation by `t` in reflected coordinates means translation by `-t`
in the original coordinates. -/
def reflectedTranslation {X : Type*} (translate : ℝ → X → X) : ℝ → X → X :=
  fun t S => translate (-t) S

/-- A left ray becomes a right ray after the physical coordinate is negated. -/
def reflectedAgreement {X : Type*} (AgreeLeft : X → X → ℝ → Prop) :
    X → X → ℝ → Prop := fun S U y => AgreeLeft S U (-y)

/-- Original starting labels are reflected ending labels. -/
def reflectedEndpoint {X α : Type*} (StartsAt : X → ℝ → α → Prop) :
    X → ℝ → α → Prop := fun S y b => StartsAt S (-y) b

def LeftAsymptotic {X : Type*} (AgreeLeft : X → X → ℝ → Prop) (S U : X) : Prop :=
  ∃ y, AgreeLeft S U y

/-- A left branch has a common left ray and different labels starting at
the branch location. -/
def LeftBranchAt {X α : Type*} (AgreeLeft : X → X → ℝ → Prop)
    (StartsAt : X → ℝ → α → Prop) (S U : X) (y : ℝ) (b c : α) : Prop :=
  AgreeLeft S U y ∧ StartsAt S y b ∧ StartsAt U y c ∧ b ≠ c

/-- The left-oriented local contract.  Agreement ending strictly after a
common starting endpoint forces the two labels there to agree. -/
structure LeftBranchLaws {X α : Type*} (f : X → X) (translate : ℝ → X → X)
    (β : ℝ) (g : α → α) (AgreeLeft : X → X → ℝ → Prop)
    (StartsAt : X → ℝ → α → Prop) : Prop where
  translate_zero : ∀ S, translate 0 S = S
  start_unique : ∀ {S y b c}, StartsAt S y b → StartsAt S y c → b = c
  agree_start : ∀ {S U r y b c}, AgreeLeft S U r → y < r →
    StartsAt S y b → StartsAt U y c → b = c
  agree_translate : ∀ {S U y} (t : ℝ), AgreeLeft S U y →
    AgreeLeft (translate t S) (translate t U) (y - t)
  start_translate : ∀ {S y b} (t : ℝ), StartsAt S y b →
    StartsAt (translate t S) (y - t) b
  agree_inflate : ∀ {S U y}, AgreeLeft S U y → AgreeLeft (f S) (f U) (β * y)
  start_inflate : ∀ {S y b}, StartsAt S y b → StartsAt (f S) (β * y) (g b)

/-- Every left local law gives the corresponding right local law in
reflected coordinates; the change in the translation parameter is proved. -/
theorem LeftBranchLaws.toRightBranchLaws {X α : Type*}
    {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : α → α}
    {AgreeLeft : X → X → ℝ → Prop} {StartsAt : X → ℝ → α → Prop}
    (laws : LeftBranchLaws f translate β g AgreeLeft StartsAt) :
    RightBranchLaws f (reflectedTranslation translate) β g
      (reflectedAgreement AgreeLeft) (reflectedEndpoint StartsAt) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S
    simpa only [reflectedTranslation, neg_zero] using laws.translate_zero S
  · intro S y b c hb hc
    exact laws.start_unique hb hc
  · intro S U r y b c hagree hlt hb hc
    exact laws.agree_start hagree (neg_lt_neg hlt) hb hc
  · intro S U y t hagree
    simpa [reflectedTranslation, reflectedAgreement, sub_eq_add_neg, add_comm] using
      laws.agree_translate (-t) hagree
  · intro S y b t hstart
    simpa [reflectedTranslation, reflectedEndpoint, sub_eq_add_neg, add_comm] using
      laws.start_translate (-t) hstart
  · intro S U y hagree
    simpa only [reflectedAgreement, mul_neg] using laws.agree_inflate hagree
  · intro S y b hstart
    simpa only [reflectedEndpoint, mul_neg] using laws.start_inflate hstart

/-- The branch data are the same after negating their physical location. -/
theorem leftBranchAt_iff_reflected {X α : Type*}
    (AgreeLeft : X → X → ℝ → Prop) (StartsAt : X → ℝ → α → Prop)
    (S U : X) (y : ℝ) (b c : α) :
    LeftBranchAt AgreeLeft StartsAt S U y b c ↔
      BranchAt (reflectedAgreement AgreeLeft) (reflectedEndpoint StartsAt) S U (-y) b c := by
  simp only [LeftBranchAt, BranchAt, reflectedAgreement, reflectedEndpoint, neg_neg]

theorem leftBranchAt_zero_iff_reflected {X α : Type*}
    (AgreeLeft : X → X → ℝ → Prop) (StartsAt : X → ℝ → α → Prop)
    (S U : X) (b c : α) :
    LeftBranchAt AgreeLeft StartsAt S U 0 b c ↔
      BranchAt (reflectedAgreement AgreeLeft) (reflectedEndpoint StartsAt) S U 0 b c := by
  simpa only [neg_zero] using leftBranchAt_iff_reflected AgreeLeft StartsAt S U 0 b c

/-- Negation of the ray's starting coordinate is a bijection on witnesses. -/
theorem rightAsymptotic_reflection_iff {X : Type*}
    (AgreeLeft : X → X → ℝ → Prop) (S U : X) :
    RightAsymptotic (reflectedAgreement AgreeLeft) S U ↔ LeftAsymptotic AgreeLeft S U := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨-y, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨-y, by simpa only [reflectedAgreement, neg_neg] using hy⟩

/-- The external BDS existence input transfers in both directions.  The
periodicizing translation changes from `t` to `-t`; its period is unchanged. -/
theorem bdsPeriodicization_reflection_iff {X : Type*}
    (f : X → X) (translate : ℝ → X → X) (AgreeLeft : X → X → ℝ → Prop) :
    BDSPeriodicization f (reflectedTranslation translate)
        (RightAsymptotic (reflectedAgreement AgreeLeft)) ↔
      BDSPeriodicization f translate (LeftAsymptotic AgreeLeft) := by
  constructor
  · intro hBDS S U hne hasym
    obtain ⟨t, hS, hU⟩ := hBDS hne
      ((rightAsymptotic_reflection_iff AgreeLeft S U).mpr hasym)
    exact ⟨-t, hS, hU⟩
  · intro hBDS S U hne hasym
    obtain ⟨t, hS, hU⟩ := hBDS hne
      ((rightAsymptotic_reflection_iff AgreeLeft S U).mp hasym)
    exact ⟨-t, by simpa only [reflectedTranslation, neg_neg] using hS,
      by simpa only [reflectedTranslation, neg_neg] using hU⟩

/-- Reflection fixes the physical origin, so the R4 input at starting
endpoints is exactly R4 for the reflected ending endpoints. -/
theorem r4ZeroFibre_reflection_iff {X Y α : Type*}
    (f : X → X) (h : X → Y) (q₀ : Y) (StartsAt : X → ℝ → α → Prop) :
    R4ZeroFibre f h q₀ (reflectedEndpoint StartsAt) ↔ R4ZeroFibre f h q₀ StartsAt := by
  simp only [R4ZeroFibre, reflectedEndpoint, neg_zero]

/-- Branch uniqueness in the left orientation is a consequence of the
proved right-oriented local argument and injectivity of coordinate negation. -/
theorem LeftBranchLaws.branch_unique {X α : Type*}
    {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : α → α}
    {AgreeLeft : X → X → ℝ → Prop} {StartsAt : X → ℝ → α → Prop}
    (laws : LeftBranchLaws f translate β g AgreeLeft StartsAt)
    {S U : X} {y z : ℝ} {b c d e : α}
    (hy : LeftBranchAt AgreeLeft StartsAt S U y b c)
    (hz : LeftBranchAt AgreeLeft StartsAt S U z d e) : y = z := by
  have h := laws.toRightBranchLaws.branch_unique
    ((leftBranchAt_iff_reflected AgreeLeft StartsAt S U y b c).mp hy)
    ((leftBranchAt_iff_reflected AgreeLeft StartsAt S U z d e).mp hz)
  exact neg_injective h

/-- Left-oriented Lemma E: persistence of starting labels is equivalent
to a common positive period at the original normalized branch. -/
theorem left_endpoint_persistent_iff_pairPeriodic {X α : Type*}
    {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : α → α}
    {AgreeLeft : X → X → ℝ → Prop} {StartsAt : X → ℝ → α → Prop}
    (laws : LeftBranchLaws f translate β g AgreeLeft StartsAt) (hβ : 1 < β)
    (hBDS : BDSPeriodicization f translate (LeftAsymptotic AgreeLeft))
    {S U : X} {b c : α} (hbranch : LeftBranchAt AgreeLeft StartsAt S U 0 b c) :
    (∀ n : ℕ, g^[n] b ≠ g^[n] c) ↔ PairPeriodic f S U :=
  endpoint_persistent_iff_pairPeriodic laws.toRightBranchLaws hβ
    ((bdsPeriodicization_reflection_iff f translate AgreeLeft).mpr hBDS)
    ((leftBranchAt_zero_iff_reflected AgreeLeft StartsAt S U b c).mp hbranch)

/-- The exact two-step test for common periodicity in the left orientation. -/
theorem left_ternary_two_step_iff_pairPeriodic {X : Type*}
    {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : Fin 3 → Fin 3}
    {AgreeLeft : X → X → ℝ → Prop} {StartsAt : X → ℝ → Fin 3 → Prop}
    (laws : LeftBranchLaws f translate β g AgreeLeft StartsAt) (hβ : 1 < β)
    (hBDS : BDSPeriodicization f translate (LeftAsymptotic AgreeLeft))
    {S U : X} {b c : Fin 3} (hbranch : LeftBranchAt AgreeLeft StartsAt S U 0 b c) :
    g^[2] b ≠ g^[2] c ↔ PairPeriodic f S U :=
  ternary_two_step_iff_pairPeriodic laws.toRightBranchLaws hβ
    ((bdsPeriodicization_reflection_iff f translate AgreeLeft).mpr hBDS)
    ((leftBranchAt_zero_iff_reflected AgreeLeft StartsAt S U b c).mp hbranch)

/-- The exact two-step zero-fibre criterion for different labels starting
at a normalized left branch; the endpoint dynamics is the supplied `g`. -/
theorem left_ternary_two_step_iff_zero_fibre {X Y : Type*}
    {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : Fin 3 → Fin 3}
    {AgreeLeft : X → X → ℝ → Prop} {StartsAt : X → ℝ → Fin 3 → Prop}
    (laws : LeftBranchLaws f translate β g AgreeLeft StartsAt) (hβ : 1 < β)
    (hBDS : BDSPeriodicization f translate (LeftAsymptotic AgreeLeft))
    (A : Y → Y) (h : X → Y) (q₀ : Y)
    (hf : Injective f) (hsem : Semiconj h f A)
    (hfinite : {x | h x = q₀}.Finite) (hfixed : A q₀ = q₀)
    (hR4 : R4ZeroFibre f h q₀ StartsAt)
    {S U : X} {b c : Fin 3} (hbranch : LeftBranchAt AgreeLeft StartsAt S U 0 b c) :
    g^[2] b ≠ g^[2] c ↔ h S = q₀ ∧ h U = q₀ :=
  ternary_two_step_iff_zero_fibre laws.toRightBranchLaws hβ
    ((bdsPeriodicization_reflection_iff f translate AgreeLeft).mpr hBDS)
    A h q₀ hf hsem hfinite hfixed
    ((r4ZeroFibre_reflection_iff f h q₀ StartsAt).mpr hR4)
    ((leftBranchAt_zero_iff_reflected AgreeLeft StartsAt S U b c).mp hbranch)

/-- A successful left endpoint test gives the same zero-fibre common
partner and common positive triple period as in the right orientation. -/
theorem left_ternary_zero_fibre_periodic_triple {X Y : Type*}
    {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : Fin 3 → Fin 3}
    {AgreeLeft : X → X → ℝ → Prop} {StartsAt : X → ℝ → Fin 3 → Prop}
    (laws : LeftBranchLaws f translate β g AgreeLeft StartsAt) (hβ : 1 < β)
    (hBDS : BDSPeriodicization f translate (LeftAsymptotic AgreeLeft))
    (A : Y → Y) (h : X → Y) (q₀ : Y)
    (hf : Injective f) (hsem : Semiconj h f A)
    (hfinite : {x | h x = q₀}.Finite) (hfixed : A q₀ = q₀)
    (hR4 : R4ZeroFibre f h q₀ StartsAt)
    {T S U : X} {b c : Fin 3} (hbranch : LeftBranchAt AgreeLeft StartsAt S U 0 b c)
    (htest : g^[2] b ≠ g^[2] c) (hTS : h T = h S) :
    h T = q₀ ∧ h S = q₀ ∧ h U = q₀ ∧
      ∃ n > 0, f^[n] T = T ∧ f^[n] S = S ∧ f^[n] U = U :=
  ternary_zero_fibre_periodic_triple laws.toRightBranchLaws hβ
    ((bdsPeriodicization_reflection_iff f translate AgreeLeft).mpr hBDS)
    A h q₀ hf hsem hfinite hfixed
    ((r4ZeroFibre_reflection_iff f h q₀ StartsAt).mpr hR4)
    ((leftBranchAt_zero_iff_reflected AgreeLeft StartsAt S U b c).mp hbranch) htest hTS

end Psc.PeriodicPartnerReflection
