/-
# Conditional dynamics for periodic-partner extraction

This module checks the deductions of Lemmas P and E in
`docs/c4-periodic-partner-extraction-2026-11-18.md`.  It does not construct a
legal tiling hull or prove the imported geometric theorems.  In particular,
`BDSPeriodicization` and `R4ZeroFibre` are explicit theorem inputs, not axioms.

The branch interface consists of local agreement and endpoint predicates,
one-step transport, and local uniqueness of labels.  Branch-position
uniqueness and the vanishing of a periodicization translation are proved.
No interface field asserts periodic extraction, zero-fibre membership of a
branch-normalized pair, or a rank-two contradiction.

See `docs/c4-periodic-partner-formalization-stop-go-2026-11-19.md` for the
pre-implementation source decision and the geometric realization boundary.
-/
import PscVerif.PeriodicPartner
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic

namespace Psc.PeriodicPartnerDynamics

open Function

/-! ## Periodic pairs and the named external periodicization input -/

/-- A common positive period; a zero iterate is not a period witness here. -/
def PairPeriodic {X : Type*} (f : X → X) (S U : X) : Prop :=
  ∃ n > 0, f^[n] S = S ∧ f^[n] U = U

/-- The existence part of the external Barge--Diamond--Swanson input.
It periodicizes two leaves by the same translation.  It does not mention
their common partner, a realization map, or an identity fibre. -/
def BDSPeriodicization {X R : Type*} (f : X → X) (translate : R → X → X)
    (Asym : X → X → Prop) : Prop :=
  ∀ {S U}, S ≠ U → Asym S U →
    ∃ t, translate t S ∈ periodicPts f ∧ translate t U ∈ periodicPts f

theorem pairPeriodic_of_mem {X : Type*} {f : X → X} {S U : X}
    (hS : S ∈ periodicPts f) (hU : U ∈ periodicPts f) : PairPeriodic f S U := by
  obtain ⟨m, hm, hSm⟩ := hS
  obtain ⟨n, hn, hUn⟩ := hU
  exact ⟨m * n, Nat.mul_pos hm hn, (hSm.mul_const n).eq, (hUn.const_mul m).eq⟩

theorem PairPeriodic.mem_left {X : Type*} {f : X → X} {S U : X}
    (h : PairPeriodic f S U) : S ∈ periodicPts f := by
  obtain ⟨n, hn, hS, _⟩ := h
  exact ⟨n, hn, hS⟩

theorem PairPeriodic.mem_right {X : Type*} {f : X → X} {S U : X}
    (h : PairPeriodic f S U) : U ∈ periodicPts f := by
  obtain ⟨n, hn, _, hU⟩ := h
  exact ⟨n, hn, hU⟩

/-- Lemma P.  Finite-fibre lifting promotes the common partner as well as
the two BDS-periodicized leaves.  The common fibre is periodic; it is not
asserted to be a distinguished or identity fibre.

The translation family need only consist of injections.  No translation
equivariance of `h`, compactness, or inflation invariance of `Z` is used. -/
theorem periodic_triple_of_asymptotic_partners {X Y R : Type*}
    (f : X → X) (A : Y → Y) (h : X → Y) (translate : R → X → X)
    (Z Asym : X → X → Prop)
    (hf : Injective f) (hsem : Semiconj h f A)
    (hfinite : ∀ q, {x | h x = q}.Finite)
    (htranslate : ∀ t, Injective (translate t))
    (hZtranslate : ∀ t {x y}, Z x y → Z (translate t x) (translate t y))
    (hAsymTranslate : ∀ t {x y}, Asym x y → Asym (translate t x) (translate t y))
    (hZfibre : ∀ {x y}, Z x y → h x = h y)
    (hZne : ∀ {x y}, Z x y → x ≠ y)
    (hBDS : BDSPeriodicization f translate Asym)
    {T S U : X} (hTS : Z T S) (hTU : Z T U) (hSU : S ≠ U) (hAsym : Asym S U) :
    ∃ t n q, 0 < n ∧
      Z (translate t T) (translate t S) ∧ Z (translate t T) (translate t U) ∧
      f^[n] (translate t T) = translate t T ∧
      f^[n] (translate t S) = translate t S ∧
      f^[n] (translate t U) = translate t U ∧
      h (translate t T) = q ∧ h (translate t S) = q ∧ h (translate t U) = q ∧
      A^[n] q = q ∧
      translate t T ≠ translate t S ∧ translate t T ≠ translate t U ∧
      translate t S ≠ translate t U ∧ Asym (translate t S) (translate t U) := by
  obtain ⟨t, hSp, hUp⟩ := hBDS hSU hAsym
  have hTS' := hZtranslate t hTS
  have hTU' := hZtranslate t hTU
  have hTp : translate t T ∈ periodicPts f :=
    Psc.PeriodicPartner.mem_periodicPts_of_finite_fibre f A h hf hsem
      (hfinite (h (translate t S))) (hsem.mapsTo_periodicPts hSp) (hZfibre hTS')
  obtain ⟨n, hn, hTn, hSn, hUn⟩ :=
    Psc.PeriodicPartner.common_period_three f hTp hSp hUp
  have hbase : A^[n] (h (translate t S)) = h (translate t S) := by
    rw [← (hsem.iterate_right n) (translate t S), hSn]
  exact ⟨t, n, h (translate t S), hn, hTS', hTU', hTn, hSn, hUn,
    hZfibre hTS', rfl, (hZfibre hTU').symm.trans (hZfibre hTS'), hbase,
    hZne hTS', hZne hTU', fun heq => hSU (htranslate t heq), hAsymTranslate t hAsym⟩

/-! ## Local right-branch geometry -/

/-- Exact agreement on some right half-ray.  Topological asymptoticity and
its relation to this predicate remain part of a geometric realization. -/
def RightAsymptotic {X : Type*} (AgreeRight : X → X → ℝ → Prop) (S U : X) : Prop :=
  ∃ y, AgreeRight S U y

/-- A right branch at `y`: agreement to the right, with distinct labels of
the two tiles ending at `y`.  No dynamics or fibre condition enters. -/
def BranchAt {X α : Type*} (AgreeRight : X → X → ℝ → Prop)
    (EndsAt : X → ℝ → α → Prop) (S U : X) (y : ℝ) (b c : α) : Prop :=
  AgreeRight S U y ∧ EndsAt S y b ∧ EndsAt U y c ∧ b ≠ c

/-- Local geometric laws needed for the branch argument.

`agree_endpoint` only says that equality on a ray forces equal labels at
any later common endpoint.  It does not assume uniqueness of a branch or
any assertion about a periodic pair's centre.  Translation is written in
the convention `translate t S = S - t`. -/
structure RightBranchLaws {X α : Type*} (f : X → X) (translate : ℝ → X → X)
    (β : ℝ) (g : α → α) (AgreeRight : X → X → ℝ → Prop)
    (EndsAt : X → ℝ → α → Prop) : Prop where
  translate_zero : ∀ S, translate 0 S = S
  endpoint_unique : ∀ {S y b c}, EndsAt S y b → EndsAt S y c → b = c
  agree_endpoint : ∀ {S U r y b c}, AgreeRight S U r → r < y →
    EndsAt S y b → EndsAt U y c → b = c
  agree_translate : ∀ {S U y} (t : ℝ), AgreeRight S U y →
    AgreeRight (translate t S) (translate t U) (y - t)
  endpoint_translate : ∀ {S y b} (t : ℝ), EndsAt S y b →
    EndsAt (translate t S) (y - t) b
  agree_inflate : ∀ {S U y}, AgreeRight S U y → AgreeRight (f S) (f U) (β * y)
  endpoint_inflate : ∀ {S y b}, EndsAt S y b → EndsAt (f S) (β * y) (g b)

namespace RightBranchLaws

variable {X α : Type*} {f : X → X} {translate : ℝ → X → X}
    {β : ℝ} {g : α → α} {AgreeRight : X → X → ℝ → Prop}
    {EndsAt : X → ℝ → α → Prop}
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt)

include laws

theorem agree_iterate {S U : X} {y : ℝ} (n : ℕ) (h : AgreeRight S U y) :
    AgreeRight (f^[n] S) (f^[n] U) (β ^ n * y) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      simpa only [iterate_succ_apply', pow_succ', mul_assoc] using laws.agree_inflate ih

theorem endpoint_iterate {S : X} {y : ℝ} {b : α} (n : ℕ) (h : EndsAt S y b) :
    EndsAt (f^[n] S) (β ^ n * y) (g^[n] b) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      simpa only [iterate_succ_apply', pow_succ', mul_assoc] using laws.endpoint_inflate ih

theorem branch_ne {S U : X} {y : ℝ} {b c : α}
    (h : BranchAt AgreeRight EndsAt S U y b c) : S ≠ U := by
  intro heq
  exact h.2.2.2 (laws.endpoint_unique (heq ▸ h.2.1) h.2.2.1)

/-- Branch-position uniqueness follows from the local ray-agreement law. -/
theorem branch_unique {S U : X} {y z : ℝ} {b c d e : α}
    (hy : BranchAt AgreeRight EndsAt S U y b c)
    (hz : BranchAt AgreeRight EndsAt S U z d e) : y = z := by
  rcases lt_trichotomy y z with hlt | heq | hlt
  · exact False.elim (hz.2.2.2 (laws.agree_endpoint hy.1 hlt hz.2.1 hz.2.2.1))
  · exact heq
  · exact False.elim (hy.2.2.2 (laws.agree_endpoint hz.1 hlt hy.2.1 hy.2.2.1))

theorem branch_translate {S U : X} {y : ℝ} {b c : α} (t : ℝ)
    (h : BranchAt AgreeRight EndsAt S U y b c) :
    BranchAt AgreeRight EndsAt (translate t S) (translate t U) (y - t) b c := by
  exact ⟨laws.agree_translate t h.1, laws.endpoint_translate t h.2.1,
    laws.endpoint_translate t h.2.2.1, h.2.2.2⟩

/-- Inflation preserves a branch at level `n` when its two transported
labels are still distinct; no unconditional preservation is used. -/
theorem branch_iterate {S U : X} {y : ℝ} {b c : α} (n : ℕ)
    (h : BranchAt AgreeRight EndsAt S U y b c) (hne : g^[n] b ≠ g^[n] c) :
    BranchAt AgreeRight EndsAt (f^[n] S) (f^[n] U) (β ^ n * y) (g^[n] b) (g^[n] c) := by
  exact ⟨laws.agree_iterate n h.1, laws.endpoint_iterate n h.2.1,
    laws.endpoint_iterate n h.2.2.1, hne⟩

end RightBranchLaws

/-- The only location fixed by a positive power of a genuine expansion is zero. -/
theorem expanding_fixed_location_eq_zero {β y : ℝ} {n : ℕ}
    (hβ : 1 < β) (hn : 0 < n) (hy : y = β ^ n * y) : y = 0 := by
  by_contra hy0
  have hpow : β ^ n = 1 := (mul_eq_right₀ hy0).mp hy.symm
  exact (ne_of_gt (one_lt_pow₀ hβ (Nat.ne_of_gt hn))) hpow

/-- Persistent endpoint separation forces any common periodicization
translation of a branch-normalized pair to be zero.  This conclusion is
derived from local transport and branch uniqueness. -/
theorem periodicization_translation_eq_zero {X α : Type*}
    {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : α → α}
    {AgreeRight : X → X → ℝ → Prop} {EndsAt : X → ℝ → α → Prop}
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt) (hβ : 1 < β)
    {S U : X} {b c : α} (hbranch : BranchAt AgreeRight EndsAt S U 0 b c)
    (hpersist : ∀ n : ℕ, g^[n] b ≠ g^[n] c) {t : ℝ}
    (hperiod : PairPeriodic f (translate t S) (translate t U)) : t = 0 := by
  obtain ⟨n, hn, hSn, hUn⟩ := hperiod
  have hshift := laws.branch_translate t hbranch
  have hinflate := laws.branch_iterate n hshift (hpersist n)
  rw [hSn, hUn] at hinflate
  have hlocation := laws.branch_unique hshift hinflate
  have hzero := expanding_fixed_location_eq_zero hβ hn hlocation
  simpa using hzero

/-- Lemma E, persistence implies common periodicity of the original
branch-normalized pair, using the separately named BDS input. -/
theorem pairPeriodic_of_endpoint_persistent {X α : Type*}
    {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : α → α}
    {AgreeRight : X → X → ℝ → Prop} {EndsAt : X → ℝ → α → Prop}
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt) (hβ : 1 < β)
    (hBDS : BDSPeriodicization f translate (RightAsymptotic AgreeRight))
    {S U : X} {b c : α} (hbranch : BranchAt AgreeRight EndsAt S U 0 b c)
    (hpersist : ∀ n : ℕ, g^[n] b ≠ g^[n] c) : PairPeriodic f S U := by
  obtain ⟨t, hS, hU⟩ := hBDS (laws.branch_ne hbranch) ⟨0, hbranch.1⟩
  have hperiod := pairPeriodic_of_mem hS hU
  have ht := periodicization_translation_eq_zero laws hβ hbranch hpersist hperiod
  subst t
  simpa only [laws.translate_zero] using hperiod

/-- Common periodicity returns both endpoint labels; two different
periodic labels cannot merge at an intermediate iterate. -/
theorem endpoint_persistent_of_pairPeriodic {X α : Type*}
    {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : α → α}
    {AgreeRight : X → X → ℝ → Prop} {EndsAt : X → ℝ → α → Prop}
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt)
    {S U : X} {b c : α} (hbranch : BranchAt AgreeRight EndsAt S U 0 b c)
    (hperiod : PairPeriodic f S U) : ∀ n : ℕ, g^[n] b ≠ g^[n] c := by
  obtain ⟨p, hp, hSp, hUp⟩ := hperiod
  have hb : IsPeriodicPt g p b := laws.endpoint_unique
    (by simpa only [hSp, mul_zero] using laws.endpoint_iterate p hbranch.2.1) hbranch.2.1
  have hc : IsPeriodicPt g p c := laws.endpoint_unique
    (by simpa only [hUp, mul_zero] using laws.endpoint_iterate p hbranch.2.2.1) hbranch.2.2.1
  intro n hmerge
  exact hbranch.2.2.2 ((hb.iterate n).eq_of_apply_eq_same (hc.iterate n) hp hmerge)

theorem endpoint_persistent_iff_pairPeriodic {X α : Type*}
    {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : α → α}
    {AgreeRight : X → X → ℝ → Prop} {EndsAt : X → ℝ → α → Prop}
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt) (hβ : 1 < β)
    (hBDS : BDSPeriodicization f translate (RightAsymptotic AgreeRight))
    {S U : X} {b c : α} (hbranch : BranchAt AgreeRight EndsAt S U 0 b c) :
    (∀ n : ℕ, g^[n] b ≠ g^[n] c) ↔ PairPeriodic f S U :=
  ⟨pairPeriodic_of_endpoint_persistent laws hβ hBDS hbranch,
    endpoint_persistent_of_pairPeriodic laws hbranch⟩

/-! ## Origin endpoints and the distinguished fibre -/

/-- The external origin/fibre input (R4), with both indispensable premises:
the point is periodic and has an endpoint at the physical origin. -/
def R4ZeroFibre {X Y α : Type*} (f : X → X) (h : X → Y) (q₀ : Y)
    (EndsAt : X → ℝ → α → Prop) : Prop :=
  ∀ {S b}, S ∈ periodicPts f → EndsAt S 0 b → h S = q₀

/-- Members of a finite fibre over a fixed base point are periodic. -/
theorem periodic_of_fixed_fibre {X Y : Type*}
    (f : X → X) (A : Y → Y) (h : X → Y) (q₀ : Y)
    (hf : Injective f) (hsem : Semiconj h f A)
    (hfinite : {x | h x = q₀}.Finite) (hfixed : A q₀ = q₀)
    {S : X} (hS : h S = q₀) : S ∈ periodicPts f := by
  apply Psc.PeriodicPartner.mem_periodicPts_of_finite_fibre f A h hf hsem hfinite _ hS
  exact ⟨1, Nat.zero_lt_one, show A^[1] q₀ = q₀ from by simpa only [iterate_one] using hfixed⟩

/-- The periodicity/zero-fibre equivalence at supplied origin endpoints.
The reverse implication is proved by finite-fibre dynamics, not assumed. -/
theorem pairPeriodic_iff_zero_fibre {X Y α : Type*}
    (f : X → X) (A : Y → Y) (h : X → Y) (q₀ : Y)
    (EndsAt : X → ℝ → α → Prop)
    (hf : Injective f) (hsem : Semiconj h f A)
    (hfinite : {x | h x = q₀}.Finite) (hfixed : A q₀ = q₀)
    (hR4 : R4ZeroFibre f h q₀ EndsAt)
    {S U : X} {b c : α} (hS : EndsAt S 0 b) (hU : EndsAt U 0 c) :
    PairPeriodic f S U ↔ h S = q₀ ∧ h U = q₀ := by
  constructor
  · intro hp
    exact ⟨hR4 hp.mem_left hS, hR4 hp.mem_right hU⟩
  · rintro ⟨hSz, hUz⟩
    exact pairPeriodic_of_mem
      (periodic_of_fixed_fibre f A h q₀ hf hsem hfinite hfixed hSz)
      (periodic_of_fixed_fibre f A h q₀ hf hsem hfinite hfixed hUz)

/-- Lemma E, all alphabets: persistent endpoints exactly characterize
the distinguished fibre for a branch-normalized pair, under the explicit
BDS, R4, and finite-semiconjugacy inputs. -/
theorem endpoint_persistent_iff_zero_fibre {X Y α : Type*}
    {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : α → α}
    {AgreeRight : X → X → ℝ → Prop} {EndsAt : X → ℝ → α → Prop}
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt) (hβ : 1 < β)
    (hBDS : BDSPeriodicization f translate (RightAsymptotic AgreeRight))
    (A : Y → Y) (h : X → Y) (q₀ : Y)
    (hf : Injective f) (hsem : Semiconj h f A)
    (hfinite : {x | h x = q₀}.Finite) (hfixed : A q₀ = q₀)
    (hR4 : R4ZeroFibre f h q₀ EndsAt)
    {S U : X} {b c : α} (hbranch : BranchAt AgreeRight EndsAt S U 0 b c) :
    (∀ n : ℕ, g^[n] b ≠ g^[n] c) ↔ h S = q₀ ∧ h U = q₀ :=
  (endpoint_persistent_iff_pairPeriodic laws hβ hBDS hbranch).trans
    (pairPeriodic_iff_zero_fibre f A h q₀ EndsAt hf hsem hfinite hfixed hR4
      hbranch.2.1 hbranch.2.2.1)

/-- On three letters the geometric periodicity criterion is exactly a
two-step endpoint inequality. -/
theorem ternary_two_step_iff_pairPeriodic {X : Type*}
    {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : Fin 3 → Fin 3}
    {AgreeRight : X → X → ℝ → Prop} {EndsAt : X → ℝ → Fin 3 → Prop}
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt) (hβ : 1 < β)
    (hBDS : BDSPeriodicization f translate (RightAsymptotic AgreeRight))
    {S U : X} {b c : Fin 3} (hbranch : BranchAt AgreeRight EndsAt S U 0 b c) :
    g^[2] b ≠ g^[2] c ↔ PairPeriodic f S U :=
  (Psc.PeriodicPartner.endpoint_persistent_iff g b c).symm.trans
    (endpoint_persistent_iff_pairPeriodic laws hβ hBDS hbranch)

/-- The exact finite test for the distinguished-fibre clause of Lemma E. -/
theorem ternary_two_step_iff_zero_fibre {X Y : Type*}
    {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : Fin 3 → Fin 3}
    {AgreeRight : X → X → ℝ → Prop} {EndsAt : X → ℝ → Fin 3 → Prop}
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt) (hβ : 1 < β)
    (hBDS : BDSPeriodicization f translate (RightAsymptotic AgreeRight))
    (A : Y → Y) (h : X → Y) (q₀ : Y)
    (hf : Injective f) (hsem : Semiconj h f A)
    (hfinite : {x | h x = q₀}.Finite) (hfixed : A q₀ = q₀)
    (hR4 : R4ZeroFibre f h q₀ EndsAt)
    {S U : X} {b c : Fin 3} (hbranch : BranchAt AgreeRight EndsAt S U 0 b c) :
    g^[2] b ≠ g^[2] c ↔ h S = q₀ ∧ h U = q₀ :=
  (Psc.PeriodicPartner.endpoint_persistent_iff g b c).symm.trans
    (endpoint_persistent_iff_zero_fibre laws hβ hBDS A h q₀ hf hsem hfinite hfixed hR4 hbranch)

/-- The zero-fibre common-partner consumer.  A same-fibre link to either
leaf is enough after both leaves have passed the two-step test; the second
strict link can be retained unchanged by the caller. -/
theorem ternary_zero_fibre_periodic_triple {X Y : Type*}
    {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : Fin 3 → Fin 3}
    {AgreeRight : X → X → ℝ → Prop} {EndsAt : X → ℝ → Fin 3 → Prop}
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt) (hβ : 1 < β)
    (hBDS : BDSPeriodicization f translate (RightAsymptotic AgreeRight))
    (A : Y → Y) (h : X → Y) (q₀ : Y)
    (hf : Injective f) (hsem : Semiconj h f A)
    (hfinite : {x | h x = q₀}.Finite) (hfixed : A q₀ = q₀)
    (hR4 : R4ZeroFibre f h q₀ EndsAt)
    {T S U : X} {b c : Fin 3} (hbranch : BranchAt AgreeRight EndsAt S U 0 b c)
    (htest : g^[2] b ≠ g^[2] c) (hTS : h T = h S) :
    h T = q₀ ∧ h S = q₀ ∧ h U = q₀ ∧
      ∃ n > 0, f^[n] T = T ∧ f^[n] S = S ∧ f^[n] U = U := by
  obtain ⟨hS, hU⟩ :=
    (ternary_two_step_iff_zero_fibre laws hβ hBDS A h q₀ hf hsem hfinite hfixed hR4 hbranch).mp htest
  have hT : h T = q₀ := hTS.trans hS
  refine ⟨hT, hS, hU, ?_⟩
  exact Psc.PeriodicPartner.common_period_three f
    (periodic_of_fixed_fibre f A h q₀ hf hsem hfinite hfixed hT)
    (periodic_of_fixed_fibre f A h q₀ hf hsem hfinite hfixed hS)
    (periodic_of_fixed_fibre f A h q₀ hf hsem hfinite hfixed hU)

end Psc.PeriodicPartnerDynamics
