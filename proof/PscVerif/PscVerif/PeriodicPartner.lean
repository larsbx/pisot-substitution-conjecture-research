/-
# Finite steps for periodic-partner extraction

The geometric inputs are deliberately absent from this module.  The companion research note
uses simultaneous periodicization of asymptotic tilings as an external theorem, and uses
compactness, legal vertex rays, and the strict-component hypotheses in a written proof.

This module proves only:
* lifts in a finite fibre over a periodic base are periodic when the dynamics is injective;
* on three letters, persistence of an endpoint difference is an exact finite predicate;
* a fixed base can have lifts of period two, so the base period cannot be copied unchanged.

See `docs/c4-periodic-partner-extraction-stop-go-2026-11-18.md` for the pre-code source decision.
-/
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation

namespace Psc.PeriodicPartner

open Function

/-- An injective endomap of a finite invariant set makes each point of that set periodic.
The ambient type need not be finite. -/
theorem periodic_of_finite_invariant {X : Type*} (f : X → X) (A : Set X)
    (hA : A.Finite) (hf : Injective f) (hmap : Set.MapsTo f A A)
    {x : X} (hx : x ∈ A) : ∃ n > 0, f^[n] x = x := by
  let F : A → A := fun y => ⟨f y, hmap y.property⟩
  let : Finite A := hA.to_subtype
  have hF : Injective F := by
    intro y z h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  obtain ⟨n, hn, hperiod⟩ := hF.mem_periodicPts ⟨x, hx⟩
  have hsem : Semiconj (Subtype.val : A → X) F f := fun _ => rfl
  exact ⟨n, hn, (hperiod.map hsem).eq⟩

/-- Every lift of a periodic base point in a finite fibre is periodic.  Its period is a
positive multiple of the specified base period, not necessarily that period itself. -/
theorem periodic_lift_of_finite_fibre {X Y : Type*} (f : X → X) (g : Y → Y)
    (h : X → Y) (hf : Injective f) (hsem : Semiconj h f g)
    {q : Y} (hfinite : {x | h x = q}.Finite)
    {p : ℕ} (hp : 0 < p) (hq : g^[p] q = q) {x : X} (hx : h x = q) :
    ∃ n > 0, p ∣ n ∧ f^[n] x = x := by
  have hmap : Set.MapsTo f^[p] {x | h x = q} {x | h x = q} := by
    intro y hy
    change h (f^[p] y) = q
    rw [(hsem.iterate_right p) y, hy, hq]
  obtain ⟨k, hk, hperiod⟩ :=
    periodic_of_finite_invariant f^[p] {x | h x = q} hfinite (hf.iterate p) hmap hx
  exact ⟨p * k, Nat.mul_pos hp hk, dvd_mul_right p k,
    by simpa only [iterate_mul] using hperiod⟩

/-- The preceding lifting statement gives a positive period for the lift. -/
theorem mem_periodicPts_of_finite_fibre {X Y : Type*} (f : X → X) (g : Y → Y)
    (h : X → Y) (hf : Injective f) (hsem : Semiconj h f g)
    {q : Y} (hfinite : {x | h x = q}.Finite)
    (hq : q ∈ periodicPts g) {x : X} (hx : h x = q) : x ∈ periodicPts f := by
  obtain ⟨p, hp, hqp⟩ := hq
  obtain ⟨n, hn, _, hperiod⟩ :=
    periodic_lift_of_finite_fibre f g h hf hsem hfinite hp hqp.eq hx
  exact ⟨n, hn, hperiod⟩

/-- Three periodic points have a common positive period. -/
theorem common_period_three {X : Type*} (f : X → X) {x y z : X}
    (hx : x ∈ periodicPts f) (hy : y ∈ periodicPts f) (hz : z ∈ periodicPts f) :
    ∃ n > 0, f^[n] x = x ∧ f^[n] y = y ∧ f^[n] z = z := by
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, hb, hyb⟩ := hy
  obtain ⟨c, hc, hzc⟩ := hz
  refine ⟨a * b * c, Nat.mul_pos (Nat.mul_pos ha hb) hc,
    ((hxa.mul_const b).mul_const c).eq,
    ((hyb.const_mul a).mul_const c).eq, (hzc.const_mul (a * b)).eq⟩

/-! ## Endpoint persistence on the three-letter alphabet -/

/-- An endpoint difference survives every substitution level. -/
def EndpointPersistent (g : Fin 3 → Fin 3) (b c : Fin 3) : Prop :=
  ∀ n : ℕ, g^[n] b ≠ g^[n] c

/-- After two steps no new equality can first appear for a self-map on three letters. -/
theorem endpoint_separation_step :
    ∀ (g : Fin 3 → Fin 3) (b c : Fin 3),
      g^[2] b ≠ g^[2] c → g^[2] (g b) ≠ g^[2] (g c) := by
  decide

/-- Exact finite decision for the infinite endpoint-persistence condition. -/
theorem endpoint_persistent_iff (g : Fin 3 → Fin 3) (b c : Fin 3) :
    EndpointPersistent g b c ↔ g^[2] b ≠ g^[2] c := by
  refine ⟨fun h => h 2, fun h n => ?_⟩
  have hsep : ∀ n : ℕ, g^[2] (g^[n] b) ≠ g^[2] (g^[n] c) := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      simpa only [iterate_succ_apply'] using endpoint_separation_step g (g^[n] b) (g^[n] c) ih
  exact fun heq => hsep n (congrArg g^[2] heq)

/-- Every three-letter endpoint has entered a cycle after two iterates, and its cycle
length divides six. -/
theorem endpoint_period_six :
    ∀ (g : Fin 3 → Fin 3) (b : Fin 3), g^[6] (g^[2] b) = g^[2] b := by
  decide

/-- Injectivity of the relevant endpoint map suffices for persistence. -/
theorem endpoint_persistent_of_injective (g : Fin 3 → Fin 3) (hg : Injective g)
    {b c : Fin 3} (hbc : b ≠ c) : EndpointPersistent g b c := by
  intro n h
  exact hbc ((hg.iterate n) h)

/-- An endpoint collision persists at every later level. -/
theorem endpoint_merge_persists {X : Type*} (g : X → X) {b c : X} {n : ℕ}
    (h : g^[n] b = g^[n] c) (k : ℕ) : g^[k + n] b = g^[k + n] c := by
  simp only [iterate_add_apply, h]

/-! ## Negative control: fixed base, period-two lift -/

def swapTwo : Fin 2 → Fin 2 := ![1, 0]

theorem swapTwo_injective : Injective swapTwo := by decide

theorem swapTwo_semiconj :
    Semiconj (fun _ : Fin 2 => ()) swapTwo (id : Unit → Unit) := by
  intro x
  rfl

theorem swapTwo_not_fixed : swapTwo 0 ≠ 0 := by decide

theorem swapTwo_period_two : swapTwo^[2] 0 = 0 := by decide

end Psc.PeriodicPartner
