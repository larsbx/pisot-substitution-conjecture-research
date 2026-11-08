import Mathlib
import Lean.Util.CollectAxioms

/-!
# Source-bound support certificates after the productivity correction

Theorems below concern an explicitly supplied transition relation. They do
not extract finite balanced-pair support from a general Pisot substitution.
A strict certificate checks ALL literal ordered children of its selected
support. A positive certificate checks every row and supplies ONE decreasing
successor per nontarget state; other transitions may lie on cycles.
-/
namespace PscRoutes.R1SupportCertificate

variable {S T : Type*}

inductive Reach (edge : S → S → Prop) : S → S → Prop where
  | refl (s : S) : Reach edge s s
  | step {s t u : S} : edge s t → Reach edge t u → Reach edge s u

def Productive (edge : S → S → Prop) (target : S → Prop) (s : S) : Prop :=
  ∃ t, Reach edge s t ∧ target t

def Closed (edge : S → S → Prop) (support : S → Prop) : Prop :=
  ∀ s t, support s → edge s t → support t

theorem reach_trans {edge : S → S → Prop} {s t : S}
    (p : Reach edge s t) : ∀ {u}, Reach edge t u → Reach edge s u := by
  induction p with
  | refl _ => intro u q; exact q
  | step e _ ih => intro u q; exact Reach.step e (ih q)

theorem productivity_backward {edge : S → S → Prop} {target : S → Prop}
    {s t : S} (p : Reach edge s t) (ht : Productive edge target t) :
    Productive edge target s := by
  rcases ht with ⟨u, q, hu⟩
  exact ⟨u, reach_trans p q, hu⟩

theorem nonproductivity_forward_closed (edge : S → S → Prop)
    (target : S → Prop) : Closed edge (fun s => ¬ Productive edge target s) := by
  intro s t hs e ht
  exact hs (productivity_backward (Reach.step e (Reach.refl t)) ht)

theorem closed_preserves_reach {edge : S → S → Prop} {support : S → Prop}
    (hclosed : Closed edge support) {s t : S} (p : Reach edge s t) :
    support s → support t := by
  induction p with
  | refl _ => exact fun hs => hs
  | step e _ ih => intro hs; exact ih (hclosed _ _ hs e)

theorem closed_target_free_unproductive (edge : S → S → Prop)
    (target support : S → Prop) (hclosed : Closed edge support)
    (hfree : ∀ s, support s → ¬ target s) {s : S} (hs : support s) :
    ¬ Productive edge target s := by
  rintro ⟨t, p, ht⟩
  exact hfree t (closed_preserves_reach hclosed p hs) ht

/-- A target path must START INSIDE the purported strict support.
A productive ancestor outside it supplies no contradiction. -/
theorem internal_witness_refutes_strict_support (edge : S → S → Prop)
    (target support : S → Prop) (hclosed : Closed edge support)
    (hfree : ∀ s, support s → ¬ target s) {s : S}
    (hs : support s) (hp : Productive edge target s) : False := by
  exact closed_target_free_unproductive edge target support hclosed hfree hs hp

/-- General graph equivalence, NOT finite strict-component extraction.
The witness on the right may be infinite. This is the G1 firewall. -/
theorem unproductive_iff_closed_target_free_support
    (edge : S → S → Prop) (target : S → Prop) (s : S) :
    (¬ Productive edge target s) ↔
    ∃ support : S → Prop, support s ∧ Closed edge support ∧
      (∀ t, support t → ¬ target t) := by
  constructor
  · intro hs
    refine ⟨fun t => Reach edge s t, Reach.refl s, ?_, ?_⟩
    · intro t u ht e
      exact reach_trans ht (Reach.step e (Reach.refl u))
    · intro t ht htarget
      exact hs ⟨t, ht, htarget⟩
  · rintro ⟨support, hs, hc, hf⟩
    exact closed_target_free_unproductive edge target support hc hf hs

/-- Existential decrease suffices. Requiring EVERY edge to decrease
would falsely exclude productive graphs with target-avoiding cycles. -/
theorem rank_progress_productive (edge : S → S → Prop) (target : S → Prop)
    (rank : S → ℕ)
    (hprogress : ∀ s, ¬ target s → ∃ t, edge s t ∧ rank t < rank s)
    (s : S) : Productive edge target s := by
  classical
  have h : ∀ n : ℕ, ∀ x : S, rank x = n → Productive edge target x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      by_cases ht : target x
      · exact ⟨x, Reach.refl x, ht⟩
      · rcases hprogress x ht with ⟨y, e, hy⟩
        have hlt : rank y < n := by simpa [hx] using hy
        rcases ih (rank y) hlt y rfl with ⟨z, p, hz⟩
        exact ⟨z, Reach.step e p, hz⟩
  exact h (rank s) s rfl

theorem reach_map {edge : S → S → Prop} {other : T → T → Prop}
    (decode : S → T) (h : ∀ s t, edge s t → other (decode s) (decode t))
    {s t : S} (p : Reach edge s t) : Reach other (decode s) (decode t) := by
  induction p with
  | refl s => exact Reach.refl (decode s)
  | step e _ ih => exact Reach.step (h _ _ e) ih

section Checks
variable {n : ℕ} {Raw : Type*} [DecidableEq Raw]

-- Use the core finite-index searches for these validators. Mathlib's generic
-- Fintype decisions also execute, but their proof transports carry classical
-- dependencies. This local choice keeps the checker axiom budget constructive;
-- it does not restrict the general classical rank proofs above.
attribute [local instance 2000] Nat.decidableForallFin Nat.decidableExistsFin

/-- Inputs `actual`, `stateOK`, and `target` are the SOURCE specification,
not unauthenticated claims made by a proposed packet. Literal ordered
list equality preserves missing exits, orientation and multiplicity. -/
def StrictConditions (actual : Raw → List Raw) (stateOK target : Raw → Bool)
    (decode : Fin n → Raw) (rows : Fin n → List (Fin n))
    (keep : Fin n → Bool) : Prop :=
  (∃ i, keep i = true) ∧ ∀ i, keep i = true →
    stateOK (decode i) = true ∧
    (rows i).map decode = actual (decode i) ∧
    target (decode i) = false ∧
    (∀ j, j ∈ rows i → keep j = true)

/-- Keep finite decidability available at the proof-recovery boundary as
well as inside the executable checker. Instance search does not unfold the
ordinary `StrictConditions` definition to rediscover a locally supplied
`@decide` instance. No classical decision procedure is used here. -/
instance strictConditionsDecidable
    (actual : Raw → List Raw) (stateOK target : Raw → Bool)
    (decode : Fin n → Raw) (rows : Fin n → List (Fin n))
    (keep : Fin n → Bool) :
    Decidable (StrictConditions actual stateOK target decode rows keep) := by
  unfold StrictConditions
  infer_instance

def strictCheck (actual : Raw → List Raw) (stateOK target : Raw → Bool)
    (decode : Fin n → Raw) (rows : Fin n → List (Fin n))
    (keep : Fin n → Bool) : Bool :=
  decide (StrictConditions actual stateOK target decode rows keep)

/-- A successful check proves nonproductivity for EVERY selected
raw source state, by induction on arbitrary-length raw descendant paths.
It does not assert strong connectivity or realization of a Pisot SCC. -/
theorem strictCheck_sound
    (actual : Raw → List Raw) (stateOK target : Raw → Bool)
    (decode : Fin n → Raw) (rows : Fin n → List (Fin n))
    (keep : Fin n → Bool)
    (hcheck : strictCheck actual stateOK target decode rows keep = true) :
    (∃ i, keep i = true) ∧ ∀ i, keep i = true →
      ¬ Productive (fun a b => b ∈ actual a) (fun a => target a = true) (decode i) := by
  have hv : StrictConditions actual stateOK target decode rows keep :=
    of_decide_eq_true hcheck
  rcases hv with ⟨hne, hrows⟩
  let support : Raw → Prop := fun a => ∃ i, keep i = true ∧ decode i = a
  have hc : Closed (fun a b => b ∈ actual a) support := by
    rintro a b ⟨i, hi, rfl⟩ hab
    rcases hrows i hi with ⟨_, hrow, _, hclosed⟩
    rw [← hrow] at hab
    rcases List.mem_map.mp hab with ⟨j, hj, hdecode⟩
    exact ⟨j, hclosed j hj, hdecode⟩
  have hf : ∀ a, support a → ¬ target a = true := by
    rintro a ⟨i, hi, rfl⟩ ht
    have hfalse := (hrows i hi).2.2.1
    rw [hfalse] at ht
    cases ht
  refine ⟨hne, ?_⟩
  intro i hi
  exact closed_target_free_unproductive _ _ support hc hf ⟨i, hi, rfl⟩

/-- All model rows are covered. One strictly descending successor for
EVERY nontarget state witnesses existential productivity, not universal
termination of every walk. Cycles on unchosen edges are allowed. -/
def RankConditions (actual : Raw → List Raw) (stateOK target : Raw → Bool)
    (decode : Fin n → Raw) (rows : Fin n → List (Fin n))
    (rank : Fin n → ℕ) : Prop :=
  ∀ i, stateOK (decode i) = true ∧
    (rows i).map decode = actual (decode i) ∧
    (target (decode i) = true ∨ ∃ j, j ∈ rows i ∧ rank j < rank i)

/-- Computable finite search, shared by `rankCheck` and every theorem
recovering `RankConditions` from an accepted Boolean certificate. -/
instance rankConditionsDecidable
    (actual : Raw → List Raw) (stateOK target : Raw → Bool)
    (decode : Fin n → Raw) (rows : Fin n → List (Fin n))
    (rank : Fin n → ℕ) :
    Decidable (RankConditions actual stateOK target decode rows rank) := by
  unfold RankConditions
  infer_instance

def rankCheck (actual : Raw → List Raw) (stateOK target : Raw → Bool)
    (decode : Fin n → Raw) (rows : Fin n → List (Fin n))
    (rank : Fin n → ℕ) : Bool :=
  decide (RankConditions actual stateOK target decode rows rank)

theorem rankCheck_sound
    (actual : Raw → List Raw) (stateOK target : Raw → Bool)
    (decode : Fin n → Raw) (rows : Fin n → List (Fin n))
    (rank : Fin n → ℕ)
    (hcheck : rankCheck actual stateOK target decode rows rank = true)
    (i : Fin n) :
    Productive (fun a b => b ∈ actual a) (fun a => target a = true) (decode i) := by
  have hv : RankConditions actual stateOK target decode rows rank :=
    of_decide_eq_true hcheck
  have hp : ∀ j, ¬ target (decode j) = true →
      ∃ k, k ∈ rows j ∧ rank k < rank j := by
    intro j hnot
    rcases (hv j).2.2 with ht | hstep
    · exact False.elim (hnot ht)
    · exact hstep
  rcases rank_progress_productive (fun j k => k ∈ rows j)
    (fun j => target (decode j) = true) rank hp i with ⟨j, p, ht⟩
  refine ⟨decode j, reach_map decode ?_ p, ht⟩
  intro a b hab
  rw [← (hv a).2.1]
  exact List.mem_map.mpr ⟨b, hab, rfl⟩

/-- Complete rows, not root productivity, justify the stronger
all-descendants conclusion. No global finite BPA closure is assumed:
the claim is restricted to the supplied finite complete carrier. -/
theorem rankCheck_all_literal_descendants
    (actual : Raw → List Raw) (stateOK target : Raw → Bool)
    (decode : Fin n → Raw) (rows : Fin n → List (Fin n))
    (rank : Fin n → ℕ)
    (hcheck : rankCheck actual stateOK target decode rows rank = true)
    (i : Fin n) (raw : Raw)
    (path : Reach (fun a b => b ∈ actual a) (decode i) raw) :
    Productive (fun a b => b ∈ actual a) (fun a => target a = true) raw := by
  have hv : RankConditions actual stateOK target decode rows rank :=
    of_decide_eq_true hcheck
  let covered : Raw → Prop := fun a => ∃ j, decode j = a
  have hc : Closed (fun a b => b ∈ actual a) covered := by
    rintro a b ⟨j, rfl⟩ hab
    rw [← (hv j).2.1] at hab
    rcases List.mem_map.mp hab with ⟨k, _, hk⟩
    exact ⟨k, hk⟩
  rcases closed_preserves_reach hc path ⟨i, rfl⟩ with ⟨j, hj⟩
  rw [← hj]
  exact rankCheck_sound actual stateOK target decode rows rank hcheck j

end Checks
end PscRoutes.R1SupportCertificate

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names := #[
    `PscRoutes.R1SupportCertificate.reach_trans,
    `PscRoutes.R1SupportCertificate.productivity_backward,
    `PscRoutes.R1SupportCertificate.nonproductivity_forward_closed,
    `PscRoutes.R1SupportCertificate.closed_preserves_reach,
    `PscRoutes.R1SupportCertificate.closed_target_free_unproductive,
    `PscRoutes.R1SupportCertificate.internal_witness_refutes_strict_support,
    `PscRoutes.R1SupportCertificate.unproductive_iff_closed_target_free_support,
    `PscRoutes.R1SupportCertificate.rank_progress_productive,
    `PscRoutes.R1SupportCertificate.reach_map,
    `PscRoutes.R1SupportCertificate.strictCheck_sound,
    `PscRoutes.R1SupportCertificate.rankCheck_sound,
    `PscRoutes.R1SupportCertificate.rankCheck_all_literal_descendants]
  for name in names do
    let axioms ← collectAxioms name
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Nonstandard axiom in {name}: {ax}"
    liftIO <| IO.println s!"PSC_SUPPORT_AXIOMS_OK\t{name}"
