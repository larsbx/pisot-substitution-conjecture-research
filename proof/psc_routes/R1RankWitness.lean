import R1SupportCertificate
import R1SupportFixtures

/-!
Quantitative refinement of the existing existential rank certificate.
The rank bounds ONE actual target path, not every path and not global BPA
termination. Both support checks below use the SAME raw source specification.
No finite Pisot support extraction or new universal PSC premise is supplied.
-/
namespace PscRoutes.R1RankWitness
open PscRoutes.R1SupportCertificate

variable {S T : Type*}

inductive Steps (edge : S → S → Prop) : ℕ → S → S → Prop where
  | nil (s : S) : Steps edge 0 s s
  | cons {k : ℕ} {s t u : S} :
      edge s t → Steps edge k t u → Steps edge (k + 1) s u

theorem steps_to_reach {edge : S → S → Prop} {k : ℕ} {s t : S}
    (p : Steps edge k s t) : Reach edge s t := by
  induction p with
  | nil s => exact Reach.refl s
  | cons e _ ih => exact Reach.step e ih

theorem steps_map {edge : S → S → Prop} {other : T → T → Prop}
    (decode : S → T) (h : ∀ s t, edge s t → other (decode s) (decode t))
    {k : ℕ} {s t : S} (p : Steps edge k s t) :
    Steps other k (decode s) (decode t) := by
  induction p with
  | nil s => exact Steps.nil (decode s)
  | cons e _ ih => exact Steps.cons (h _ _ e) ih

/-- Strict natural-number decrease yields a target within the start rank.
An arbitrary unchosen edge need not decrease; an initial target needs no step. -/
theorem rank_progress_bounded (edge : S → S → Prop) (target : S → Prop)
    (rank : S → ℕ)
    (hprogress : ∀ s, ¬ target s → ∃ t, edge s t ∧ rank t < rank s)
    (s : S) :
    ∃ k t, k ≤ rank s ∧ Steps edge k s t ∧ target t := by
  classical
  have h : ∀ n : ℕ, ∀ x : S, rank x = n →
      ∃ k t, k ≤ rank x ∧ Steps edge k x t ∧ target t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      by_cases ht : target x
      · exact ⟨0, x, Nat.zero_le _, Steps.nil x, ht⟩
      · rcases hprogress x ht with ⟨y, e, hy⟩
        have hlt : rank y < n := by simpa [hx] using hy
        rcases ih (rank y) hlt y rfl with ⟨k, z, hk, path, hz⟩
        exact ⟨k + 1, z, by omega, Steps.cons e path, hz⟩
  exact h (rank s) s rfl

/-- Complete literal rows transfer the bounded witness with unchanged
path length to raw source states. It is NOT a bound on all walks. -/
theorem rankCheck_bounded_raw_witness
    {n : ℕ} {Raw : Type*} [DecidableEq Raw]
    (actual : Raw → List Raw) (stateOK target : Raw → Bool)
    (decode : Fin n → Raw) (rows : Fin n → List (Fin n))
    (rank : Fin n → ℕ)
    (hcheck : rankCheck actual stateOK target decode rows rank = true)
    (i : Fin n) :
    ∃ k raw, k ≤ rank i ∧
      Steps (fun a b => b ∈ actual a) k (decode i) raw ∧ target raw = true := by
  have hv : RankConditions actual stateOK target decode rows rank :=
    of_decide_eq_true hcheck
  have hp : ∀ j, ¬ target (decode j) = true →
      ∃ t, t ∈ rows j ∧ rank t < rank j := by
    intro j hnot
    rcases (hv j).2.2 with ht | hstep
    · exact False.elim (hnot ht)
    · exact hstep
  rcases rank_progress_bounded (fun j t => t ∈ rows j)
    (fun j => target (decode j) = true) rank hp i with ⟨k, j, hk, path, ht⟩
  refine ⟨k, decode j, hk, steps_map decode ?_ path, ht⟩
  intro a b hab
  rw [← (hv a).2.1]
  exact List.mem_map.mpr ⟨b, hab, rfl⟩

/-- Two packets can use different index sets and alias raw states.
They cannot certify strict nonproductivity and productivity for the SAME
raw state with the SAME independently specified children and targets. -/
theorem accepted_supports_cannot_overlap
    {n m : ℕ} {Raw : Type*} [DecidableEq Raw]
    (actual : Raw → List Raw) (stateOK target : Raw → Bool)
    (sd : Fin n → Raw) (sr : Fin n → List (Fin n)) (keep : Fin n → Bool)
    (pd : Fin m → Raw) (pr : Fin m → List (Fin m)) (rank : Fin m → ℕ)
    (hs : strictCheck actual stateOK target sd sr keep = true)
    (hp : rankCheck actual stateOK target pd pr rank = true)
    (i : Fin n) (j : Fin m) (hi : keep i = true) (same : sd i = pd j) : False := by
  have hn := (strictCheck_sound actual stateOK target sd sr keep hs).2 i hi
  have hy := rankCheck_sound actual stateOK target pd pr rank hp j
  rw [same] at hn
  exact hn hy

/-- A literal positive-source consequence, including zero-length paths
for states already diagonal. The graph still has an avoiding two-cycle. -/
theorem fibonacci_target_path_within_one (i : Fin 4) :
    ∃ k raw, k ≤ 1 ∧
      Steps (fun a b => b ∈ PscRoutes.R1SupportFixtures.Fibonacci.children a)
        k (PscRoutes.R1SupportFixtures.Fibonacci.decode i) raw ∧
      PscRoutes.R1SupportFixtures.Binary.diagonal raw = true := by
  let F := PscRoutes.R1SupportFixtures.Fibonacci.rank
  have hbound : F i ≤ 1 := by
    fin_cases i <;> decide
  rcases rankCheck_bounded_raw_witness
    PscRoutes.R1SupportFixtures.Fibonacci.children
    PscRoutes.R1ProductivityScope.irreducible
    PscRoutes.R1SupportFixtures.Binary.diagonal
    PscRoutes.R1SupportFixtures.Fibonacci.decode
    PscRoutes.R1SupportFixtures.Fibonacci.rows
    PscRoutes.R1SupportFixtures.Fibonacci.rank
    PscRoutes.R1SupportFixtures.Fibonacci.full_productivity_certificate_accepted i
      with ⟨k, raw, hk, path, ht⟩
  exact ⟨k, raw, le_trans hk hbound, path, ht⟩

/-- No choice of arbitrarily large natural ranks can rescue the complete
binary negative fixture. This is not merely a bounded rank enumeration. -/
theorem binary_has_no_all_state_rank (rank : Fin 5 → ℕ) :
    ¬ rankCheck PscRoutes.R1ProductivityScope.children
      PscRoutes.R1ProductivityScope.irreducible
      PscRoutes.R1SupportFixtures.Binary.diagonal
      PscRoutes.R1SupportFixtures.Binary.decode
      PscRoutes.R1SupportFixtures.Binary.rows rank = true := by
  intro hp
  exact accepted_supports_cannot_overlap
    PscRoutes.R1ProductivityScope.children
    PscRoutes.R1ProductivityScope.irreducible
    PscRoutes.R1SupportFixtures.Binary.diagonal
    PscRoutes.R1SupportFixtures.Binary.decode
    PscRoutes.R1SupportFixtures.Binary.rows
    PscRoutes.R1SupportFixtures.Binary.strictMask
    PscRoutes.R1SupportFixtures.Binary.decode
    PscRoutes.R1SupportFixtures.Binary.rows rank
    PscRoutes.R1SupportFixtures.Binary.actual_strict_support_accepted
    hp 1 1 (by decide) rfl

end PscRoutes.R1RankWitness

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names := #[
    `PscRoutes.R1RankWitness.steps_to_reach,
    `PscRoutes.R1RankWitness.steps_map,
    `PscRoutes.R1RankWitness.rank_progress_bounded,
    `PscRoutes.R1RankWitness.rankCheck_bounded_raw_witness,
    `PscRoutes.R1RankWitness.accepted_supports_cannot_overlap,
    `PscRoutes.R1RankWitness.fibonacci_target_path_within_one,
    `PscRoutes.R1RankWitness.binary_has_no_all_state_rank]
  for name in names do
    let axioms ← collectAxioms name
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Nonstandard axiom in {name}: {ax}"
    liftIO <| IO.println s!"PSC_RANK_WITNESS_AXIOMS_OK\t{name}"
