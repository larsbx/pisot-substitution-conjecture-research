import R1RankWitness

/-!
Acceptance checks for the finite source-bound R1 certificates.

This file deliberately separates executable validation from theorem inspection.
The Boolean checks exercise computation; the typed examples pin the mathematical
contracts; the final command inspects imported, compiled theorem declarations and
collects their actual axiom dependencies. None of these checks claims that an
arbitrary substitution has a complete finite presentation of its pair process.
-/

namespace PscRoutes.R1SupportAcceptance

open PscRoutes.R1SupportCertificate
open PscRoutes.R1RankWitness

/- Generic decidability must remain available without classical reasoning. -/
section ComputableDecidability

variable {n : ℕ} {Raw : Type*} [DecidableEq Raw]
variable (actual : Raw → List Raw) (stateOK target : Raw → Bool)
variable (decode : Fin n → Raw) (rows : Fin n → List (Fin n))

example (keep : Fin n → Bool) :
    Decidable (StrictConditions actual stateOK target decode rows keep) :=
  inferInstance

example (rank : Fin n → ℕ) :
    Decidable (RankConditions actual stateOK target decode rows rank) :=
  inferInstance

/- Pin the conjuncts, including exact ordered rows and occurrence multiplicity. -/
example (keep : Fin n → Bool) :
    StrictConditions actual stateOK target decode rows keep ↔
      (∃ i, keep i = true) ∧ ∀ i, keep i = true →
        stateOK (decode i) = true ∧
        (rows i).map decode = actual (decode i) ∧
        target (decode i) = false ∧
        (∀ j, j ∈ rows i → keep j = true) :=
  Iff.rfl

example (rank : Fin n → ℕ) :
    RankConditions actual stateOK target decode rows rank ↔
      ∀ i, stateOK (decode i) = true ∧
        (rows i).map decode = actual (decode i) ∧
        (target (decode i) = true ∨
          ∃ j, j ∈ rows i ∧ rank j < rank i) :=
  Iff.rfl

end ComputableDecidability

/- Pin the direction of propagation and the strict-support contract. -/
example {S : Type*} {edge : S → S → Prop} {target : S → Prop}
    {s t : S} (path : Reach edge s t) (productive : Productive edge target t) :
    Productive edge target s :=
  productivity_backward path productive

example {S : Type*} (edge : S → S → Prop)
    (target support : S → Prop) (closed : Closed edge support)
    (free : ∀ s, support s → ¬ target s) {s : S} (selected : support s) :
    ¬ Productive edge target s :=
  closed_target_free_unproductive edge target support closed free selected

example {S : Type*} (edge : S → S → Prop) (target : S → Prop)
    (rank : S → ℕ)
    (progress : ∀ s, ¬ target s → ∃ t, edge s t ∧ rank t < rank s)
    (s : S) : Productive edge target s :=
  rank_progress_productive edge target rank progress s

example {S : Type*} (edge : S → S → Prop) (target : S → Prop)
    (rank : S → ℕ)
    (progress : ∀ s, ¬ target s → ∃ t, edge s t ∧ rank t < rank s)
    (s : S) : ∃ k t, k ≤ rank s ∧ Steps edge k s t ∧ target t :=
  rank_progress_bounded edge target rank progress s

section SourceBoundContracts

variable {n m : ℕ} {Raw : Type*} [DecidableEq Raw]
variable (actual : Raw → List Raw) (stateOK target : Raw → Bool)
variable (decode : Fin n → Raw) (rows : Fin n → List (Fin n))

example (keep : Fin n → Bool)
    (accepted : strictCheck actual stateOK target decode rows keep = true) :
    (∃ i, keep i = true) ∧ ∀ i, keep i = true →
      ¬ Productive (fun a b => b ∈ actual a)
        (fun a => target a = true) (decode i) :=
  strictCheck_sound actual stateOK target decode rows keep accepted

example (rank : Fin n → ℕ)
    (accepted : rankCheck actual stateOK target decode rows rank = true)
    (i : Fin n) :
    Productive (fun a b => b ∈ actual a)
      (fun a => target a = true) (decode i) :=
  rankCheck_sound actual stateOK target decode rows rank accepted i

/- Descendants are covered through the actual source and complete certified rows. -/
example (rank : Fin n → ℕ)
    (accepted : rankCheck actual stateOK target decode rows rank = true)
    (i : Fin n) (raw : Raw)
    (path : Reach (fun a b => b ∈ actual a) (decode i) raw) :
    Productive (fun a b => b ∈ actual a) (fun a => target a = true) raw :=
  rankCheck_all_literal_descendants actual stateOK target decode rows rank accepted i raw path

/- A rank bounds the length of an actual raw-source path to a target. -/
example (rank : Fin n → ℕ)
    (accepted : rankCheck actual stateOK target decode rows rank = true)
    (i : Fin n) :
    ∃ k raw, k ≤ rank i ∧
      Steps (fun a b => b ∈ actual a) k (decode i) raw ∧ target raw = true :=
  rankCheck_bounded_raw_witness actual stateOK target decode rows rank accepted i

/- Both certificates must be bound to the same actual source and target test. -/
example (keep : Fin n → Bool)
    (pd : Fin m → Raw) (pr : Fin m → List (Fin m)) (rank : Fin m → ℕ)
    (hs : strictCheck actual stateOK target decode rows keep = true)
    (hp : rankCheck actual stateOK target pd pr rank = true)
    (i : Fin n) (j : Fin m) (hi : keep i = true) (same : decode i = pd j) : False :=
  accepted_supports_cannot_overlap actual stateOK target decode rows keep pd pr rank
    hs hp i j hi same

end SourceBoundContracts

/- The binary exclusion quantifies over every natural-valued rank, without a cap. -/
example (rank : Fin 5 → ℕ) :
    ¬ rankCheck PscRoutes.R1ProductivityScope.children
      PscRoutes.R1ProductivityScope.irreducible
      PscRoutes.R1SupportFixtures.Binary.diagonal
      PscRoutes.R1SupportFixtures.Binary.decode
      PscRoutes.R1SupportFixtures.Binary.rows rank = true :=
  binary_has_no_all_state_rank rank

example (i : Fin 4) :
    ∃ k raw, k ≤ 1 ∧
      Steps (fun a b => b ∈ PscRoutes.R1SupportFixtures.Fibonacci.children a)
        k (PscRoutes.R1SupportFixtures.Fibonacci.decode i) raw ∧
      PscRoutes.R1SupportFixtures.Binary.diagonal raw = true :=
  fibonacci_target_path_within_one i

/- These are evaluated by the compiler, rather than replaced by theorem proofs. -/
open PscRoutes.R1SupportFixtures in
#eval do
  let strict := strictCheck PscRoutes.R1ProductivityScope.children
    PscRoutes.R1ProductivityScope.irreducible Binary.diagonal Binary.decode
  let ranked := rankCheck Fibonacci.children PscRoutes.R1ProductivityScope.irreducible
    Binary.diagonal Fibonacci.decode
  let tests : List (String × Bool × Bool) := [
    ("strict_complete_support", strict Binary.rows Binary.strictMask, true),
    ("strict_productive_root_rejected", strict Binary.rows Binary.wrongMask, false),
    ("strict_omitted_target_exits_rejected", strict Binary.droppedTargets Binary.wrongMask, false),
    ("strict_reordered_source_rejected", strict Binary.reversedRow Binary.strictMask, false),
    ("strict_duplicated_source_rejected", strict Binary.duplicateRow Binary.strictMask, false),
    ("strict_empty_support_rejected", strict Binary.rows (fun _ => false), false),
    ("rank_complete_source", ranked Fibonacci.rows Fibonacci.rank, true),
    ("rank_no_progress_rejected", ranked Fibonacci.rows (fun _ => 0), false),
    ("rank_wrong_actual_source_rejected",
      rankCheck (fun _ => []) PscRoutes.R1ProductivityScope.irreducible
        Binary.diagonal Fibonacci.decode Fibonacci.rows Fibonacci.rank, false),
    ("rank_invalid_states_rejected",
      rankCheck Fibonacci.children (fun _ => false)
        Binary.diagonal Fibonacci.decode Fibonacci.rows Fibonacci.rank, false),
    ("rank_target_free_source_rejected",
      rankCheck Fibonacci.children PscRoutes.R1ProductivityScope.irreducible
        (fun _ => false) Fibonacci.decode Fibonacci.rows Fibonacci.rank, false),
    ("rank_omitted_source_child_rejected",
      ranked (fun i => if i = 0 then [2] else Fibonacci.rows i) Fibonacci.rank, false),
    ("rank_reordered_source_rejected",
      ranked (fun i => if i = 0 then [1, 2] else Fibonacci.rows i) Fibonacci.rank, false),
    ("rank_actual_target_path_within_one",
      decide (∀ i : Fin 4,
        Binary.diagonal (Fibonacci.decode i) = true ∨
          ∃ j : Fin 4,
            Fibonacci.decode j ∈ Fibonacci.children (Fibonacci.decode i) ∧
            Binary.diagonal (Fibonacci.decode j) = true), true)]
  for (label, observed, expected) in tests do
    if observed != expected then
      throw <| IO.userError s!"Certificate computation failed: {label}: expected {expected}, got {observed}"
    IO.println s!"PSC_SUPPORT_ACCEPTANCE_BOOL_OK\t{label}\t{observed}"

/- Inspect the actual compiled theorem inventory, rejecting admitted/nonstandard proofs. -/
open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names := #[
    `PscRoutes.R1ProductivityScope.literal_factorization,
    `PscRoutes.R1ProductivityScope.raw_child_coverage,
    `PscRoutes.R1ProductivityScope.all_named_pairs_irreducible,
    `PscRoutes.R1ProductivityScope.productive_root_complete_cuts,
    `PscRoutes.R1ProductivityScope.root_words_are_legal_factors,
    `PscRoutes.R1ProductivityScope.incidence_has_nonzero_kernel,
    `PscRoutes.R1ProductivityScope.strict_class_child_closed,
    `PscRoutes.R1ProductivityScope.strict_class_has_no_target,
    `PscRoutes.R1ProductivityScope.strict_class_recurrent,
    `PscRoutes.R1ProductivityScope.reach_trans,
    `PscRoutes.R1ProductivityScope.strict_reachable_closed,
    `PscRoutes.R1ProductivityScope.strict_class_unproductive,
    `PscRoutes.R1ProductivityScope.root_productive,
    `PscRoutes.R1ProductivityScope.productivity_propagates_to_predecessors,
    `PscRoutes.R1ProductivityScope.productive_parent_has_unproductive_child,
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
    `PscRoutes.R1SupportCertificate.rankCheck_all_literal_descendants,
    `PscRoutes.R1SupportFixtures.Binary.complete_raw_rows,
    `PscRoutes.R1SupportFixtures.Binary.actual_strict_support_accepted,
    `PscRoutes.R1SupportFixtures.Binary.productive_root_cannot_join_strict_support,
    `PscRoutes.R1SupportFixtures.Binary.omitted_target_exits_rejected,
    `PscRoutes.R1SupportFixtures.Binary.raw_order_change_rejected,
    `PscRoutes.R1SupportFixtures.Binary.altered_occurrence_multiplicity_rejected,
    `PscRoutes.R1SupportFixtures.Binary.empty_support_is_not_a_counterexample,
    `PscRoutes.R1SupportFixtures.Binary.selected_actual_pairs_unproductive,
    `PscRoutes.R1SupportFixtures.Fibonacci.complete_raw_rows,
    `PscRoutes.R1SupportFixtures.Fibonacci.full_productivity_certificate_accepted,
    `PscRoutes.R1SupportFixtures.Fibonacci.productive_support_keeps_target_avoiding_cycle,
    `PscRoutes.R1SupportFixtures.Fibonacci.invalid_rank_rejected,
    `PscRoutes.R1SupportFixtures.Fibonacci.all_covered_raw_descendants_productive,
    `PscRoutes.R1RankWitness.steps_to_reach,
    `PscRoutes.R1RankWitness.steps_map,
    `PscRoutes.R1RankWitness.rank_progress_bounded,
    `PscRoutes.R1RankWitness.rankCheck_bounded_raw_witness,
    `PscRoutes.R1RankWitness.accepted_supports_cannot_overlap,
    `PscRoutes.R1RankWitness.fibonacci_target_path_within_one,
    `PscRoutes.R1RankWitness.binary_has_no_all_state_rank]
  if names.size != 47 then
    throwError "Expected exactly 47 imported theorem contracts"
  let env ← getEnv
  for name in names do
    let some info := env.find? name | throwError "Missing compiled theorem: {name}"
    match info with
    | .thmInfo _ => pure ()
    | _ => throwError "Expected a compiled theorem declaration: {name}"
    logInfo m!"PSC_SUPPORT_ACCEPTANCE_TYPE\t{name}\n{info.type}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Nonstandard axiom in {name}: {ax}"
    liftIO <| IO.println s!"PSC_SUPPORT_ACCEPTANCE_AXIOMS\t{name}\t{reprStr axioms}"
  liftIO <| IO.println s!"PSC_SUPPORT_ACCEPTANCE_THEOREMS\t{names.size}"

/- Record the chosen finite decision instances, including implicit arguments. -/
set_option pp.explicit true in
#print PscRoutes.R1SupportCertificate.strictConditionsDecidable

set_option pp.explicit true in
#print PscRoutes.R1SupportCertificate.rankConditionsDecidable

/- This axiom budget is stronger than executability: it also constrains erased
proof dependencies. The #eval checks above separately establish execution. -/
open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Quot.sound]
  let names := #[
    `PscRoutes.R1SupportCertificate.strictConditionsDecidable,
    `PscRoutes.R1SupportCertificate.rankConditionsDecidable,
    `PscRoutes.R1SupportCertificate.strictCheck,
    `PscRoutes.R1SupportCertificate.rankCheck]
  let env ← getEnv
  for name in names do
    let some info := env.find? name | throwError "Missing compiled checker: {name}"
    match info with
    | .defnInfo _ => pure ()
    | _ => throwError "Expected a computational definition: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Checker axiom budget exceeded in {name}: {ax}"
    liftIO <| IO.println s!"PSC_SUPPORT_ACCEPTANCE_COMPUTABLE\t{name}\t{reprStr axioms}"

end PscRoutes.R1SupportAcceptance
