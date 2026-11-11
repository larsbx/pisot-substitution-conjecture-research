import R1SupportCertificate
import R1ProductivityScope

/-!
Literal-word bindings for the support certificates. The binary mixed-root
fixture is reused from the accepted productivity correction. The positive
fixture is 0 -> 01, 1 -> 0; its whole four-state child table is recomputed
by the same all-cut literal factorization specification. Neither fixture
is asserted to settle a new universal Pisot claim.
-/
namespace PscRoutes.R1SupportFixtures
open PscRoutes.R1SupportCertificate
namespace Binary
open PscRoutes.R1ProductivityScope

def decode (i : Fin 5) : Pair :=
  if i = 0 then pair State.root else
  if i = 1 then pair State.plus else
  if i = 2 then pair State.minus else
  if i = 3 then pair State.zero else pair State.one

def rows (i : Fin 5) : List (Fin 5) :=
  if i = 0 then [1,3,4,2] else
  if i = 1 then [1,2] else
  if i = 2 then [2,1] else
  if i = 3 then [3,4] else [4,3]

def diagonal (p : Pair) : Bool :=
  match p with
  | ([a], [b]) => decide (a = b)
  | _ => false

def strictMask (i : Fin 5) : Bool := decide (i = 1 ∨ i = 2)
def wrongMask (i : Fin 5) : Bool := decide (i = 0 ∨ i = 1 ∨ i = 2)

def droppedTargets (i : Fin 5) : List (Fin 5) :=
  if i = 0 then [1,2] else rows i

def reversedRow (i : Fin 5) : List (Fin 5) :=
  if i = 1 then [2,1] else rows i

def duplicateRow (i : Fin 5) : List (Fin 5) :=
  if i = 1 then [1,2,1] else rows i

theorem complete_raw_rows (i : Fin 5) :
    (rows i).map decode = children (decode i) := by
  fin_cases i <;> decide

theorem actual_strict_support_accepted :
    strictCheck children irreducible diagonal decode rows strictMask = true := by decide

theorem productive_root_cannot_join_strict_support :
    strictCheck children irreducible diagonal decode rows wrongMask = false := by decide

/-- The graph-only truncated rows are closed and target-free, but
literal row coverage detects the two hidden diagonal exits. -/
theorem omitted_target_exits_rejected :
    (∀ i : Fin 5, wrongMask i = true →
      diagonal (decode i) = false ∧
      (∀ j, j ∈ droppedTargets i → wrongMask j = true)) ∧
    strictCheck children irreducible diagonal decode droppedTargets wrongMask = false := by
  decide

theorem raw_order_change_rejected :
    strictCheck children irreducible diagonal decode reversedRow strictMask = false := by decide

theorem altered_occurrence_multiplicity_rejected :
    strictCheck children irreducible diagonal decode duplicateRow strictMask = false := by decide

theorem empty_support_is_not_a_counterexample :
    strictCheck children irreducible diagonal decode rows (fun _ => false) = false := by decide

/-- Arbitrary raw path lengths are excluded by the generic soundness
proof, not by assuming a finite sample of paths was sufficient. -/
theorem selected_actual_pairs_unproductive (i : Fin 5) (hi : strictMask i = true) :
    ¬ PscRoutes.R1SupportCertificate.Productive
      (fun a b => b ∈ children a) (fun a => diagonal a = true) (decode i) := by
  exact (strictCheck_sound children irreducible diagonal decode rows strictMask
    actual_strict_support_accepted).2 i hi
end Binary

namespace Fibonacci
open PscRoutes.R1ProductivityScope (Pair irreducible factors)

def image (a : Fin 2) : List (Fin 2) := if a = 0 then [0,1] else [0]
def children (p : Pair) : List Pair :=
  factors (p.1.flatMap image, p.2.flatMap image)

def decode (i : Fin 4) : Pair :=
  if i = 0 then ([0,1], [1,0]) else
  if i = 1 then ([1,0], [0,1]) else
  if i = 2 then ([0], [0]) else ([1], [1])

def rows (i : Fin 4) : List (Fin 4) :=
  if i = 0 then [2,1] else
  if i = 1 then [2,0] else
  if i = 2 then [2,3] else [2]

def rank (i : Fin 4) : ℕ := if i = 0 ∨ i = 1 then 1 else 0

theorem complete_raw_rows (i : Fin 4) :
    (rows i).map decode = children (decode i) := by
  fin_cases i <;> decide

theorem full_productivity_certificate_accepted :
    rankCheck children irreducible Binary.diagonal decode rows rank = true := by decide

/-- There is an off-diagonal two-cycle even though the existential
productivity certificate covers EVERY literal state and descendant. -/
theorem productive_support_keeps_target_avoiding_cycle :
    (1 : Fin 4) ∈ rows 0 ∧ (0 : Fin 4) ∈ rows 1 ∧
    Binary.diagonal (decode 0) = false ∧
    Binary.diagonal (decode 1) = false ∧ rank 0 = rank 1 := by decide

theorem invalid_rank_rejected :
    rankCheck children irreducible Binary.diagonal decode rows (fun _ => 0) = false := by decide

theorem all_covered_raw_descendants_productive (i : Fin 4) (raw : Pair)
    (h : PscRoutes.R1SupportCertificate.Reach
      (fun a b => b ∈ children a) (decode i) raw) :
    PscRoutes.R1SupportCertificate.Productive
      (fun a b => b ∈ children a) (fun a => Binary.diagonal a = true) raw := by
  exact rankCheck_all_literal_descendants children irreducible Binary.diagonal
    decode rows rank full_productivity_certificate_accepted i raw h
end Fibonacci
end PscRoutes.R1SupportFixtures

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names := #[
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
    `PscRoutes.R1SupportFixtures.Fibonacci.all_covered_raw_descendants_productive]
  for name in names do
    let axioms ← collectAxioms name
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Nonstandard axiom in {name}: {ax}"
    liftIO <| IO.println s!"PSC_SUPPORT_FIXTURE_AXIOMS_OK\t{name}"
