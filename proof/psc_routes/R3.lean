import Mathlib
import Lean.Util.CollectAxioms

/-!
# Route R3: literal prefix shifts and block-discrepancy bounds

The lemmas are exact and computable. Uniform existence of the block cuts
for all substitution depths, and eventual coincidence/productivity,
remain open. No implication from balance alone is claimed.
-/
namespace PscRoutes.R3

/-- A two-track difference of coordinate prefix counts, each no
larger than the common block length, is bounded by that length. -/
theorem bounded_block_coordinate
    (blockLength topCount bottomCount : ℕ)
    (htop : topCount ≤ blockLength)
    (hbottom : bottomCount ≤ blockLength) :
    -(blockLength : ℤ) ≤ (topCount : ℤ) - bottomCount ∧
    (topCount : ℤ) - bottomCount ≤ (blockLength : ℤ) := by
  constructor <;> omega

/-- The B-prime shift/factor identity is algebraic, independent of
frequencies, primitivity, or assumptions about balanced cuts. -/
theorem shift_factor_identity (P : ℕ → ℤ) (t k : ℕ) :
    P k - (P (t + k) - P t) =
      P t - (P (k + t) - P k) := by
  rw [Nat.add_comm t k]
  ring


/-- Telescoping scalar prefix increments over a fixed-width window;
this is exact over integers and independent of the substitution. -/
theorem telescoping_prefix_increments
    (P : ℕ → ℤ) (K t : ℕ) :
    (∑ j ∈ Finset.range t, (P (K + j + 1) - P (K + j))) =
      P (K + t) - P K := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ, ih]
      have hidx : K + t + 1 = K + (t + 1) := by omega
      rw [hidx]
      ring

/-- Exact double-Cesàro transport: sums of all windows of length t
equal sums of t long-range prefix increments. Frequency averaging
will require an independent primitive-substitution frequency theorem. -/
theorem sliding_factor_sum_identity
    (P : ℕ → ℤ) (t K : ℕ) :
    (∑ k ∈ Finset.range K, (P (k + t) - P k)) =
      ∑ j ∈ Finset.range t, (P (K + j) - P j) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      calc
        (∑ j ∈ Finset.range t, (P (K + j) - P j)) +
            (P (K + t) - P K) =
          (∑ j ∈ Finset.range t, (P (K + j) - P j)) +
            (∑ j ∈ Finset.range t,
              (P (K + j + 1) - P (K + j))) := by
              rw [telescoping_prefix_increments]
        _ = ∑ j ∈ Finset.range t,
              (P ((K + 1) + j) - P j) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro j _
              have hidx : K + j + 1 = (K + 1) + j := by omega
              rw [hidx]
              ring


/-- Per-letter Parikh counting inherits the sliding-factor sum identity
coordinatewise on any finite alphabet. This is an exact integer
identity; primitive letter-frequency limits are a separate import. -/
theorem vector_sliding_factor_sum_identity
    {d : ℕ} (P : ℕ → Fin d → ℤ) (t K : ℕ) (letter : Fin d) :
    (∑ k ∈ Finset.range K,
      (P (k + t) letter - P k letter)) =
    ∑ j ∈ Finset.range t,
      (P (K + j) letter - P j letter) := by
  exact sliding_factor_sum_identity (fun k => P k letter) t K


/-- The bounded-length alphabetic pair space is finite in every finite
alphabet. This is the already-standard finite-state step between
uniform return gaps and finiteness of *prefix-seeded* BPA states.
The genuinely open step is proving a bound uniformly in depth,
without borrowing overlap productivity. -/
theorem finite_bounded_pair_states (d L : ℕ) :
    {p : List (Fin d) × List (Fin d) |
      p.1.length ≤ L ∧ p.2.length ≤ L}.Finite := by
  have hwords : {w : List (Fin d) | w.length ≤ L}.Finite :=
    List.finite_length_le (Fin d) L
  have hpair : ({w : List (Fin d) | w.length ≤ L} ×ˢ
      {w : List (Fin d) | w.length ≤ L}) =
      {p : List (Fin d) × List (Fin d) |
        p.1.length ≤ L ∧ p.2.length ≤ L} := by
    ext p
    simp only [Set.mem_prod, Set.mem_setOf_eq]
  rw [← hpair]
  exact hwords.prod hwords

/-- Passing to a prescribed balance predicate and irreducible subset
cannot destroy the bounded-length finiteness. No reachability or
substitution-specific child identity is assumed in this lemma. -/
theorem finite_bounded_balanced_states (d L : ℕ)
    (balanced : List (Fin d) × List (Fin d) → Prop) :
    {p : List (Fin d) × List (Fin d) |
      p.1.length ≤ L ∧ p.2.length ≤ L ∧ balanced p}.Finite := by
  apply (finite_bounded_pair_states d L).subset
  intro p hp
  exact ⟨hp.1, hp.2.1⟩

end PscRoutes.R3

#print axioms PscRoutes.R3.bounded_block_coordinate
#print axioms PscRoutes.R3.shift_factor_identity
#print axioms PscRoutes.R3.telescoping_prefix_increments
#print axioms PscRoutes.R3.sliding_factor_sum_identity
#print axioms PscRoutes.R3.vector_sliding_factor_sum_identity
#print axioms PscRoutes.R3.finite_bounded_pair_states
#print axioms PscRoutes.R3.finite_bounded_balanced_states

/- Fail-closed exact-declaration axiom audit for this standalone branch.
   All declared helper theorems must use only the standard Lean axioms.
   This does not establish a full substitution-to-Lemma refinement. -/
open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`PscRoutes.R3.bounded_block_coordinate, `PscRoutes.R3.shift_factor_identity, `PscRoutes.R3.telescoping_prefix_increments, `PscRoutes.R3.sliding_factor_sum_identity, `PscRoutes.R3.vector_sliding_factor_sum_identity, `PscRoutes.R3.finite_bounded_pair_states, `PscRoutes.R3.finite_bounded_balanced_states] do
    let axioms ← collectAxioms name
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Nonstandard axiom in {name}: {ax}"
    liftIO <| IO.println s!"PSC_ROUTE_AXIOMS_OK\t{name}"
