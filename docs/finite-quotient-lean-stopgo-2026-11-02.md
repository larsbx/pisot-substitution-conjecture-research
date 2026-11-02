# Finite quotient distance lemma: pre-implementation stop/go

Decision: **proceed with a conditional finite graph theorem**, following the
accepted finite certificates of #447. No native-to-Lean refinement is claimed.
The side-notes ledger and earlier selected-rank/finite-certificate gates were
read before selecting this route.

## Primary sources inspected (2026-11-02)

1. [Pinned Lean Nat lemmas](https://github.com/leanprover/lean4/blob/v4.34.0-rc2/src/Init/Data/Nat/Lemmas.lean):
   the Nat induction/arithmetic layer, including its `Init.Omega` import.
2. [Pinned Mathlib relation closures](https://github.com/leanprover-community/mathlib4/blob/4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09/Mathlib/Logic/Relation.lean):
   `ReflTransGen` is built from reflexivity and genuine edge extension.
   Reuse the repository's already compiled, length-indexed `SelectedRank.Path`
   to retain exact lengths; do not introduce another reachability kernel.
3. Alkassar–Böhme–Mehlhorn–Rizkallah,
   [A Framework for the Verification of Certifying Computations](https://arxiv.org/abs/1301.7462),
   author abstract: a certificate checker and its correctness are separate from
   the producing algorithm. This is a methodology boundary, not a claim that
   this repository's native checker is formally verified.

The quotient hitting/distance argument is standard projection plus path
lifting, already stated in `class-a-reversal-quotient-2026-10-31.md`.
No novelty claim is made for that graph lemma or shortest-distance potentials.

## Exact scope and hypothesis boundary

Use finite original and quotient vertex types. Require explicit edge
projection, an actual edge lift from **every** original source orientation,
and equivalence of typed terminal membership with quotient terminal membership.
Prove length-preserving terminal path equivalence, including absence of a
terminal path; transfer the minimum path length without defining a fake finite
value for infinity. Combine the existing selected-rank witness with every-edge
inequalities to prove exact shortest lengths, rather than only an upper bound.

Controls: a genuine longer selected terminal path with a direct shorter edge;
a quotient edge that lifts from a representative but not another original
source; incompatible terminal sets. The proposed lemma must reject the missing
hypotheses. It does not establish the actual literal/Parikh/exact-sign/native
semantics of any accepted file, or all-parameter coverage, X closure, nonunit
realization, BH or PSC. Those remain independent premises.
