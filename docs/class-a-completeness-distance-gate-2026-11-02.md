# Finite completeness and distance certificates: stop/go (2026-11-02)

Decision before implementation: **proceed with the bounded certificate target**
of #442/#447. No new coincidence criterion or uniform invariant is proposed.
Read `side-notes-ledger.md` and the existing reversal quotient/hitting lemma first.

Primary sources inspected on 2026-11-02:

- Akiyama–Lee, *Algorithm for determining pure pointedness of self-affine
  tilings*, [author abstract](https://arxiv.org/abs/1003.2898). Complete overlap
  coincidence algorithms are prior art. The earlier full-text review is in
  `occurrence-path-replay-gate-2026-10-16.md`. A bounded swap graph does not
  supply the complete realized tiling dictionary or the Meyer hypothesis.
- Mercat–Akiyama, *Yet another characterization of the Pisot substitution
  conjecture*, [author abstract](https://arxiv.org/abs/1810.03500).
  Its automata criterion explicitly assumes irreducible **unit** Pisot.
  No transfer of that criterion to this nonunit realization is authorized.
- Alkassar–Böhme–Mehlhorn–Rizkallah, *A Framework for the Verification of
  Certifying Computations*, [author abstract](https://arxiv.org/abs/1301.7462).
  Witness/checker separation is established methodology; it does not make our
  Mojo checker formally verified. We specialize the standard unweighted
  distance witness: terminal zeros, all-edge inequalities, and actual
  selected edges descending by one. No novelty claim for that argument.

Exact target: for each declared completed bounded S18 specimen, rescan the
Cartesian product of literal occurrence addresses independently of the native
streaming builder. Typed full-zero coincidences are absorbing by definition.
Check seed inclusion and seed reachability, all required outgoing addresses,
full child labels, reversal lifts and original/quotient shortest terminal
length equality. Export deterministic rows for an independent Fraction oracle.

Controls: paired edge deletion (symmetry still passes), missing seeds,
extraneous components, bad addresses, incorrect distances, fake terminal
paths, longer descending ranks hiding a shorter edge, and exhausted node or
pair budgets. Budget exhaustion refuses a conclusion. Exact sign refusal
propagates. No carrier/realization/PSC claim or governance promotion follows.
