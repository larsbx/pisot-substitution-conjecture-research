# Finite productivity: pre-code source decision

Decision: **proceed with a conditional finite-reachability bridge**. This
note was written before the new `FiniteProductivity.lean` and
`NamedFiniteProductivity.lean` sources, on parent
`16dd825648d1a1bcdba9038e079463a9bebbaf3d`.

## Exact target

For an arbitrary substitution `s` on an alphabet with decidable equality,
assume that no finite strict system exists. For every actual irreducible
balanced block `T`, prove

```text
TerminatesWithCoincidence s T
  iff {U | ReflTransGen (ChildNC s) T U}.Finite.
```

The forward implication is part of the existing definition. For the
reverse implication, each nonproductive reachable block would generate a
finite coincidence-free complete factor set and hence a forbidden strict
system. Derive the corresponding infinite-reachability obstruction when
productivity or termination fails. Specialize only through the existing
validated named packet; do not supply its missing finiteness premise.

## Three primary-source checks

1. **V. F. Sirvent and B. Solomyak, *Pure Discrete Spectrum for
   One-dimensional Substitution Systems of Pisot Type*, Canadian
   Mathematical Bulletin 45 (2002), 697–710,
   [doi:10.4153/CMB-2002-062-3](https://doi.org/10.4153/CMB-2002-062-3).**
   Fresh retrieval of the publisher PDF, section 3, separates finite
   balanced-pair closure from the requirement that every pair reaches a
   coincidence. The proof of Theorem 3.1 uses the associated directed
   graph, with occurrence multiplicities. Its Remark 3 records the
   familiar finite-termination plus strong-coincidence implication. The
   proposed contribution is the repository's weaker sufficient input
   `no StrictSystem`, with arbitrary initial blocks. It imports no
   spectral conclusion or prefix-seed identification from this paper.
2. **M. Barge, S. Štimac and R. F. Williams, *Pure discrete spectrum in
   substitution tiling spaces*, Discrete and Continuous Dynamical
   Systems 33 (2013), 579–597,
   [doi:10.3934/dcds.2013.33.579](https://doi.org/10.3934/dcds.2013.33.579),
   [author PDF](https://web.math.pmf.unizg.hr/~sonja/PDSfinal.pdf).**
   Fresh retrieval of the definition preceding Theorem 3.2 requires both
   a finite set of irreducible factors and eventual coincidence for each
   such factor. Theorem 3.2 and Corollary 2 add Pisot and independence or
   irreducibility hypotheses for a spectral conclusion. Those hypotheses
   and the spectral construction are outside this graph bridge. Its
   conclusion retains the repository's existing `ChildNC` definition,
   where coincidence states are terminal; it does not silently replace
   that relation with the paper's full factor closure.
3. **B. F. Martensen, *A Generalized Balanced Pair Algorithm*, Topology
   Proceedings 28 (2004),
   [arXiv:math/0309194](https://arxiv.org/abs/math/0309194),
   [preprint PDF](https://arxiv.org/pdf/math/0309194).**
   Fresh retrieval of Example 3.13 and section 4 shows why forced
   coincidences and finite closure must be kept separate: the rewritten
   Morse–Thue example is nonterminating despite forced coincidences.
   The paper also changes the word equivalence relation, which can
   change termination behavior. We preserve exact Parikh balance,
   literal reduction and the current complete child relation. Its
   generalized-equivalence results are not imported.

The journal-hosted Martensen search result redirected to an unrelated
pseudo-arc paper; it was rejected, and the author-uploaded arXiv PDF was
used instead. This is a retrieval correction, not a mathematical input.

## Source-contract check

At the exact parent, `StrictSystem.lean` provides
`strictSystem_of_factorSet`, `factorSet_eq_reachable`, and
`reachable_of_not_productive`. `Descendants.reachable_isBlock` transports
the actual block hypothesis along the complete child relation. Lift a
`ChildNC` path into that relation; do not assume the reached state is a
block merely from its name. Transitivity embeds each descendant's
reachable set in the original finite set. These are the only structural
steps needed, with no nonerasure, primitivity, Pisot, or finite-alphabet
premise on the generic theorem.

`Psc.ArchivedPayload.Packet.no_strictSystem` supplies the exclusion only
for its authenticated `Fin 2` fixture. Its complete gate is pending at
this decision; provisional development does not supply that receipt.
The existing inverse-overlap archive is not a forward BPA state set.

## Controls and decision boundary

- Reuse actual Thue–Morse `0 -> 01, 1 -> 10`: its two-state reachable
  closure is finite, but the strict system makes `(01,10)` nonproductive.
  This forbids deleting the exclusion premise.
- State the reachability finiteness premise explicitly in every named
  forward implication. No counterexample to a standing PIP conjecture
  is asserted by the generic calibration.
- Productivity means that a path to a coincidence exists for each
  reachable state. It is not a universal assertion about every path.
- This is standard finite graph reasoning bound to actual word
  reduction, not a novelty claim about the balanced-pair criterion.

Proceed with this scope. A future unconditional named termination result
needs a separately checked finite forward-child carrier. General C4, G1,
spectral purity and PSC are not promoted by this increment.
