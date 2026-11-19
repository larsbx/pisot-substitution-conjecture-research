# Barge–Diamond word conclusion and vertex coincidence

Base assessed: `main@ec026774e666fb8e8ac43b1ba975b9a4df8891b2`.
The November 18 review was pinned to PR #608 at
`6b175ce350b8691563d8ea254e33bd84445860ef`. At the November 19 assessment
#608 remained open and conflicted. This change is independent of its
length-functional de-duplication and rank-at-most-two theorem.

## Work shown

### Assumptions and hypotheses

The correspondence needs a finite alphabet with decidable equality and any
substitution `s : α → List α`. It uses the existing `power`, `IndexWitness`,
`WitnessAt`, `EdgeDescendant`, `EdgeCoincident` and `VertexCoincident`
definitions. Nonerasure, primitivity, Pisot spectrum, property (F), stable
geometry and unimodularity are unnecessary for the correspondence.

| Published convention or requirement | Repository binding |
| --- | --- |
| Output letter i counted in the image of seed j | `inc s i j = (s j).count i`; no transpose change. |
| One common substitution iterate | `power s n a = (subst s)^[n] [a]`, with the same `n` on both tracks. |
| One-based matching position k | Zero-based `i = k - 1`; equal prefix counts force equal prefix lengths. |
| Matching letter and equal prefix abelianizations | `IndexWitness s a b n i i`, using `Equiv1`; `pvec_eq_iff` converts to integer Parikh vectors. Literal prefix equality is unnecessary. |
| Nonempty images and primitivity | PIP3's positive incidence power implies nonerasure by the existing `nonerasing_of_primitive`; `primitive_word_iteration` binds that power to membership in the actual words. |
| Expanding Perron eigenvalue | The existing positive left eigen-row and `one_lt_perron` give `1 < β`; `isRoot_of_pos_left_eigen` identifies the root. |
| Other roots have modulus strictly between zero and one | The existing Pisot condition gives the upper bound; `pip3_complex_root_ne_zero` obtains the lower bound from irreducibility of the degree-three rational characteristic polynomial. |
| Property (F) | An extra premise of the rank consumer, not of this bridge. |
| Distinct seed letters | Kept explicitly in `WordConclusion`; `indexWitness_level_pos` excludes iteration zero for such a pair. |

### Derivation / reduction

An occurrence `power s n a = P ++ c :: Q` in the inflated edge starting at
`x` has endpoint coordinate `M^n x + pvec P`. At the origin that coordinate
is exactly `pvec P`, with a positive prefix contribution. The descendant
retains its letter label. Thus, at each fixed level,

```lean
WitnessAt s a b n ↔
  ∃ z, EdgeDescendant s n (a, 0) z ∧ EdgeDescendant s n (b, 0) z
```

The reverse implication reads off equal prefix vectors from the common
labelled edge. The forward implication chooses `(c, pvec P)`. The existing
index/decomposition equivalence and alignment lemma then give

```lean
WordConclusion s ↔ ∃ a b, a ≠ b ∧ VertexCoincident s a b
```

`WordConclusion` is a named, source-pinned **external existence premise**.
Its definition supplies no witness and introduces no axiom. A caller of
#608's conditional theorem can translate a supplied word conclusion through
`wordConclusion_iff_hBD`; that rank theorem is not added or changed here.

The nonzero-root proof uses irreducibility to exclude the rational root zero
in degree three. Evaluation of the rational characteristic polynomial in
the complex numbers is the existing `Psc.BPrime.aeval_charpoly`. Injectivity
of the rational algebra map gives the contradiction. It assumes no unit
determinant and does not strengthen the source theorem.

### Primary-source decision

This ports the reviewed contract rather than proposing another universal
invariant. Proceed with the word/edge correspondence and explicit controls.
The published existence theorem and geometric rank identification remain
outside the new theorem statements.

| Primary source | Binding and scope boundary |
| --- | --- |
| [Barge–Diamond 2002, DOI 10.24033/bsmf.2433](https://www.numdam.org/article/BSMF_2002__130_4_619_0.pdf), Theorem 1 p. 620, definitions p. 621, restatement p. 622, controls p. 625 | Distinct seeds have a common letter after equal abelianized prefixes at one iterate. Pisot type requires nonzero contracting non-Perron eigenvalues. Its geometric existence proof is not replayed by the word correspondence. |
| [Barge–Kwapisz 2006](https://math.montana.edu/jarek/documents/papers/AJM2006.pdf), Definition 7.1 and (7.2)–(7.3), pp. 1237–1238 | Eventual coincidence shares a labelled edge and is translation equivariant. Its unimodular setting is not imposed on the present word bridge. |
| [Baker–Barge–Kwapisz 2006](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf), Definition 4.1 and Remark 4.3 | Geometric strand rank is identified with maxima of half-open edge states over a common fibre. This global identification does not follow from the integer word predicate alone. |

### Evidence and replay

The earlier source-extracted replay checked all 24 proposed named proofs and
audited 212 declarations under standard axioms. Those historical results
were limited to a source-bound standalone slice. This port additionally
attempts the actual modules in their full repository import environment.
The exact local terminal results are recorded in
`evidence/barge-diamond-bridge-2026-11-19/`.

The actual-import attempt did not reach the new modules within the local
run. It was stopped in existing dependencies (`CountBridge`, and `M0Pisot`
in the concurrent attempt). There was no reported rejection of the new
source, but this is not successful actual-module acceptance. The precise
boundary is in `local-import-attempt.json`; the new hosted isolated job was
queued at inspection. Integration remains pending that acceptance gate.

```sh
cd proof/PscVerif
lake build PscVerif.BargeDiamondBridgeControls
lake env lean BargeDiamondBridgeAudit.lean
```

The audit inspects every owned declaration in the actual import closure,
including definitions and generated helpers. It rejects local axioms and
axiom closures outside `propext`, `Classical.choice`, `Quot.sound`.
The dedicated hosted workflow copies source/configuration only into a fresh
workspace, clones pinned upstream dependencies, uses the fixed upstream
source-hash cache, compiles the actual modules and checks named-proof
coverage. Hosted completion is a separate receipt; queued checks are not
reported as passed. The complete isolated whole-library gate remains a
separate, broader check.

### Negative controls

| Control | Guarded distinction |
| --- | --- |
| Tribonacci `01/02/0`, level 1, index 0 | A valid PIP3 word conclusion translates to the vertex premise. |
| `010/110`, level 1, index 1 | Equal matching letters and prefix lengths do not give equal counts: `[0]` differs from `[1]`. |
| The second edge in `010` | The coordinate is `+e_0`; negative and forgotten zero offsets are rejected. |
| Thue–Morse `01/10`, level 1, index 0 | Equal prefix vectors without an equal label are insufficient. |
| BD's `121/221`, relabelled `010/110` | Suffix coincidence holds, but prefix coincidence fails at every level. |
| `0 ↦ 1, 1 ↦ 0` | Comparing levels zero and one gives a spurious shared edge; no synchronized level gives coincidence. |
| `012/102/2`, level 1, index 2 | Prefixes may differ literally while having equal abelianization. |

The negative specimens are outside PIP3. These are counterexamples to wrong
encodings, not new counterexamples to BD, universal C4 or PSC.

### Non-claims / remaining gaps

Barge–Diamond Theorem 1's existence proof remains external. Its bounded
configurations, maximal separated families and unstable-line lattice
contradiction are not introduced here. The BBK rank/zero-slice identification,
the remaining global rank-two exclusion and universal C4 are not discharged.
No governed claim or status is promoted. Independent human review remains
pending; it is distinct from the exact scoped mechanical checks.
