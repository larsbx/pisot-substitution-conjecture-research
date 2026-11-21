# The ordinary tiling action for the parameter family

## Source decision

Proceed with the ordinary legal hull of the literal substitution
`0 ↦ 1, 1 ↦ 0 1^k 2, 2 ↦ 001` for `k ≥ 2`. The objective is to check the
geometric object and standing hypotheses used in the existing spectral
application, using the same substitution, Perron root and swap seed.

- [Barge–Štimac–Williams, §§2–3 and Corollary 2](https://doi.org/10.3934/dcds.2013.33.579)
  use the primitive, aperiodic, finite-local-complexity geometric substitution
  with Perron lengths. The two-letter swap criterion accepts determinant two.
- [Solomyak–Treviño, §§2.1–2.2](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/C9F722B2D26B94B06D3078A2A6136335/S0143385723000640a.pdf/spectral-cocycle-for-substitution-tilings.pdf)
  give the ordinary patch topology and the recognizability theorem for
  aperiodic FLC substitution tilings. The standing hypotheses can be checked
  on the repository hull before any recognizability theorem is used.
- [Barge–Kwapisz, geometric coincidence](https://math.montana.edu/jarek/documents/papers/AJM2006.pdf)
  assumes unimodularity. The family has determinant two, so use the
  balanced-pair implication above for the current application.

Use the existing half-open labelled tiles and `LocalHull` topology. A
label-preserving passage to closed interval supports leaves tile positions
intact and induces the same local topology by enlarging each test window.
The existing Thue–Morse hull supplies a control: an inflation-fixed tiling
can exist with rational expansion, so its existence does not establish
irrationality or the irreducible Pisot hypothesis.

The proof of Barge–Štimac–Williams Theorem 3.2 also identifies the next
geometric step. In the fundamental swap cell, the finitely many balanced
blocks have uniformly bounded inflated lengths. Their scaled-back lengths
shrink to zero, and each block eventually contains a common tile on the
two tracks. Use actual placed words and common tile **interiors** for this
step. The `k=2` control in the family rules out insisting on an immediate
coincidence for every block.

## Work shown

### Assumptions and hypotheses

The geometric substitution has words `σₖ`, Perron root `β` and lengths
`(β, β², β + 2)`. Its legal hull is inhabited for every `k ≥ 1`. For
`k ≥ 2` the full-factor theorem supplies finiteness and a coincidence
descendant for each factor reached from `01/10`. The parameter-one
spectral conclusion still follows from the published trace bound
recorded in the [family spectral note](c4-family-spectral-closure-2026-11-14.md).

### Derivation / reduction

1. The eigenvector identity gives the total length of every inflated
   word. The two tiles of `1.1` occur in `σₖ²(2)` and persist under
   `σₖ²`. Their nested inflations give a legal two-sided tiling fixed by
   the square of inflation.
2. A wide legal window contains a whole supertile at any prescribed
   level. Every letter occurs in each level-two image, so every finite
   window of any hull tiling occurs, up to translation, in every other
   hull tiling. The period group of the inflation-fixed tiling has a
   positive gap at zero from the length of one tile. A nontrivial such
   group would be cyclic and closed under multiplication by `β²`.
   This would make `β²` an integer. The cubic and irrationality of `β`
   in fact rule out every rational value of `β²`. Exact window recurrence
   transfers any putative period to the inflation-fixed tiling.
3. A bounded window fits inside a word bracketed by two tile vertices.
   The positive minimum tile length bounds the word length, so the window
   patches lie, after translation, in the powersets of a finite set of
   placed words. The translation action is jointly continuous under the
   existing ordinary local topology.
4. In each inflated swap cell the balanced factors partition both words
   into intervals with the same endpoints. The finitely many factors
   have lengths bounded by a common number `B`. At level `n` the
   factor containing `βⁿt` has length at most `B/βⁿ` in original units.
   Inflate that factor to any singleton coincidence and select the
   midpoint of its common tile. Pulling the midpoint back gives a point
   arbitrarily close to `t` where the two inflated tracks coincide on a
   tile interior. The period of the cell is `β+β²`, and the shift from
   the repeated `01` pattern to the repeated `10` pattern is `β`. Every
   integer translate of the cell has the same scaled-back coincidence
   witnesses. This gives dense eventual coincidence on the whole line,
   including arbitrarily close to cell boundaries. The rotation ratio
   `1/(1+β)` is irrational, and the swap translation has a dense orbit
   on the circle of one period.

The new endpoints are in
[C4ParameterFamilyTiling.lean](../proof/PscVerif/PscVerif/C4ParameterFamilyTiling.lean).
The interval argument uses the reusable
[balanced geometry](../proof/PscVerif/PscVerif/PeriodicPartnerBalancedGeometry.lean)
and [hull patch](../proof/PscVerif/PscVerif/PeriodicPartnerHullPatches.lean)
lemmas.

### Evidence and replay

The family audit checks literal endpoint types and rejects a missing
declaration, a theorem with the wrong type and reliance on any axiom outside
Lean's standard axioms. The hosted workflow runs the isolated gate at the
checked-out revision.

```sh
./tools/setup_lean.sh
./tools/check_c4_parameter_family.sh
python3 tools/make_proof_bank.py --check
```

### Negative controls

The prior `k = 2` control has a block without an immediate coincidence child.
The proof above uses any later coincidence and never prescribes the first
child. The original identity-substitution control has a finite set of
balanced factors and no coincidence, so finiteness alone does not give the
geometric density conclusion.

### Non-claims / remaining gaps

The [legal-patch follow-up](c4-family-legal-coincidence-2026-11-21.md)
checks the transfer from periodic patterns to legal patches and the
closed-origin argument for periodic partners. The remaining formal chain
uses the structure of the maximal equicontinuous factor of the literal
hull. Its final endpoint should assert that the span of translation
eigenfunctions is dense in the invariant measure's `L²` space. The
published Corollary 2 already gives the paper-level result.

At base revision `8bbc05b898b48b3ad97fcab0534a128998ec9677` the broader endpoints
are distinct research obligations.

| Obligation | Shortest remaining target |
| --- | --- |
| [BH #139](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/139) | For each cyclic, seed-reachable strict zipper, construct one composable occurrence-indexed path to offset zero. Reuse the completed Class-A entry argument at its exact scope. The remaining coverage theorem includes the full nonunit representation. |
| [Residual A1′ #138](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/138) | Prove one-sided eventual coincidence for the residual first-letter-fixed hub pair. An equal-Parikh prefix with the same next letter is sufficient. The uncovered non-crossing Theorem K cells give the narrower first target. |
| [C4 #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461) | The [graph-spectrum bridge](c4-graph-spectrum-review-2026-11-21.md) supports the written nonunit rank-two strict-system exclusion. For arbitrary rank-two nonunit hulls, the [parity and cohomology derivation](c4-nonunit-rank-two-residue-2026-11-21.md) leaves `K₂,₂` with two non-injective endpoint maps and nilpotent incidence modulo two. The residue needs a new geometric obstruction. Unit determinant, higher rank and extraction of a finite strict carrier from arbitrary failure remain separate. |
