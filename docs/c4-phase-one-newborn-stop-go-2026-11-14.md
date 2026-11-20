# Source review for phase-one newborn seams

This continuation of [issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461) asks whether a proposed two-ended phase-one carrier has any possible newborn seam. The new filter must retain physical orders, check the previous generation's orientation on equal prefixes or suffixes, and use actual witnessed edges at both ends.

| Source | Transfer and scope |
| --- | --- |
| [Bernat, Study of irreducible balanced pairs](https://doi.org/10.1051/ita:2007062) and [Sirvent–Solomyak](https://doi.org/10.4153/CMB-2002-062-3) | Literal complete balanced factorization and half-coincidences are the relevant cut semantics. A local candidate is an overapproximation and has no guaranteed whole-word realization. |
| [Barge–Diamond, Theorem 1](https://doi.org/10.24033/bsmf.2433) | Actual aligned coincidence on a pair of letters gives the hub by exclusion. Apply separately to the reversed substitution for the right end. The checker must not treat endpoint-map compatibility as a witness. |
| [Durand, A characterization of substitutive sequences using return words](https://arxiv.org/abs/0807.3322) | The substitution-language setting applies to legal factors. For possible seams, the required legal bigram closure is derived directly from image interiors and actual boundary inheritance. No return-substitution theorem is imported. |

The existing [phase-zero seam filter](c4-legal-seams-2026-11-04.md) and
[newborn residue proof](c4-seam-birth-orbits-2026-11-04.md) use a fixed ordered
hub at each end. In phase one the child tracks are switched relative to
the parent. The [period theorem](c4-strict-component-period-2026-11-14.md)
fixes the relative position of the two hubs for every state normalized
with its left hub on top.

**Decision.** Reuse literal prefix/suffix counts, complete legal bigrams
and integral image-lattice tests. Extend the checks to both flipped
endpoints. Pair the finite replay with a source-level analysis of a
representative parameter family if a uniform birth exclusion appears.
Retain a productive PIP survivor and a genuine strict reducible survivor
to delimit the implication. An empty finite superset suffices for a
conditional exclusion, but a surviving seam never certifies closure.

**Follow-up decision.** The family endpoint pairs alone determine the four possible ordered seams. The residue and bilateral-image-boundary contradictions are independent of the hub phase. Replay the more general checker with both parent orders as well as the phase-one version.
