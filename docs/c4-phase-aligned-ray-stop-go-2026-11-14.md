# Source review for phase-restricted periodic rays

This pre-code review narrows [issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461) to the orientation of actual common starts in the periodic-ray overlap graph.

| Source | Transfer and scope |
| --- | --- |
| [Sirvent–Solomyak, Lemma 5.5 and Theorem 5.6](https://doi.org/10.4153/CMB-2002-062-3) | Half-coincidences correspond to balanced cuts through rational independence. Their bounded-gap result concerns fixed-point prefixes and translates. The aligned two-ray version is proved in the periodic-ray note. A common right endpoint can count for gap bounds, while a hub side is read only at a common start. |
| [Akiyama–Lee](https://arxiv.org/abs/1003.2898) | Finite overlap paths are a standard way to check coincidence. Keeping generation parity is a finite graph product. The new work binds each phase label to the direction of the literal hub on every balanced factor of the two fixed rays. |
| [Barge–Diamond, Theorem 1](https://doi.org/10.24033/bsmf.2433) | A genuinely coincident letter pair supplies the complementary hub. The executable verifies a literal witness for the supplied edge using the same complete aligned graph. The edge cannot be inferred from the first-letter map. |

The repository already proves [phase-zero orientation and terminal constraints](c4-oriented-alignment-2026-11-04.md), [constant first-child phase](c4-first-child-hub-phase.md), and [the per-source periodic-ray criterion](c4-periodic-ray-decision-2026-11-14.md). The phase-restricted criterion should work in phases zero and one, including transient overlaps inside the rooted graph. Equality of the physical overlap types at different depths cannot erase the depth parity when the hub flips. The #460 two-generation control and the reducible strict system remain required boundaries.

**Decision.** Proceed with the exact two-way criterion on fully closed rays, and replay shortest literal paths to a forbidden aligned start on genuine Pisot sources. This is a finite per-source exclusion, including cases where that alignment is found earlier than a diagonal of the same root. It is not an assertion of the disjunction uniformly over all sources. A synthetic edge or a cap cannot justify a source-level verdict.
