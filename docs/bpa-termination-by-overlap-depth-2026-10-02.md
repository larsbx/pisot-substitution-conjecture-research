# Balanced-pair termination from overlap depth — 2026-10-02

**Status:** Proposition 1 is a conditional statement proved here: it assumes
productivity of the seed-patch overlap graph from every swap seed. Corollary
2 is a finite-domain theorem for one substitution, resting on Proposition 1
and an exact Mojo certificate. Remark 3 records the finite-domain
consequence for the total-length class. This note does not prove G1 or
G1b-2 in general, does not prove the overlap-productivity gate of issue #84,
and records Proposition 1 in the ledger as a conditional theorem whose open
premise is all-seed overlap productivity (§5).

## 1. Setting

`sigma` is a primitive irreducible Pisot substitution on `A = {0,1,2}` with
incidence matrix `M`, Perron root `beta` and positive left eigenvector `ell`
(`ell M = beta ell`), read as tile lengths. `B_sigma` is the repository's
balanced-pair graph: the closure of the seeds `(ab, ba)`, `a < b`, under
`(u, v) -> ` the irreducible balanced pieces of `(sigma u, sigma v)`
(`substitution_dynamics.balanced_pairs`). The seed-patch overlap graph is the
graph of manuscript Theorem 4.22, built from the three swap seeds
(`psc.overlap_seed_patch`); it is finite for every such `sigma`.

Two facts are used.

- **Cuts are simultaneous boundaries.** Because the characteristic polynomial
  is irreducible, the coordinates of `ell` are linearly independent over `Q`.
  So two words have equal geometric length `<ell, pi(.)>` exactly when they
  have equal Parikh vectors. A balanced cut of a pair at symbolic position
  `L` is therefore the same thing as a point that is a tile boundary of both
  tilings, and the symbolic indices on the two sides then agree.
- **Pieces at level n are gaps.** By induction on `n`, the states of
  `B_sigma` reached at level `n` from the seed `(ab, ba)` are exactly the
  pieces of `(sigma^n(ab), sigma^n(ba))` between consecutive balanced cuts:
  a cut of a parent pair stays a cut after inflation, so decomposing the
  pieces of level `n` gives the pieces of level `n + 1`. The overlaps of the
  two level-`n` tilings are the depth-`n` descendants of the seed overlaps of
  `(ab, ba)`, which are vertices of the seed-patch overlap graph: inside the
  first period `[0, ell_a + ell_b)` the periodic swap patches are `ab` and
  `ba`, and both have a boundary at its right end.

## 2. Proposition 1 (bounded gaps from finite overlap depth)

*Suppose every vertex of the seed-patch overlap graph of `sigma` is
productive, and let `D` be the largest first-coincidence depth over its
vertices (finite, since the graph is finite). Then every state of `B_sigma`
reached at a level `n >= D` has geometric length at most
`2 beta^D ell_max`, where `ell_max = max_a ell_a`. Consequently `B_sigma` is
finite.*

*Proof.* Fix a seed `(ab, ba)` and a level `n >= D`, and let `t` be a point
of `[0, beta^n (ell_a + ell_b))`. The level-`(n - D)` tilings of
`sigma^(n-D)(ab)` and `sigma^(n-D)(ba)`, scaled by `beta^D`, are partitioned
into scaled overlaps, and `t` lies in the closure of one of them, `R`. `R` is
the scaled image of an overlap `O` of geometric length at most `ell_max`, so
`|R| <= beta^D ell_max`. `O` is a vertex of the graph, hence has a coincident
descendant at some depth `k <= D`; the children of a coincident tile are
coincident, so it has one at depth exactly `D`, and that tile lies inside
`R` in the level-`n` tilings. Its endpoints are simultaneous boundaries, so
`t` is within `beta^D ell_max` of a balanced cut. Two consecutive cuts are
therefore at most `2 beta^D ell_max` apart, and every piece of
`(sigma^n(ab), sigma^n(ba))` — every state reached at level `n` — is no
longer than that.

States reached at levels below `D` are finitely many, since each level has
finitely many pieces. States reached at levels `n >= D` have bounded
geometric length, hence symbolic length at most `2 beta^D ell_max / ell_min`,
and there are finitely many pairs of words of bounded length. So `B_sigma`
has finitely many states. `square`

The hypothesis is productivity from **every** swap seed: `B_sigma` is the
union of the three seed closures (`docs/bpa-literature-bridge.md` §4), and
the proof bounds each closure by the depth of its own seed's descendants.
That is stronger than the one-seed gate that manuscript Theorem 5.38 needs.

## 3. Corollary 2 (the cube-image specimen)

*For `sigma: 0 -> 1, 1 -> 222, 2 -> 0222`, `B_sigma` is finite, and every
state has symbolic length at most 45,136,797,534.*

*Proof.* The characteristic polynomial is `x^3 - 3x^2 - 3`, with
`beta ≈ 3.27902` and `ell = (1, beta, beta^2/3) ≈ (1, 3.27902, 3.58399)`, so
`ell_min = 1` and `ell_max = beta^2/3`. The regression
`test_the_cube_image_specimen_has_a_productive_depth_19_overlap_graph` in
`mojo/tests/test_overlap_seed_patch.mojo` certifies, in exact arithmetic,
that its seed-patch overlap graph from all three swap seeds has 1,142
vertices, is not capped, has no nonproductive vertex, and has largest
first-coincidence depth `D = 19`. Proposition 1 applies, and
`2 beta^19 ell_max / ell_min ≈ 4.5137e10`. `square`

This explains the exploratory record of
`docs/lost-depth-indexed-formulation-2026-10-01.md` §7: the bounded sweep
and the probe exhausted state-length budgets of 100,000 to 400,000 letters,
while the longest state grew by a factor close to `beta`. That is growth
towards a bound of order `10^10`, not evidence of an infinite automaton. The
bound is crude; the true longest state may be far shorter, but it is not
within reach of a direct build.

## 4. Remark 3 (the total-length class)

The exploratory overlap sweep of
`docs/lost-depth-indexed-formulation-2026-10-01.md` §6 is exhaustive and
deterministic over the 24,486 primitive irreducible Pisot substitutions with
total image length at most 8, and decided productivity exactly for every
specimen: every graph was built uncapped and none has a nonproductive
vertex. Proposition 1 therefore gives a finite `B_sigma` for every member of
that class, including the 120 longest-image-4 specimens whose direct builds
exhaust the state-length budget. This is a finite-domain consequence of
Proposition 1 and that sweep's exact verdicts; it is not a statement about
substitutions outside the class.

## 5. What this does not establish, and what review should decide

- It does not prove G1 or G1b-2 in general. Proposition 1 reduces finite
  `B_sigma` to productivity of the seed-patch overlap graph from every swap
  seed, which remains open.
- It does not touch the one-seed gate of issue #84 or Open Problem 5.35.
- The ledger records Proposition 1 as `G1OverlapRoute`, a conditional theorem
  whose open premise is the new gate `AllSeedOverlapProductivity`
  (`scripts/make_ledger.py`; `docs/proof-ladder.md`, "Overlap-depth route to
  G1"). `docs/cross-program-bridge-psc-nlapjt-2026-09-12.md` §5 (B1) already
  identifies G1b-2 with bounded gaps between simultaneous boundaries;
  Proposition 1 supplies that bound from overlap depth, for the reachable
  swap-pair states, without a realization hypothesis. The manuscript text
  is not changed here.
