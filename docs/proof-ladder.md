# Proof ladder

The current shortest route to the Pisot Substitution Conjecture in the standing regime has **one open mathematical premise**: seedwise overlap productivity. The finite-BPA/G1 and closed-carrier programmes remain important stronger structural routes, but they are no longer prerequisites of the shortest PDS sufficiency theorem.

For detailed claim status use `docs/claim-status-and-source-map-2026-09-13.md`; for the current weekly snapshot use `docs/completion-ledger-2026-09-14.md`; theorem statements and imported hypotheses are in `manuscripts/PSC_balanced_pair_state_2026-09-13.tex`.

# Stable base — incidence rank, UD, and bounded discrepancy

Established on `main`:

1. `det M_sigma != 0` gives full incidence rank / letter injectivity.
2. The defect theorem gives unique decodability of the image code `{sigma(a)}`.
3. UD propagates to powers because `det M_{sigma^r}=(det M_sigma)^r != 0`.
4. G1b-1 bounded discrepancy is repository-proved by the independent reconstruction merged in PR #69.

UD is therefore a theorem, not an independent standing hypothesis. Bounded discrepancy bounds the prefix-difference walk, not balanced-state length.

The old predecessor-contraction claim and the inference `UD => bounded total padding => finite BPA` are withdrawn permanently.

# Primary completion ladder — finite seed-patch overlaps, no G1

The current shortest honest chain is

```text
primitive irreducible Pisot
=> bounded discrepancy                                  [PROVED]
=> finite seed-patch overlap graph                      [PROVED]
=> one swap seed has only productive reachable overlaps [OPEN]
=> coincidence density one / dense good set             [PROVED equivalence]
=> pure discrete spectrum                               [IMPORTED theorem]
```

## Finite seed-patch overlap graph

**Repository-proved.** Manuscript Theorem 4.22 / PR #72 shows that every exact overlap type reachable from a swap seed lies in an explicitly bounded integer-coordinate set derived from G1b-1. This graph is finite without assuming finite BPA, Meyer structure, or unimodularity.

## Overlap productivity — the current critical gate

**OPEN (Open Problem 5.35).** For every PIP substitution it is enough to prove existence of one legal pair `a != b` such that every overlap reachable from the seed overlaps of `(ab,ba)` is productive.

Proving productivity for every seed or every vertex in the union graph is stronger than necessary for manuscript Theorem 5.38.

The strongest current algebraic reduction is Corollary 5.34 / PR #76. If `S` is a nonempty child-closed set of noncoincidence overlap types, then its intersection-vector span is a nonzero rational `M_sigma`-invariant subspace. Irreducibility forces

```text
rank V_S = |A|
```

and the child-count matrix inherits every Galois conjugate of the Perron eigenvalue. A hypothetical bad set is therefore algebraically **full rank**, not rank-deficient.

The best immediate contradiction target is a minimal reachable child-closed nonproductive set `S`:

```text
minimal bad S
=> full rational intersection-vector rank
=> inherited child-count spectrum
=> ordered descendant / prefix-Parikh constraints
=> boundary hit or contradiction.
```

## Coincidence density and PDS bridge

**Repository-proved:** Lemma 5.36 identifies seedwise overlap productivity with coincidence density one and density of the eventual-coincidence good set. The proof does not assume that the finite-stage good sets are nested; the corrected argument uses the finite subdivision-point difference between stages.

**Imported theorem:** Barge–Štimac–Williams supplies the dense-eventual-coincidence-to-PDS implication in the precise one-dimensional Pisot-family setting checked in manuscript Imported Theorem 5.37. Hence Theorem 5.38 has no G1 hypothesis.

## Endpoint-aligned boundary case

PR #82 proves:

- swapping tiling sides preserves productivity;
- offset-zero and right-aligned seed overlaps are productive exactly in the prefix/suffix strong-coincidence cases;
- an overlap reaches an offset-zero descendant at level `m` exactly when `M^m w` is a difference of proper-prefix Parikh vectors, equivalently when inflated subtiles have a common left endpoint;
- under strong coincidence, productivity reduces to this boundary-hitting statement.

This sharpens Open Problem 5.35 but does not solve arbitrary interior overlaps.

# Stronger route A — Level 2 / finite BPA

The stronger Level-2 ladder remains

```text
primitive + Pisot spectrum
=> bounded discrepancy (G1b-1)       [PROVED]
=> renewal finiteness (G1b-2)         [OPEN]
=> finite BPA (G1).
```

## G1b-2 — renewal finiteness

**OPEN; equivalent to G1 after G1b-1. Not required by Theorem 5.38.**

Prove that only finitely many reachable irreducible balanced pairs occur inside the established discrepancy bound. A bounded difference alphabet does not suffice because labelled first-return words can revisit the same nonzero difference vertices indefinitely.

The structural target is

```text
realizable labelled first-return words
=> level-scaled contracting/Rauzy address
=> finite-return / uniform-discreteness theorem
=> G1b-2.
```

The proof must remain non-unimodular-safe:

- no `|det M|=1` assumption;
- no purely Euclidean internal-space assumption where a profinite/non-Archimedean factor is required;
- no claim that `pi_s(Z^A)` is a lattice;
- preserve label/order data lost by cumulative difference walks.

### Retired Level-2 shortcuts

Do not use:

- UD implies bounded total padding;
- bounded discrepancy implies finite BPA;
- naive zero-sum-hyperplane contraction;
- every long state has a uniformly short core;
- two-letter renewal is trivial;
- unlabelled cumulative difference walk determines a balanced state.

# Stronger route B — SCC Producer under G1

Assume G1. Nonproductivity then reduces to a finite closed/sink recurrent noncoincident carrier.

The current spectral split is

```text
closed recurrent carrier
=> K2 == 0 or K2 != 0
=> [OPEN] concentration or [OPEN] wedge productivity
=> productivity
=> SCC Producer.
```

## Concentration / aux-B

**OPEN.** Equivalent in the current cubic wedge dichotomy to excluding strict components with `K2 == 0`.

The archived degree-three theorem applies only to its explicit seeds. The live degree-two carrier-span statement is independently repository-proved; no missing v16 source is required.

## Wedge productivity

**OPEN.** Equivalent to excluding strict components with `K2 != 0`. Full rational wedge span is a classification constraint, not a productivity theorem.

The exact 4,554-member corpus has fail-closed finite-domain certificates excluding both first-defect branches in their stated domains. Those certificates are not uniform theorems.

## Relation to the overlap route

A proof of general overlap productivity is stronger than needed to bypass G1 and, under G1, supplies productivity of all reachable BPA states. Therefore the overlap theorem can feed SCC Producer, but the finite-BPA carrier route is not required to prove Theorem 5.38.

# Supporting structural machinery

The following remain theoremically useful where their individual notes mark them theorem-grade:

- sink-SCC reduction under G1;
- endpoint synchronization quotient and A/B eliminator;
- Barge–Diamond type-G eliminator and hub-star normal form;
- Parikh intertwiner `P_C N_C = M_sigma P_C`;
- orientation monodromy and signed child-count matrices;
- signed first-defect intertwiners;
- degree-3, degree-4 and generalized-Witt spectral sieves;
- ordered degree-2 mid-area factorization and integral filters;
- bounded-gap zero-return calculus;
- finite Pisot ancestry states and legal ancestry towers;
- derived recognizability and relative hierarchy-offset states.

The C4 chain

```text
C4 => C3-local => C2 => C1
```

remains a valid one-way sufficiency route. It is not the headline completion ladder.

# Realization / MEF route

The realization programme remains an open bridge / certificate route. Its audited interface has obligations G0–G6. Do not identify:

```text
formal producer-free recurrence
= global realization
= survival to a finite collar bound.
```

Finite collar death is evidence until an independent completeness theorem is available.

# Exact finite calibration

Across the exact 4,554 short-image ternary PIP corpus:

- G1b-1 cross-check: maximum reachable discrepancy `14`, with reachable state length at least `48,020`;
- every BPA build used by the finite certificates terminates below its fail-closed cap;
- seed-patch overlap graphs: `4,554 / 0 / 0` built/capped/failed;
- total overlap vertices: `1,118,850`;
- largest overlap graph: `2,640`;
- specimens containing a nonproductive overlap: `0`;
- maximum first-coincidence depth: `18`;
- maximum first left-aligned depth: `17`;
- maximum prefix and suffix strong-coincidence depths: `15`;
- all specimens satisfy the tested two-sided strong-coincidence condition;
- the degree-two and degree-three finite carrier certificates have zero survivors in their stated domains.

These are exact finite-domain results/evidence according to their individual completeness contracts. They do not prove the general conjecture.

# Hypothesis firewall

Every proposed completion proof must preserve:

1. **Tile-length independence is derived.** Do not add rational/integer independence as a separate PSC hypothesis when irreducibility supplies it.
2. **UD is derived.** Do not make unique decodability a standing assumption.
3. **FI/boundary injectivity is extra.** Do not silently restrict to permutation/injective boundary maps.
4. **No unimodularity leak.** Unit-only converse theorems or Euclidean-only Rauzy constructions remain restricted unless separately generalized.
5. **No false stable lattice.** `pi_s(Z^A)` is generally not a discrete lattice.
6. **No realization shortcut.** Formal recurrence does not imply global realization.
7. **No computational self-certification.** Finite corpus/collar bounds require an independent completeness theorem before universal use.

# Completion order

1. **P0 — synchronization.** Keep manuscript, claim/source map, conjecture ledger, proof ladder, README and TLA dependency comments aligned.
2. **P1 — overlap productivity.** Prove the one-seed form of Open Problem 5.35. This is the only open premise on the current shortest PDS route.
3. **P2 — minimal bad overlap set.** Combine full-rank child-closed algebra with ordered prefix-Parikh/boundary-hitting structure and Pisot contraction.
4. **P3 — G1b-2.** Continue as a stronger independent theorem on BPA finiteness, with the non-unimodular firewall intact.
5. **P4 — concentration and wedge productivity.** Continue as the alternative finite-BPA/SCC route.
6. **P5 — realization bridge.** Discharge G0–G6 only if pursuing the coincidence-rank/collar certification route.

No additional fixed-size SCC sieve should displace P1 unless it supplies a credible uniform theorem feeding the overlap gate.
