# Current PSC proof architecture — 2026-09-11

**Status:** canonical project-status ledger for the current research program. **Update 2026-09-13:** the merged manuscript `manuscripts/PSC_balanced_pair_state_2026-09-13.tex` is the authoritative status-tagged prose account; its Proposition 5.20 (wedge dichotomy) shows that the concentration step below is equivalent to excluding strict components with `K2 == 0`, and that the final spectral step is equivalent to excluding those with `K2 != 0`; both remain open (see `docs/conjecture-ledger.md`). This file records the present proof architecture and priorities. Former v16/later status claims have now been resolved claim by claim: G1b-1 and the degree-two carrier-span implication are repository-proved by independent reconstruction, while concentration and the realization/rank chain are open mathematical obligations rather than source-pending theorems. The missing historical file is recorded as provenance metadata, not used as a proof premise. The dated weekly ledger `docs/completion-ledger-2026-09-11.md` carries the full evidence tables and a per-item repository cross-check.

## Executive status

The proof is not complete. The original finite-BPA assembly has two genuinely independent gates. A later overlap/density architecture supplies a second, potentially G1-free route to PDS; its two open inputs are recorded separately below.

| Gate | Status | Remaining obligation |
| --- | --- | --- |
| Level 2 / G1: finiteness of the balanced-pair automaton | **OPEN** | G1b-2 renewal finiteness |
| Level 3 / SCC Producer | **OPEN at two independent obligations** in the strongest current spectral attack (updated 2026-09-13) | concentration (no strict component with `K2 == 0`) **and** wedge productivity (no strict component with `K2 != 0`); proving concentration alone does not close Level 3 |
| G1-free overlap route to PDS | **OPEN at two inputs** | productivity of every seed-patch overlap **and** the coincidence-density-one-to-PDS bridge; overlap-graph finiteness and the transfer to all BPA states are proved |

Unique decodability is not an open hypothesis. It is a theorem from `det M_sigma != 0` and must remain downstream of irreducibility/full incidence rank rather than being assumed independently.

The realization/MEF track is a parallel reformulation/certificate route, not a third proof gate. Its finiteness assumption is downstream of G1, and its load-bearing notion of global realization contains essentially the remaining coincidence obstruction.

## Level 2 — finiteness

The current intended chain is

```text
primitive + Pisot spectrum
=> bounded discrepancy (G1b-1)   [THEOREM, reconstructed 2026-09-13]
=> [OPEN] renewal finiteness (G1b-2)   (now equivalent to G1)
=> |B_sigma| < infinity.
```

### G1b-1 — bounded discrepancy

**Status. THEOREM (repository-proved, 2026-09-13).** Independently reconstructed, with a complete proof, in `docs/source-imports/issue-45/g1b1-bounded-discrepancy-reconstruction.md`; stated as Theorem 4.4 of `manuscripts/PSC_balanced_pair_state_2026-09-13.tex`. Every reachable state `T` of `B_sigma` satisfies

```text
Disc(T) <= D_sigma := 4 (|A| + 1) C_sigma,
```

with `C_sigma` an explicit constant from the contracting part of `M_sigma`. The proof uses only primitivity and the Pisot spectrum (every non-Perron eigenvalue inside the unit circle); it does not use unimodularity, unique decodability, or legality of seeds. It is a global bound on the prefix-difference walk of every inflated swap seed, not a child-versus-parent contraction: the reported estimate

```text
Disc(sigma w) <= c Disc(w) + 2 E_sigma,    c < 1
```

was not reconstructed and is not needed. Bounded discrepancy bounds the difference walk, not the state length; exact census: maximum discrepancy `14` and a reachable state of length `48,020` over the `4,554`-member corpus.

### G1b-2 — renewal finiteness

**Status: OPEN.** This is the exact Level-2 bottleneck, and with G1b-1 proved it is equivalent to G1 (manuscript Proposition 4.11).

Required statement: only finitely many reachable irreducible balanced pairs have `Disc(s) <= D_sigma`.

Bounded discrepancy alone is insufficient: a reduced difference walk can remain in a finite nonzero lattice box while having arbitrarily long first-return data.

The current computational anatomy reported by the v16 audit is:

- 135 difference vertices;
- 623 edges;
- 1,425 observed `(difference, local 2-window)` configurations;
- BFS discovery saturation by depth at most 43;
- realized first-return data of length at least 17,078;
- thousands of revisits to the same difference vertex.

These are finite observations, not a proof.

### Level-2 proof target

Do **not** seek another bounded norm. The target is a renewal/discreteness theorem of the shape

```text
realizable first-return words
=> level-scaled contracting/Rauzy address
=> uniform discreteness / finite return types
=> G1b-2.
```

The construction must be non-unimodular from the outset. In particular it must not silently assume that the internal space is purely Euclidean or that `pi_s(Z^A)` is a lattice.

## Level 3 — coincidence under G1

Assume G1, so the recurrent obstruction can be reduced to finite closed/sink behavior.

The strongest current route is

```text
closed recurrent carrier
=> split by K2 == 0 or K2 != 0
=> [OPEN] concentration or [OPEN] wedge productivity
=> productivity.
```

For the nonzero-`K2` branch, full rational wedge span is already
repository-proved by the wedge dichotomy. It clarifies the obstruction but
does not turn span into productivity.

Both bracketed arrows are open (2026-09-13): concentration is equivalent to `no strict component with K2 == 0`, wedge productivity to `no strict component with K2 != 0`; proving either alone does not close Level 3.

### Concentration / aux-B

**Status: OPEN; highest-leverage Level-3 obligation.**

The required statement is that the expanding wedge contribution generated by recurrent behavior has nonzero projection inside a closed recurrent carrier.

The old independent subdominant-nonvanishing obligations are removed by a self-contained argument on `main`: irreducibility of the exterior-square characteristic polynomial makes a nonzero invariant rational carrier span the whole wedge space.

**Provenance:** PR #68 separates this repository proof from the historical degree-three seed certificate. Aux-B is the open concentration statement itself, with formulation provenance but no claimed proof. See `docs/galois-aux-b-source-resolution-2026-09-13.md` and `docs/claim-status-and-source-map-2026-09-13.md`.

### Independence from G1b-2

Do not unify the two open gates artificially.

- concentration is an algebraic/nonvanishing problem on the recurrent closed carrier;
- G1b-2 is a contracting-side renewal/discreteness problem needed to prove that the BPA is finite in the first place.

Progress on one does not discharge the other.

## G1-free overlap/density route

Bounded discrepancy also produces a finite seed-patch overlap graph
`O_sigma` without assuming G1 (manuscript Theorem 4.22;
`docs/overlap-finiteness-and-coincidence-density-2026-09-13.md`).
Productivity of every overlap is equivalent to coincidence density one for
every swap seed and implies productivity of every reachable balanced-pair
state without a finiteness hypothesis (Theorem 5.32).

This yields the alternative assembly

```text
bounded discrepancy
=> finite seed-patch overlap graph                   [PROVED]
=> every overlap productive                          [OPEN]
=> every reachable BPA state productive              [PROVED implication]
=> coincidence density one gives PDS                 [OPEN bridge]
=> PDS.
```

This route can bypass G1 in a proof of PDS if both open inputs are established.
It does not prove G1 itself. The exact census finds all 1,118,850 overlap
vertices productive over the 4,554-member corpus, with largest graph size
2,640; those productivity counts remain finite evidence, not a general
overlap-productivity theorem.

The older finite-BPA route remains independently useful: G1b-2 is still exactly
the unresolved finiteness theorem, and under G1 the overlap formulation,
SCC Producer, and closed-carrier obstruction can be compared on a finite
graph.

## Supporting C4 / endpoint / recognizability machinery

The substantial C4 program on `main` remains valuable and theorem-grade where its individual notes say so. It supplies:

- sink-SCC reduction;
- endpoint synchronization quotient and A/B global eliminator;
- Barge-Diamond type-G eliminator and hub-letter normal form;
- Parikh and signed defect intertwiners;
- orientation monodromy and Perron-signing structure;
- first-child hub phase and system-level good-edge compatibility;
- exact finite defect-degree and three-state calibrations;
- legal ancestry towers;
- finite Pisot ancestry states;
- derived recognizability and relative hierarchy-offset states.

These should now be treated as **supporting structural reductions / alternative Level-3 route**, not as a substitute for the two-gate completion architecture above.

## Realization / MEF route

Under the finiteness hypothesis, the current realization program uses the normal form

```text
coincidence rank > 1
<=> non-eventually-coincident tilings in one MEF fibre
<=> a recurrent producer-free BPA component is globally realized.
```

This is conceptually valuable because it separates formal recurrence from genuine realization. It does not remove the need for G1, and “globally realized” is itself load-bearing.

Finite collar experiments therefore remain evidence only until an independently proved collar-completeness/death-radius theorem is available.

## Permanent independence / generality firewall

Future proof changes must preserve the following.

1. **Tile-length independence** must be derived from irreducibility/cyclic-vector structure, not assumed separately.
2. **Unique decodability** is a theorem from full incidence rank; do not add it as a headline hypothesis.
3. **Finite injectivity / boundary permutation hypotheses** are extra structure and may not enter the general theorem silently.
4. **Non-unimodularity:** no proof may assume unit determinant or a purely Euclidean internal space unless explicitly restricted to that case.
5. **Discreteness:** do not treat `pi_s(Z^A)` as a lattice in general.
6. **Realization:** a formal recurrent BPA cycle is not automatically globally realized.
7. **Computational completeness:** no collar depth or finite census proves universal completeness without an independent bound.

## Retired Level-2 routes

Do not reintroduce these without genuinely new input:

- UD implies bounded total padding;
- bounded discrepancy implies finitely many balanced pairs;
- naive zero-sum-hyperplane contraction;
- uniformly short core in every long state;
- two-letter renewal is trivial;
- unlabelled difference walks determine balanced states.

## Manuscript corrections completed

The audited 2026-09-13 manuscript implements:

1. **Aperiodicity:** primitivity on an alphabet of size at least two does not imply aperiodicity. Derive aperiodicity from the full standing hypotheses or retain it explicitly.
2. **Mosse recognizability:** it comes from primitive + aperiodic substitution structure, not from the Pisot property itself.
3. **Two-letter attribution:** distinguish Barge-Diamond strong coincidence for the two-letter case from Sirvent-Solomyak pure discrete spectrum / BPA-overlap results; cite Hollander-Solomyak only for the exact bridge actually used.
4. **Closed vs closed-nonproductive:** mass-balance conclusions requiring nonproductivity must say so explicitly.
5. **Span-rich status:** any statement depending on concentration remains conditional until aux-B is proved.

## Prioritized completion ledger

1. **P0 — status and reference synchronization.** Keep the manuscript, claim/source map, prose and TLA ledgers, and citations aligned. Preserve the missing-v16 fact as historical metadata; it is not a live proof prerequisite.
2. **P1-A — Level-3 closed-carrier obligations.** Concentration / aux-B (`K2 == 0` case) and wedge productivity (`K2 != 0` case); both are needed, and the finite evidence points to the `K2 != 0` case as the main one.
3. **P1-B — G1b-2 renewal finiteness.** Unavoidable for proving G1 and for the finite-BPA assembly; potentially bypassed only on the separate overlap/density route to PDS.
4. **P2 — non-unimodular firewall for G1b-2.** Build the contracting address in the correct Euclidean/profinite setting when required.
5. **P3 — SCC Producer assembly.** Once G1, concentration, and wedge productivity are all available, write the finite-graph assembly explicitly.
6. **P4 — realization/collar completeness.** Parallel certification route.
7. **P5 — final PDS bridge audit.** Check exact hypotheses of the selected literature bridge against the final BPA formulation.
8. **P6 — machine-checkable certificates.** Continue converting finite evidence into reproducible Mojo certificates without upgrading evidence to theorem status.

## Immediate next proof move

Work asymmetrically:

- attack the **Level-3 closed-carrier obligations** (concentration and wedge productivity); neither alone closes the route, and the `K2 != 0` case is the one realized by essentially all reachable states in the exact corpus;
- attack **overlap productivity** and the **density-to-PDS bridge** as the finite, G1-free alternative;
- in parallel, continue **G1b-2** for the stronger BPA-finiteness theorem, specifically realizable first-return words and a level-scaled non-unimodular contracting address.

The UD layer is finished. PDS can be completed either through the finite-BPA carrier assembly (G1 plus both Level-3 obligations and the final literature interface) or through the G1-free overlap assembly (general overlap productivity plus the density-to-PDS bridge). Neither route is complete.