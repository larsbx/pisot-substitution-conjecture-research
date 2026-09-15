# Conjecture ledger

The machine-checked dependency form is `tla/Ledger.tla`. This prose ledger distinguishes repository proofs, imported theorems, finite-domain theorems, open gates, open bridges, empirical evidence, and retired claims. The concise status/source index is `docs/claim-status-and-source-map-2026-09-13.md`; the current architecture is `docs/current-proof-architecture-2026-09-14.md`; the latest weekly snapshot is `docs/completion-ledger-2026-09-14.md`.

## Executive status — one shortest-path gate, several stronger parallel programmes

The Pisot Substitution Conjecture remains open.

The **shortest current PDS sufficiency route** has one open premise:

| Route item | Status | Load-bearing statement |
| --- | --- | --- |
| G1b-1 bounded discrepancy | **Repository-proved** | all reachable swap-state prefix-difference walks are uniformly bounded |
| Seed-patch overlap graph finiteness | **Repository-proved** | every swap seed has a finite exact overlap graph |
| **Seedwise overlap productivity** | **OPEN — current critical gate** | for every PIP substitution, one legal swap seed has only productive reachable overlaps |
| Coincidence-density / dense-good-set equivalence | **Repository-proved** | productivity gives density one / dense eventual coincidence |
| Dense eventual coincidence to PDS | **Imported theorem** | Barge–Štimac–Williams, hypotheses audited in the manuscript |

Therefore manuscript Theorem 5.38 proves PDS from overlap productivity **without G1**.

Three stronger programmes remain open in parallel:

1. **G1 / BPA finiteness:** G1b-2 renewal finiteness.
2. **Finite-BPA SCC route:** concentration (`K2 == 0`) and wedge productivity (`K2 != 0`).
3. **Realization / coincidence-rank route:** audited open bridge obligations G0–G6.

These are not hidden assumptions of the primary overlap route.

## A. Stable base

### Full incidence rank and unique decodability

**Status: repository-proved.** Full incidence rank follows from the standing irreducible/nonzero-determinant setup. The defect theorem gives unique decodability of substitution images, and the same holds for powers because `det M_{sigma^r} != 0`.

UD is derived, not assumed.

### G1b-1 bounded discrepancy

**Status: repository-proved by reconstruction (PR #69).** Every reachable state has bounded prefix-difference discrepancy, using primitivity and the Pisot spectrum only. It does not assume unimodularity or UD and does not imply finite BPA.

Finite calibration over the 4,554-member corpus reports maximum discrepancy `14` and a reachable state of length `48,020`.

## B. Primary open gate — overlap productivity

### Seed-patch overlap finiteness

**Status: repository-proved (PR #72).** Bounded discrepancy yields an explicit finite coordinate bound on exact overlap types reachable from the swap seeds. This does not require G1.

### Overlap productivity / Open Problem 5.35

**Status: OPEN.** It is sufficient to prove the one-seed form:

> For every PIP substitution there exist letters `a != b` such that every exact overlap reachable from the seed overlaps of `(ab,ba)` is productive.

All-seed or all-vertex productivity is stronger than manuscript Theorem 5.38 requires.

### Full-rank constraint on a bad set

**Status: repository-proved (PR #76).** For a nonempty child-closed set `S` of noncoincidence overlaps, the intersection-vector row span is a nonzero rational `M_sigma`-invariant subspace. Irreducibility therefore forces full rank; the child-count matrix inherits the Galois spectrum of `M_sigma`.

This corrects the former rank-deficiency heuristic. Full rank is a constraint, not a contradiction.

### Endpoint and boundary-hitting structure

**Status: repository-proved (PR #82).** Offset-zero and right-aligned seed overlaps are exactly the prefix/suffix strong-coincidence boundary cases. An overlap has an offset-zero descendant at level `m` iff `M^m w` is a difference of proper-prefix Parikh vectors, equivalently iff inflated descendants have a common left endpoint. Under strong coincidence, productivity reduces to this hitting condition.

The remaining obstruction can therefore be assumed genuinely interior and boundary-avoiding.

### Coincidence density and PDS

**Status: repository-proved + imported theorem (PR #77).** Lemma 5.36 supplies the repository equivalence between overlap productivity, coincidence density one, and a dense good set. Barge–Štimac–Williams supplies the dense-eventual-coincidence-to-PDS implication. The finite-stage good sets are not nested; the corrected proof uses only finite subdivision-point losses between stages.

## C. Parallel programme — G1 / renewal finiteness

### G1b-2

**Status: OPEN.** Since G1b-1 is proved, G1b-2 is the exact missing theorem for finite BPA.

Required statement: only finitely many realizable irreducible balanced pairs occur inside the established discrepancy bound.

A bounded local difference alphabet does not bound labelled first-return data. The intended structural route remains:

```text
realizable labelled first-return words
=> level-scaled contracting/Rauzy address
=> finite local return types / uniform discreteness
=> G1b-2
=> G1.
```

This programme is no longer completion-critical for Theorem 5.38, but it remains the canonical route to the stronger finite-BPA theorem.

## D. Parallel programme — SCC Producer under G1

Assume G1. Then nonproductivity reduces to a finite closed/sink recurrent noncoincident carrier.

### Concentration / aux-B

**Status: OPEN, not source-pending.** In the current cubic wedge dichotomy this is equivalent to excluding strict components with `K2 == 0`.

### Wedge productivity

**Status: OPEN, not source-pending.** Equivalent to excluding strict components with `K2 != 0`. The degree-two carrier-span implication is repository-proved, but full rational wedge span alone does not force productivity.

### Exact bounded-domain carrier results

Two fail-closed Mojo certificates give finite-domain theorems on the exact 4,554-member short-image corpus:

- no strict `K2=0`, first-`K3` component;
- no closed nonproductive recurrent nonzero-`K2` component.

Neither is a uniform theorem.

## E. Supporting structural programme

The C4/endpoint/defect hierarchy remains useful and theorem-grade where its notes say so. It includes sink-SCC reduction, endpoint synchronization, Barge–Diamond endpoint elimination, Parikh and signed defect intertwiners, orientation monodromy, higher-defect spectral sieves, ordered degree-two factorization, and recognizability/ancestry machinery.

The one-way chain

```text
C4 => C3-local => C2 => SCC Producer
```

remains a valid sufficiency chain. It is not the current shortest completion route.

## F. Realization / MEF bridge

**Status: OPEN bridge.** The source audit decomposes the former realization/coincidence-rank equivalence into obligations G0–G6.

Do not identify formal recurrence, global realization, and finite collar survival. Finite collar death remains evidence until an independent completeness bound is proved.

## G. Exact finite evidence

On the 4,554-member ternary PIP short-image corpus:

- all finite-certificate BPA builds terminate below their fail-closed caps;
- maximum reachable discrepancy: `14`;
- longest reachable state in the G1b-1 cross-check: `48,020`;
- seed-patch overlap graphs built / capped / failed: `4,554 / 0 / 0`;
- total overlap vertices: `1,118,850`;
- largest overlap graph: `2,640`;
- specimens with a nonproductive overlap: `0`;
- maximum first-coincidence depth: `18`;
- maximum first left-aligned depth: `17`;
- maximum prefix and suffix strong-coincidence depths: `15`;
- every specimen satisfies the tested two-sided strong-coincidence condition.

These results strongly guide proof search but do not establish a universal image-length/alphabet-size completeness bound.

## H. Independence / unimodularity / realization firewall

The final theorem must preserve all of the following.

- **Tile-length independence is derived.** Do not add rational/integer independence as a separate assumption.
- **UD is derived.** Do not make unique decodability a standing hypothesis.
- **FI/boundary injectivity is extra.** It cannot enter the general proof silently.
- **No unimodularity leak.** Do not import `|det M|=1` through a converse or internal-space construction without marking the result restricted.
- **No false stable lattice.** Do not treat `pi_s(Z^A)` as a discrete lattice in general.
- **No realization shortcut.** A formal recurrent component is not automatically globally realized.
- **No computational self-certification.** A finite corpus or collar radius becomes universal only with an independent completeness theorem.

## I. Retired claims / routes

Do not use as completion arguments:

- predecessor contraction proving finite BPA;
- `UD => bounded total padding`;
- bounded discrepancy alone implying finite BPA;
- naive zero-sum-hyperplane contraction;
- uniformly short core in every long state;
- trivial two-letter renewal;
- unlabelled difference walks determining balanced states;
- rank-deficiency of a child-closed bad overlap set;
- nested finite-stage good sets in the coincidence-density proof.

## J. Source/provenance status

The missing historical v16 manuscript remains provenance metadata, not a live proof prerequisite.

- G1b-1 is independently repository-proved.
- Degree-two carrier span is independently repository-proved.
- Concentration is an open mathematical gate, not a missing-source theorem.
- The realization chain is an open bridge, not a missing-source theorem.
- The P0 manuscript hypothesis/attribution corrections have been implemented in the live manuscript.

## K. Priority ledger

1. **P0 — status synchronization.** Keep manuscript, claim/source map, proof ladder, this ledger, README and TLA comments consistent.
2. **P1 — seedwise overlap productivity.** Current critical theorem target.
3. **P2 — minimal bad overlap set contradiction.** Use full rank, inherited spectrum, ordered descendants and boundary-hitting/Pisot contraction.
4. **P3 — G1b-2.** Stronger finite-BPA theorem; preserve non-unimodular generality.
5. **P4 — concentration and wedge productivity.** Alternative finite-BPA SCC route.
6. **P5 — realization bridge.** Secondary certificate route.

The project should not spend the primary proof budget on another fixed-size SCC sieve unless it supplies a uniform theorem feeding P1.
