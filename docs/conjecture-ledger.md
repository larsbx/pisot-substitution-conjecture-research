# Conjecture ledger

The machine-checked dependency form is `tla/Ledger.tla`. This prose ledger distinguishes deliberately between:

- results proved in the present repository;
- reconstructed results proved on `main`, historical restricted theorems, and missing-source metadata, kept as distinct categories;
- open proof gates;
- finite computational evidence.

The concise claim/source index is `docs/claim-status-and-source-map-2026-09-13.md`. The authoritative prose account of the mathematics, with every statement status-tagged, is the merged manuscript `manuscripts/PSC_balanced_pair_state_2026-09-13.tex` (referee report: `manuscripts/codex-referee-report-2026-09-13.md`; response: `manuscripts/response-to-reviewers-2026-09-13.md`). The current completion architecture is summarized in `docs/current-proof-architecture-2026-09-11.md`. The dated weekly completion ledger, with the repository cross-check of which reported results and figures are verifiable on `main`, is `docs/completion-ledger-2026-09-11.md`.

## Executive status — two independent gates

The proof is not complete. The remaining work separates into two independent obligations.

| Gate | Status | Load-bearing statement |
| --- | --- | --- |
| **Level 2 / G1** | **OPEN** | G1b-2 renewal finiteness |
| **Level 3 / SCC Producer under G1** | **OPEN at two independent obligations** in the strongest current spectral route | concentration / aux-B (`K2 == 0` case) **and** wedge productivity (`K2 != 0` case); see the 2026-09-13 clarification below |

Unique decodability is already a theorem from full incidence rank and is not an independent hypothesis.

## G1 — finiteness of the repository balanced-pair automaton

**Statement.** For every primitive irreducible Pisot substitution in the standing alphabet-three regime, the repository graph `B_sigma` is finite.

**Status. OPEN.**

The predecessor-contraction proof is permanently withdrawn. The current Level-2 decomposition is:

```text
primitive + Pisot spectrum
=> bounded discrepancy (G1b-1)   [THEOREM, reconstructed 2026-09-13]
=> [OPEN] renewal finiteness (G1b-2)   (now equivalent to G1)
=> finite BPA.

Unique decodability (a consequence of det M_sigma != 0) is a theorem but plays no role in this chain.
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

**Status. OPEN. This is the exact Level-2 bottleneck, and since G1b-1 is proved it is equivalent to G1 (manuscript Proposition 4.11).**

Prove that only finitely many reachable irreducible balanced pairs have `Disc(s) <= D_sigma`. (For any `R0 >= D_sigma` the corresponding statement is G1 itself; for `R0 < D_sigma` it follows from G1.)

Bounded discrepancy alone is insufficient: a labelled first-return walk may remain forever inside a finite nonzero difference box while accumulating arbitrarily long return data.

The target is therefore not another bounded norm. It is a renewal/discreteness theorem:

```text
realizable labelled first-return word
=> level-scaled contracting/Rauzy address
=> uniform discreteness / finite local return types
=> G1b-2.
```

The construction must preserve non-unimodular generality. In particular, it may not assume unit determinant, a purely Euclidean internal space, or that `pi_s(Z^A)` is a lattice.

**Evidence only.** The exact 4,554-PIP alphabet-three corpus terminates below the BPA cap in every case.

## Level 3 — SCC Producer under G1

### C1 — SCC Producer

**Statement.** Every recurrent noncoincident SCC of `B_sigma` is productive.

**Global status. OPEN until G1 plus the Level-3 carrier argument are assembled.**

Under G1, nonproductivity reduces to a finite closed/sink recurrent noncoincident SCC by `docs/sink-scc-reduction.md`.

### Strongest current closed-carrier route

The current repository-supported spectral route is

```text
closed recurrent carrier
=> split by K2 == 0 or K2 != 0
=> [OPEN] concentration or [OPEN] wedge productivity
=> productivity.
```

The nonzero-`K2` to full-wedge-span implication is already
repository-proved. It is an algebraic classification of a carrier, not a
productivity theorem.

Two arrows are open: concentration (equivalent to `no strict component with K2 == 0`) and wedge productivity (equivalent to `no strict component with K2 != 0`). Neither implies the other; see the 2026-09-13 clarification below.

#### Concentration / aux-B

**Status. OPEN; highest-leverage Level-3 obligation.**

Prove from first principles that expanding wedge mass generated by recurrent behavior has nonzero projection inside a closed recurrent carrier.

PR #68 resolved the former Galois/aux-B source ambiguity. The degree-two carrier-span implication is proved self-containedly by irreducibility of `chi_{Lambda^2 M}`; the archived degree-three Galois theorem is restricted to six seed defects; and aux-B is the open concentration obligation itself. No missing historical source is used by the current rung.

**Clarification (2026-09-13, manuscript Proposition 5.20, wedge dichotomy).** For a closed nonproductive SCC `C` on three letters, `span_Q{K2(T) : T in C}` is `Lambda^2 M`-invariant, hence equals `0` or `Lambda^2 Q^3` by irreducibility of `chi_{Lambda^2 M}`. Consequently:

- concentration (`phi_dom != 0` on the carrier) is **equivalent** to `K2 !≡ 0` on `C`, i.e. to the statement *no strict component has first defect degree >= 3* (manuscript Open Problem "Concentration");
- once concentration holds, the "span-rich" step is automatic, with no Galois argument;
- the final step "span-rich => productive" is equivalent to *no strict component has first defect degree 2* (manuscript Open Problem "Wedge productivity").

Both statements remain **OPEN**. Together they are exactly the nonexistence of strict components split by first defect degree, so the spectral route contains no proved implication from wedge data to productivity. The higher-degree sieves constrain the first case without closing it. This does not change the status table above.

**Degree-three partial result (bounded corpus only).** The exact 4,554-member
image-length-at-most-three corpus contains no strict component with `K2=0` and
first nonzero defect `K3`. The canonical Mojo computation checks the
component-level hypotheses and emits any survivor as a replayable countermodel.
This is a finite-domain theorem, recorded in
`docs/p1a-degree3-partial-theorem.md`; it does not promote concentration, G1, or
G1b-2. Its general spectral input is the in-repository first-defect intertwiner,
not the historical seed-specific Galois certificate.

**Degree-two partial result (bounded corpus only).** The same exact corpus
contains no closed nonproductive recurrent component with nonzero `K2`.
The canonical Mojo driver checks the component predicates directly, fails
closed on incomplete automata, and emits any survivor as a replayable exact
countermodel. This is a finite-domain wedge-productivity theorem, not the
general `K2 != 0` implication; see
`docs/p1a-degree2-wedge-productivity.md`.

### Independence from G1b-2

Do not conflate the two gates:

- concentration and wedge productivity are two algebraic/combinatorial problems on a finite closed carrier once it exists, split by first defect degree;
- G1b-2 is the renewal/discreteness theorem needed to prove finite BPA existence.

Neither gate discharges the other.

## Supporting C4 structural program

The large C4 program on `main` remains valid and useful where each individual note marks a result theorem-grade. It is now classified as **supporting Level-3 structure / an alternative coincidence route**, not the headline completion architecture.

Established support includes:

1. **Sink-SCC reduction.** Under finite BPA, any nonproductive state set contains a closed recurrent noncoincident sink SCC.
2. **Endpoint quotient.** The 27 endpoint maps have seven types A–G; eventual endpoint synchronization is a quotient permutation.
3. **Global A/B eliminator.** A globally synchronizing prefix or suffix endpoint map makes every balanced pair productive.
4. **Barge-Diamond G eliminator.** A strict PIP component cannot have endpoint type G. A fixed eventually-coincident pair gives the two-edge hub-star normal form.
5. **Hub/signing bridge.** Child orientation is a `Z/2` cocycle; after the hub gauge it has a concrete boundary-side interpretation. The first-child hub phase and system-level good-edge compatibility are finite necessary conditions.
6. **Parikh intertwiner.** On a finite closed strict component, `P_C N_C = M_sigma P_C`; in the irreducible cubic regime `rank P_C=3` and `rho(N_C)=beta`.
7. **Signed defect intertwiners.** `Q2 S=(Lambda^2 M)Q2`; with `K2=0`, `Q3 S=Phi3 Q3`; normalized SCC transfer is signed, not unsigned.
8. **Higher-degree spectral sieve.** Degree 3 centralizer restriction, degree-4 free-Lie floor, and generalized-Witt/mod-3 near-balanced candidates.
9. **Degree-2 ordered factorization.** Mid-area and integral lattice/Sylvester constraints retain child order; three-state filters are calibration only.
10. **Uniform return/alignment support.** Bounded-gap zero returns, finite Pisot ancestry states, legal ancestry towers, derived recognizability, birth-event catalogues, and relative hierarchy-offset states.

These do not replace G1b-2 or concentration.

## C2/C3/C4 sufficiency chain

For the boundary-synchronization route, the one-way chain remains

```text
C4 => C3-local => C2 => C1.
```

No converse is claimed, and synchronization of every recurrent SCC is not required. This chain is retained as a supporting route, not promoted over the two-gate completion architecture.

## Overlap route (G1-free form of Level 3, 2026-09-13)

**Theorem (repository-proved).** The seed-patch overlap graph `O_sigma` of the swap pairs is finite for every primitive Pisot-spectrum substitution, with an explicit bound from bounded discrepancy (manuscript Theorem 4.22; `docs/overlap-finiteness-and-coincidence-density-2026-09-13.md`). Productivity of every vertex of `O_sigma` is equivalent to coincidence density one for every seed and implies productivity of every reachable state of `B_sigma` with no finiteness hypothesis (Theorem 5.32); under G1 it is equivalent to SCC Producer.

**Density bridge (imported, 2026-09-14).** Barge–Štimac–Williams Theorem 3.1 (with the argument of their Theorem 3.2) gives PDS from a dense set of eventually coincident points of the periodic swap patch and its translate, for any primitive Pisot substitution and any letters; with Lemma 5.36 (three forms of the density condition) this is manuscript Imported Theorem 5.37 and Theorem 5.38 (main theorem without finiteness): productivity of the overlaps reachable from one swap seed implies PDS, with no finiteness hypothesis. G1 is no longer a hypothesis of the sufficiency route; its own status is unchanged (open).

**Endpoint-aligned case (2026-09-14).** The offset-zero and right-aligned overlaps are seed overlaps and are productive iff the letter pair is eventually coincident (prefix / suffix), so Open Problem 5.35 contains the two-sided strong coincidence condition of Arnoux–Ito (manuscript Proposition 5.39). An overlap has a common sub-tile left endpoint at level `m` iff `M^m w` is a difference of proper-prefix Parikh vectors iff it has an offset-zero descendant (Proposition 5.40); under strong coincidence every BPA state is productive, Open Problem 5.35 is this hitting statement for every vertex, and closed nonproductive sets never have boundary coincidences (Corollary 5.41). Exact corpus census: maximum first left-aligned depth 17, maximum strong-coincidence depth 15 (both forms), every specimen satisfies two-sided strong coincidence. **Contracting lower bound (2026-09-15, Proposition 5.42):** a hit at level `m` forces `|varsigma(t)| <= C_varsigma sum_{s<=m} |varsigma(beta)|^{-s}` for every contracting embedding; on the corpus this bound is at most 7 while the depth reaches 17 (excess up to 14), so the hitting level is dominated by a scale-free combinatorial part, not by the contracting size of the offset.

**Open.** Overlap productivity itself (Open Problem 5.35). Nothing here proves it, G1, or PSC. Exact census over the 4,554 corpus: all overlap graphs finite (largest 2,640 vertices), all 1,118,850 vertices productive; finite evidence only.

## Realization / MEF route

Under a finiteness hypothesis, the project uses the realization normal form

```text
coincidence rank > 1
<=> distinct non-eventually-coincident tilings in one MEF fibre
<=> a recurrent producer-free BPA component is globally realized.
```

This is a useful reformulation/certificate framework, not an independent proof of PSC. “Globally realized” is load-bearing, and formal BPA recurrence does not imply realization.

Finite collar death experiments are evidence only until an independent finite collar-completeness theorem is proved.

## Unique decodability and hypothesis firewall

The final theorem must preserve these restrictions.

- **UD is derived, not assumed.** `det M_sigma != 0` yields the established unique-decodability theorem, and the power case follows from `det M_{sigma^r} != 0`.
- **Tile-length independence is derived.** Do not assume separate rational/integer independence when irreducibility supplies it through cyclic-vector structure.
- **FI/boundary injectivity is extra.** It may be used experimentally but cannot enter the general theorem silently.
- **No unimodularity leak.** A contracting/Rauzy argument must handle the non-unimodular internal-space structure rather than silently reduce to the unit case.
- **No false lattice assumption.** `pi_s(Z^A)` is generally dense.
- **No realization shortcut.** A formal SCC/cycle is not automatically globally realized.
- **No computational self-certification.** A finite collar radius or corpus is theorem-grade only after an independent completeness bound.

## Retired Level-2 routes

Do not reattempt these without genuinely new input:

- UD implies bounded total padding;
- bounded discrepancy implies BPA finiteness;
- naive contraction of the zero-sum hyperplane;
- every long state contains a uniformly short core;
- the two-letter renewal argument is trivial;
- an unlabelled cumulative difference walk determines the balanced state.

## Mandatory P0 manuscript/source corrections

Before the next manuscript is treated as authoritative:

1. **Aperiodicity:** remove any claim that primitivity on `|A|>=2` alone implies aperiodicity. Derive it from the full standing hypotheses or state it separately.
2. **Mosse recognizability:** attribute it to primitive + aperiodic substitution structure, not to Pisot itself.
3. **Two-letter literature:** distinguish Barge-Diamond strong coincidence in the two-letter case from Sirvent-Solomyak pure discrete spectrum / BPA-overlap results; cite Hollander-Solomyak only for the exact bridge used.
4. **Closed vs closed-nonproductive:** mass-balance statements needing nonproductivity must say so.
5. **Span-rich claims:** anything using dominant-eigenspace concentration stays conditional until aux-B is proved.
6. **Status synchronization:** preserve the missing-v16 fact as historical metadata while citing the reconstructed G1b-1 and carrier-span proofs on `main`; do not relabel concentration or the realization bridge as source-pending.

Status 2026-09-13: items 1–5 are implemented in the merged manuscript `manuscripts/PSC_balanced_pair_state_2026-09-13.tex`. Item 6 is resolved claim by claim by PRs #68 and #69 and summarized in `docs/claim-status-and-source-map-2026-09-13.md`; ongoing work is ordinary synchronization, not historical source recovery.

## Priorities

- **P0:** keep manuscript claims, source map, prose/TLA ledgers, and references synchronized; archive any recovered historical source without automatic theorem promotion.
- **P1-A:** the two Level-3 closed-carrier obligations: concentration / aux-B (no strict component with `K2 == 0`) and wedge productivity (no strict component with `K2 != 0`). Proving one does not close Level 3.
- **P1-B:** G1b-2 renewal finiteness.
- **P2:** non-unimodular contracting-address design constraint.
- **P3:** final SCC Producer assembly once G1, concentration, and wedge productivity are all available.
- **P4:** realization/collar completeness as parallel certification.
- **P5:** final pure-discrete-spectrum bridge audit.
- **P6:** certificate-producing Mojo experiments without promoting finite evidence to universal theorem.

The shortest honest path to completion is now: close **both Level-3 obligations** (concentration and wedge productivity, i.e. no strict component of any first defect degree), close **G1b-2**, then assemble the finite-graph coincidence argument and audit the final spectral/PDS bridge.
