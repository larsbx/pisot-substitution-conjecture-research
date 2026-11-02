# PSC completion ledger — 2026-11-02

**Status:** dated evidence reconciliation; not a new mathematical proof.
**Baseline consulted:** `main@f76df185c25542f721d6041826cafdb9a0d3bed1`
(merge [#448](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/448);
parent `9ecc5f8de3411054256d4358795b126c5468be8b`, merge #447).
**Prior brief:** [2026-10-26 ledger](completion-ledger-2026-10-26.md),
baseline `4eb0427d440e4c2cfe28ce7de934061f1c9bf3ad`.
**Interpretation:** all scopes are repository-recorded/accepted, not
independently human reviewed unless specifically documented. The current
editorial change adds no executable checks and promotes no governed claim.

## Executive result

The general Pisot Substitution Conjecture is **OPEN**. The conditional
two-obstruction completion theorem remains the shortest route:

```text
primitive irreducible Pisot (ternary)
  + one-sided residual fixed-hub-pair eventual coincidence A1′   [OPEN #138]
  + cyclic seed-reachable strict-zipper occurrence hitting BH     [OPEN #139]
  => seedwise overlap productivity                               [conditional #84]
  => coincidence density one and PDS                              [proved/imported bridge]
```

The route does not assume G1, global unimodularity, independent tile lengths,
seed legality or an extra UD axiom. Full incidence rank derives UD for images
and powers. Bounded discrepancy G1b-1 and seed-patch overlap finiteness are
proved; renewal finiteness G1b-2 and general finite BPA/G1 remain **OPEN**.
The invalid predecessor-contraction shortcut is not reactivated.

## Issue #9: closure and next C4 proof contract

[Issue #9](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/9)
is administratively closed; its final status note explains that closure
concluded the research-routing track, **not C4**. The one-way
[candidate good-edge test](c4-good-edge-system-bridge.md) proves that a
genuine Barge–Diamond good pair survives the endpoint+first-child mask
for any **supplied** finite strict child-closed PIP derived system. If exactly one bit survives **under the supplied strict PIP hypotheses**,
then the Barge–Diamond existence theorem identifies that bit with an
actually eventually-coincident edge. A bit surviving in isolation, or in
a non-Pisot calibration, is not a certificate of eventual coincidence,
and no such mask supplies C4's interior synchronization step.

The target-aware [packet diagnostic](target-aware-bpa-diagnostic-2026-10-02.md)
records literal occurrence/address, residual Parikh, orientation,
interior/boundary flag and incoming ordered factor edge. Its PIP fixture
`1/02/202` retains 507 packets / 948 edges, four avoiding recurrent
packet SCCs with exits, and source SCCs with successful target paths.
The non-Pisot strict `1/012/1` and actual G/F `1/2/021` are preserved
controls, with 46/82 and 153/235 packets/edges respectively. These are
bounded *historically reported* exact replays, not a general C4 theorem.

The precise next attempted step, without duplicating the prior first-child
or prefix-difference work, is now specified in
[c4-ordered-word-completion-interface-2026-11-02.md](c4-ordered-word-completion-interface-2026-11-02.md).
It keeps actual ordered interior-child hub residuals, inherited legal
contexts and the distinction between immediate target diagonal and
eventual `Sync_±` explicit. The packet `209 -> 429 -> 209` regression
rejects arbitrary physical-offset monotonicity. Packet recurrence
and finite-source strict SCC extraction must not be conflated.

## Recorded scope increments since 2026-10-26

| Track | Project-recorded advance | Still required |
| --- | --- | --- |
| Class A BH | Existing all-gap `d<=4` and `d>=5,n>=5d`; [#438](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/438) derives a **scoped** minus-line Parikh-field injectivity interface; [#440](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/440) records all-parameter local RUN shear paths, not all-source closure; [#447](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/447) certifies finite full outgoing/distance records on 22 named specimens | Parameter-uniform all-descendant X/carrier closure and a separate realized-overlap/non-unit transfer; [#442](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/442) |
| Class B BH | [#367](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/367) 529-row exact middle `l>=4` certificate: plus `g>=16, 2<=r<=g-14`, minus `g>=12, 6<=r<=g-6` with separately handled `g=12,r=6`; 186 certified finite-gap rays (plus through gap 15, minus through 11) | Low/high residue strips and unbounded-gap `l<4`; actual boundary escapes prevent extension of the middle table |
| Class C BH | [#384](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/384), [#399](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/399), [#394](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/394) cover `d>=6,n>=3d` in both signs and additionally plus `2n>=5d+8` / minus `2n>=5d+16` below slope three; existing `d<=5` remains | Remaining lower cone below those bounds |
| Class D | Accepted every PIP member in Theorem E's Class D, with scoped G1 corollary; unchanged | No reopening of resolved class-D certification |
| Finite Class-A quotient | [#448](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/448) proves **conditional** Lean path-lifting and shortest-distance preservation when edge projection, lift from *every* original source and terminal equivalence are supplied | Separate native/Lean refinement and proof that actual canonical Mojo graph meets all refinement premises, plus parameter-uniform coverage |

All these extensions are family-conditional or bounded-computational as stated.
No finite census or local seed path is promoted into universal BH or PSC.

## Implementation/verification boundary

- [#447](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/447)
  merged at `9ecc5f8de3411054256d4358795b126c5468be8b`.
  [Dedicated exact-head acceptance](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/41448531108)
  passed for head `4ec572a60993a0e0d1d9f97ab64257fa61ee209f`;
  its report has 22 finite specimens with literal source/edge completeness
  and shortest terminal distance witnesses. Full universal coverage is not checked.
- [#448](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/448)
  merged at the baseline head. Its receipt-only head is
  `4b5ccec83c6f0e0fc89828f5421fc9b2a4ef651f`.
  The PR reports local pinned Lean compilation and axiom audit
  (68 inventoried named proofs) and 194 focused tests; the visible
  *pull-request-triggered* workflow list for that exact head includes
  successful target-aware BPA, PSC research checks, Class-A indexed
  productivity, Class-A children, canonical Pisot kernels, and the
  C4 named workflows. Those hosted results do not prove
  native-to-Lean refinement or the unbounded theorem.
- Source files/receipts: [finite quotient Lean interface](finite-quotient-distance-lean-2026-11-02.md),
  `proof/PscVerif/PscVerif/QuotientDistance.lean`,
  `evidence/finite-quotient-distance-lean-2026-11-02/`,
  `evidence/class-a-finite-hosted-acceptance-2026-11-02/`.
- This ledger was prepared by reading immutable GitHub sources and workflow
  metadata, **not** by locally replaying Mojo/Lean/CI. Human review remains
  pending final validation, not a research-progress precondition.

## Corrections and attribution firewall

1. Second-letter, depth-one and naïve six-state child maps are rejected
   by literal word factorization/residual position, not by an algebraic
   shortcut. Actual G/F synthetic `1,1,3` factor lengths are `1,2,5`;
   the discovered `2/2` diagonal must survive the negative receipt.
2. A recurring offset/alignment snapshot, constant hub phase or
   productive exit does not prove C4. A finite packet SCC may avoid the
   target while some root has a successful path. Split descendants
   are not part of the target-aware continuation graph.
3. The Barge–Diamond existence result does not prove a chosen edge
   good without the correct hypotheses. Recognizability applies to
   legal hull contexts; all swap seeds need not themselves be legal.
   Algebraic/quotient projection is not word-level realization.
4. No independent tile-length rational-independence assumption, no
   global unimodularity, no predecessor contraction, no unit-only
   geometric import to the non-unit case, and no unproved
   native-to-Lean or G1-to-C4 transfer.
5. The archived SP/UD shortcut is refuted; derived UD via full
   incidence rank remains. The Nakaishi global preprint audit is
   not proof provenance for general PSC.

## Ranked completion register

| Priority | Obligation | State | Discharge evidence |
| --- | --- | --- | --- |
| 1 | Ordered hub-residual word C4 on a **given strict component** | **OPEN unchanged** | Uniform actual ordered word/ancestry `Sync_±` bridge, or counterexample to a precisely proposed intermediate lemma; include occurrence addresses and full child order |
| 2 | Universal BH #139 | **OPEN** | Occurrence-indexed composable offset-zero path for every cyclic seed-reachable strict zipper, including all remaining A/B/C regions and full non-unit realization transfer |
| 3 | One-sided A1′ #138 | **OPEN unchanged** | Eventual coincidence of the residual first-letter-fixed bad hub pair; outstanding noncrossing cells of family F and the rest of ternary PIP |
| 4 | Completion #84 / PDS | **CONDITIONAL** | Discharge both A1′ and BH under exactly the existing assembly hypotheses, or deliver an independent valid route |
| 5 | Class-A X implementation #442 | **PARTIALLY CLOSED finite** | Canonical Mojo complete edge/occurrence checker with valid native-to-formal refinement and parameter-uniform source/descendant carrier; finite #447/#448 are not universal |
| 6 | Class-B / C residual fronts | **OPEN** | Exact actual-occurrence carrier closure/rank certificates in remaining strips/cones |
| 7 | G1b-2 / universal G1 | **OPEN unchanged** | Renewal finiteness/termination or an alternative universal implication; no precursor-contraction shortcut |
| 8 | Audit and final review | **PENDING** | Independent human review of complete theorem/receipts/assumptions; not falsely asserted and not a prerequisite for continued research |

**Governance:** this document reconciles navigation and acceptance scopes only.
No `claim_governance.toml` entry, generated dependency ledger or theorem
state is changed by adding this note.
