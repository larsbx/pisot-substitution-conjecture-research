# PSC audit-priority attainment register — 2026-10-16

**Scope:** the three directly related audit/salvage contributions from the current box-walk/SCC thread, merged as [PR #253](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/253), [PR #254](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/254), and [PR #269](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/269). This is **not** a claim to inventory every historical `audit*` or literature-gate document in the repository. It is a dated attainment checkpoint with source links, rather than a new mathematical claim.

**Evidence snapshot:** `main@ca646f28f8ba98e3e6b1e37cd29308bb4888dd3b` (includes merged PR #270). Compare future updates with current `main`, not with the dated checkpoint. Status authority remains `claim_governance.toml`, `docs/proof-ladder.md`, the manuscript and exact proof receipts.

## How attainment is recorded

**Separate the mathematical goal from prerequisite/tool progress.** "Merged audit", "negative control", "finite-depth witness", "conditional proof", and "unconditional general theorem" are different outcomes. In this register, the *degree obtained* is a **scope label**, not a numerical probability or percentage:

- **DEFINED:** statement and necessary interfaces precisely articulated, with no completed certificate for the named priority.
- **FINITE PARTIAL:** exact, replayable supporting tests or witnesses in an explicitly bounded domain (or an adjacent finite diagnostic), but not the stated complete priority.
- **CONDITIONAL / RESTRICTED:** a theorem only under an unproved premise or on a strictly narrower class, with the restrictions explicitly named.
- **OBTAINED:** the exact audit priority is established with a proof/certificate meeting its stated quantifiers and without a hidden budget or conditional premise.

"Degree obtained" below applies to the **priority itself**, not to the status of a separate supporting lemma. No universal priority in this register is marked obtained.

## Audit-by-audit priority and attainment

| Audit (merged PR) | Stated next mathematical priority | Degree obtained **for that priority** | Obtained components / evidence | What remains missing |
| --- | --- | --- | --- | --- |
| **#253 — [box-walk/extremal audit](audit-2026-10-11-boxwalk-extremal.md)** | **Certify `R*(3,4)` and characterize its extremizers**; matrix-first enumeration, complete realization/order search, exact radius observable and certified stopping/closure. | **DEFINED — NOT OBTAINED.** | Exact Mojo+Python **single-substitution, aligned-prefix** replay through depth 9 for `sigma=(001,22,220)`: depth-8 radius 8, depth-9 radius 10 at cut 9054 with defect `(5,5,-10)`. `kernel/psc/boxwalk_radius_probe.mojo`, `evidence/boxwalk-radius8-depth9.json`. The historical constrained-family “max 8” was withdrawn. | No exhaustive `n=3,L=4` search, no validated layered-extremizer reduction, no `R*(3,4)` result or closure/saturation proof. A finite-depth plateau is not a stopping theorem. The witness has **complex** secondary conjugates and measures an aligned-cut radius, not necessarily the earlier staircase/comp statistic. |
| **#254 — [K2 load-bearing SCC salvage](k2-load-bearing-scc-salvage-2026-10-11.md)** | **Prove finite reachable balanced-pair closure** from a dominant length-two `K2` source, **or** a bounded-`K2` substitute; alternatively prove a valid truncation/limiting version of path-counting without finite closure. | **DEFINED — NOT OBTAINED.** | A recorded **conditional** load-bearing result: *if* reachable balanced-pair closure is finite, then some recurrent SCC has transition spectral radius at least `beta * |beta_2|`; the local `K2` additivity and orientation/multiplicity accounting are reusable. Original predecessor-contraction inference was retired. | No unconditional finite closure from the source, no proved bounded-`K2` replacement, and no truncation/limiting theorem replacing finiteness. The conditional spectral conclusion is **not** a proof of the missing hypothesis, SCC Producer, G1, or PSC. |
| **#269 — [matched-origin/path-lifting audit](boxwalk-reachability-realizability-audit-2026-10-15.md)** | **Establish an occurrence-aware matched-target finite reachability certificate**, with exact target `Delta(q)=0 && U[q]==V[q]`, composable occurrence-address paths, proven graph closure, seed/state quantifier coverage and fail-closed budgets; canonical Mojo preferred. | **FINITE PARTIAL — NOT OBTAINED.** | The local matched-letter zero-return condition and its distinction from ordinary `Delta=0` are elementary and established; `12|21` is a negative control. **Pre-existing** `kernel/psc/target_packets.mojo` + `kernel/target_aware_bpa.mojo`, documented in `docs/target-aware-bpa-diagnostic-2026-10-02.md`, already provide actual BPA occurrence addresses, explicit target classification, path replay and fail-closed bounded diagnostics **on specified completed BPA specimens**. Merged [PR #270](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/270) later gave a **uniform one-vertex, two-parameter family** of genuine resolving child paths. | The old `box_walk_recurrence.py` BFS targets the zero *vector*, not matched letters, and splices projected contexts; its "zero stuck nodes" is no certificate. No proof that a collapsed imbalance-only graph has a sound **path-lifting** property, complete successor closure, or the required **all-state/all-overlap** productivity. Existing `target_packets` is an adjacent, stronger occurrence-aware **finite diagnostic**, not a proof of general A2, #84, #138 or #139. PR #270 does not cover all vertices of its family. |

### Reading the #269 progress correctly

The October 15 audit's proposed **future box-walk instrument** was not implemented by #269 (docs-only); however, do **not** classify the occurrence-address, replay, and matched-target subproblems as having no implementation anywhere. They were already partly supplied by the October 2 target-aware BPA packet diagnostic, whose **own report** explicitly distinguishes existential successful paths from avoidance cycles and incomplete lineage coverage.

The open task is a **proof-grade transfer** from such finite realized receipts to the audit's full target/closure/quantifier obligation, or a new exact occurrence-aware box-walk carrier with a sound lifting theorem. Avoid duplicating pre-existing target-packet machinery without a specific missing interface.

## Cross-check against the canonical completion programme (not a fourth audited priority)

- [Issue #84](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/84), **seedwise overlap productivity**, is still **OPEN** and the only outstanding mathematical premise of the shortest G1-free PDS route in `docs/proof-ladder.md`. Its two named stronger branches [#138](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/138) (aligned) and [#139](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/139) (strict zipper) remain **OPEN**.
- A **genuine obtained restricted result** is the repository's finite-domain productivity/PDS certification for the enumerated corpus subsets (e.g. Theorem Ω on 145,806 specimens as recorded in `docs/proof-ladder.md`), along with proofs on named infinite subfamilies. Those do **not** meet #84's universally quantified target.
- [PR #270](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/270) is a further exact **one-vertex** all-parameter good-exit theorem for `sigma(a)=a^k b c^h, sigma(b)=ab, sigma(c)=a`, `k>=3`, `2<=h<=k`. It explicitly does **not** prove resolving children for every vertex in a hypothetical closed nonproductive SCC.

## Ordered next checks

1. **Highest-leverage primary route:** build on the already proved finite seed-patch overlap carrier to discharge #84 (or #138/#139) with a theorem excluding **child-closed nonproductive** realized recurrent components. A selected escape path from a productive component is insufficient.
2. **#269 direct prerequisite:** specify the exact target and quantifiers, then run or extend *existing* occurrence-aware target-packet Mojo with a replayable, composable witness; prove any proposed projection's lifting and its finite successor closure. A test for `12|21` must refuse "terminal zero = coincidence." Promote neither an unclosed depth plateau nor a vector-only BFS.
3. **#253 bounded extremal research:** define the radius statistic (aligned-prefix vs realized staircase/comp); enumerate incidence matrices and *all* required word orders for `(n,L)=(3,4)`, with complete counters and explicit budget refusals. Layered ordering is a search heuristic until a rearrangement theorem justifies reduction. Prove a stopping/closure criterion before asserting `R*(3,4)`. If infinite-depth finiteness has not been established, formulate `R*` as a supremum that could a priori be infinite.
4. **#254 bounded K2 route:** either prove finite reachable `K2` closure/boundedness, or replace Step 6 of the conditional path-count argument by a rigorously controlled truncation. Until then retain its spectral SCC conclusion as conditional.

**Next update protocol:** for each row record the new main commit/PR, exact scope of the mathematical claim, a replayable witness or proof source, completed/uncompleted budgets and whether it upgrades *the stated priority* rather than only a prerequisite. A merged audit is not itself an attainment upgrade.

## What is not claimed

No new PSC, G1, SCC Producer, universal radius ceiling, general A2, or #84/#138/#139 closure follows. This file is a source-indexed status register, not a claim ledger or a theorem certificate. No generated claim-governance or TLA surfaces are modified.
