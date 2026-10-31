# Pisot Substitution Conjecture: a research and evidence map

> **Status: OPEN.** This repository investigates the Pisot Substitution Conjecture (PSC) for primitive, irreducible Pisot substitutions, including non-unimodular cases. It contains proved reductions, imported theorems, exact finite-domain certificates, results for infinite families, and unfinished universal arguments. **No general proof of PSC is claimed.**
>
> **For coding and research agents:** use [README.llm.txt](README.llm.txt), then [AGENTS.md](AGENTS.md). The human and agent guides describe the same mathematical status from different perspectives; neither overrides the governed claim ledger.

## 1. The question and why overlaps matter

A substitution replaces each letter of a finite alphabet by a nonempty word. Repeated substitution creates structured symbolic and tiling systems. The Pisot condition constrains the eigenvalues of the substitution's incidence matrix: its Perron eigenvalue is greater than one, while its other algebraic conjugates have modulus less than one. The conjecture asks whether the associated dynamical system has **pure discrete spectrum (PDS)** under the standing primitive, irreducible Pisot hypotheses.

The project's strategy is to turn that spectral question into a question about **overlaps** of substituted tiles. An overlap is *productive* if some sequence of genuine substitution-child occurrences reaches a coincidence: matching tile types at zero displacement. An overlap path must remember which **actual occurrences** of letters were selected, not merely the resulting coordinate vector.

Two ideas organize the project:

- **Reachability:** show that all overlaps relevant to a suitable swap seed eventually *can* reach coincidence. This is an existential descendant property, not a requirement that every infinite sequence of choices terminates.
- **Obstruction:** if productivity fails, a finite child-closed nonproductive configuration must survive. The program reduces that configuration to an aligned branch or a cyclic strict-zipper branch.

For the intended theorem, "primitive irreducible Pisot" is not shorthand for "unimodular"; the determinant need not be ±1. Precise assumptions and prohibited shortcuts appear under [Generality and proof discipline](#6-generality-and-proof-discipline).

## 2. The shortest route to the conjecture

The strongest organizing fact is a proved-and-imported implication chain with **one outstanding productivity premise**:

```text
Primitive irreducible Pisot substitution
    |
    v
Bounded discrepancy                               REPOSITORY-PROVED
    |
    v
Finite exact seed-patch overlap graph             REPOSITORY-PROVED
    |
    v
A suitable swap seed has only productive
reachable overlaps                                OPEN (#84)
    |
    v
Coincidence density one / dense good set          REPOSITORY-PROVED
    |
    v
Pure discrete spectrum                            IMPORTED theorem
```

Here a *swap seed* is one of the finite initial overlap configurations used by the repository's seed theorem. The sufficiency route needs **one suitable seed per substitution**, not a proof for every possible overlap state. The stronger every-state formulation is useful in its own right but should not be quietly substituted for the smaller target.

The [two-obstruction completion theorem](docs/direct-attack-frontier-2026-10-23.md) gives a more concrete sufficient way to discharge the open step:

| Open obligation | Meaning | Why it matters |
| --- | --- | --- |
| **A1′ — aligned obstruction** ([#138](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/138)) | The residual first-letter-fixed hub pair eventually coincides, in the required **one-sided** formulation. | Removes the aligned obstruction. |
| **BH — boundary hitting** ([#139](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/139)) | Every relevant cyclic, seed-reachable, strict-zipper overlap has an **actual occurrence-indexed** descendant of offset zero. | Removes the strict-zipper obstruction; a zero-offset hit need not itself have matching letters. |

Their universal completion gives the missing productivity step ([#84](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/84)) and hence PDS through the preceding chain. **Neither universal A1′ nor universal BH is established.** A result for a family of substitutions cannot close these quantifiers without a proof that the families exhaust the standing regime.

The distinction between PDS and finite balanced-pair automata also matters. The repository proves the **implications** PDS ⇒ G1 and PDS ⇒ every-seed termination with coincidence, but universal G1 is not known without its premise. G1 is a stronger structural route, not a prerequisite for the shortest sufficiency chain. See [G1/PDS status](docs/g1-pds-necessity-status-2026-10-23.md) and the [proof ladder](docs/proof-ladder.md).

## 3. Evidence, ranked by its relevance to PSC

Evidence is ranked here by **logical role**, not by when it was produced or by the volume of computation.

### A. The load-bearing general results

The foundations closest to a general proof are the repository-proved bounded-discrepancy theorem, finite seed-overlap graph, obstruction normal form, and coincidence-density implication, together with the audited imported density-to-PDS theorem. These justify the reduction in `2. The [onboarding/source firewall](docs/project-onboarding-2026-10-23.md), [claim/source map](docs/claim-status-and-source-map-2026-09-13.md), [proof ladder](docs/proof-ladder.md) and [state-of-program manuscript](manuscripts/PSC_balanced_pair_state_2026-09-13.tex) identify their hypotheses and evidence.

The obstruction normal form uses the exact child relation

```text
new_offset = incidence_matrix * old_offset
             + Parikh(bottom proper prefix)
             - Parikh(top proper prefix)
```

together with true letter types and strict overlap geometry. A cycle of abstract affine labels alone is **not** a symbolic coincidence certificate.

### B. Universal statements proved only in structured families

These results settle infinite subclasses and provide candidate mechanisms for the still-open universal A1′/BH steps.

- **Class D:** boundary hitting is recorded for the entire PIP determinant-two class-D normal form, with scoped finite-BPA consequences. See [class-D assembly](docs/class-d-assembly-audit-2026-10-21.md) and [G1 corollary](docs/class-d-g1-corollary-2026-10-22.md).
- **Aligned A1′ and other determinant-two families:** the catch-up-free classification proves large sectors; a residual non-crossing part of Theorem K's family F remains an explicit open frontier. See the [direct attack map](docs/direct-attack-frontier-2026-10-23.md).
- **Classes A, B and C:** exact boundary-hitting certificates cover many lines, wedges and parameter regions. Remaining A/C regimes and the class-B top layer cannot be declared closed by accumulating more bounded tables. The program needs a genuinely uniform covering argument. The [run-index analysis](docs/p1b-class-a-run-index-2026-10-21.md) also rules out a parameter-independent class-A hitting-depth bound.

**A particularly useful local frontier:** in the minus class-A normal form (`4), complete stars, real two-cycles, selected coincidence exits and some *every-first-choice* exits can be checked symbolically. They make the obstruction graph more explicit, but still do **not** certify every relevant cyclic strict-zipper state.

### C. Exact finite-domain theorems

[Theorem Ω's audit](docs/audit-theorem-omega-2026-10-08.md) records a complete box-automaton PDS certificate on **145,806** ternary PIP substitutions in the declared bounded union (images of length at most four, or total image length at most eight). Its conclusion on that **finite domain** uses the exact overlap/Meyer and flow-to-symbolic imports.

Finite-domain theorems settle every specimen in their *specified* finite sets. They cannot be extrapolated to arbitrary substitution lengths without an additional completeness theorem.

### D. Independent experimental checks and negative controls

The standing **4,554-member** short-image corpus has exact seed-patch overlap graphs for all specimens; the recorded census reports **no nonproductive overlap** in that corpus, with largest graph 2,640 vertices and maximum first-coincidence depth 18. A broader total-length-≤10 census records the two-sided strong-coincidence test on **408,798** specimens. These observations support conjecture formation and regression, **not** universal assertions.

Negative results constrain proof design. Exact productive cycles rule out arguments requiring a rank that decreases on every edge. Affine-state equality does not guarantee occurrence-compatible symbolic pumping. Finite-radius separation, rank deficiency, and magnitude-only contraction arguments have documented counterexamples or insufficiencies. Consult the [retired-route audit](docs/direct-attack-frontier-2026-10-23.md) and [side-notes ledger](docs/side-notes-ledger.md) before reopening such approaches.

## 4. A worked example: what the class-A progress actually proves

In one **minus class-A** family, with integers `k,t ≥ 0`,

```text
n = k + t + 3
d = 2n - 1 - k
A = n + d
x -> x y^A x
c -> c y^n x
y -> x y^(n-1) c
```

An oriented overlap is written `(top_letter, bottom_letter, Δx, Δc, Δy)`. The last three entries are **bottom-minus-top Parikh offsets**. Reversal swaps the two letters and negates all three offsets. Old nicknames such as T, Q or V are never a safe substitute for the complete five-tuple.

The following snapshots illustrate increasing proof strength:

| Source and result | What is established at its exact scope | Mainline status at this documentation revision |
| --- | --- | --- |
| Canonical P3 family, T/X/Y0 | Exact complete-star packets and typed exits; the P3 and T/X/Y0 **outgoing images** have 37 and 42 oriented labels, with a 59-label union | [#372](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/372), [#412](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/412), [#413](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/413): merged |
| `Y0=(y,y,1,-1,-1)` | A selected coincidence exit, plus a scoped result giving a selected completion after **every actual first choice** (≤6 total edges) | [#412](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/412), [#419](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/419): merged |
| `CY=(c,y,0,-2,2)` | Exactly `2n+1` indexed children per orientation, six typed child labels, a productive Y0↔CY cycle and one selected coincidence exit | [#414](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/414): merged |
| CY, stronger result | A selected completion after **every actual first choice** (≤7 total edges), with symbolic transport and rational-overlap guards | [#415](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/415): **open**, not on `main` |
| `CC=(c,c,0,-2,3)` | Proposed four-index complete star and selected three-edge exit; the Y0 LAST/LAST edge to this **specific** CC state is strict only for `t=0` | [#416](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/416): **open** |
| CC, stronger result | Proposed selected completion after every first choice (≤5 total edges) | [#417](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/417): **open**, stacked on #416 |
| U short tail | Recovered four-edge seed-to-internal-coincidence witness, including two edges from U | [#411](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/411): **open** |

The [recovered-branch provenance audit](docs/branch-conjugate-audit-2026-10-30.md), [canonical frontier report](docs/class-a-boundary-consolidated-frontier-2026-10-31.md) and [Y0 first-choice derivation](docs/class-a-boundary-y0-every-child-2026-10-31.md) provide details. The 59-label union is **not** a forward-closed carrier; its review queue is not a global count of unresolved overlaps.

A *selected exit* proves there exists a path. *Every-first-choice productivity* allows any genuine first edge, then selects a path. Neither asserts termination under every subsequent arbitrary choice, and neither by itself discharges universal BH. Finite replay checks implementations; it does not replace the algebraic derivation for unbounded `k,t`.

## 5. What remains to finish

In order of proximity to the missing sufficiency step:

1. **Universal BH:** classify or otherwise control the relevant **seed-reachable cyclic strict-zipper** obstruction in the full standing regime. In class-A/C use genuinely parameter-uniform certificates; finish the class-B top layer. Move beyond determinant two without dropping necessary finite-place (M-adic) coordinates.
2. **Universal one-sided A1′:** settle the remaining fixed-hub aligned cases, including the non-crossing family-F residue, then eliminate additional assumptions when passing to the full PIP regime.
3. **Assemble the two-obstruction completion at full scope:** validate actual occurrence transports, strict overlap, seed reachability, child closure and any representation-space dependencies. Only then can #84 be closed and the imported final spectral step applied.

Parallel, stronger investigations include renewal finiteness/G1b-2, finite-BPA SCC productivity, realization/coincidence-rank bridges, and exact finite-interface analogies. They remain useful, but **are not extra premises** of the shortest route. See the [ranked direct research directions](docs/direct-attack-frontier-2026-10-23.md).

## 6. Generality and proof discipline

The standing substitution is primitive, has nonzero determinant and irreducible rational characteristic polynomial, and has a Pisot Perron eigenvalue. **Do not insert** unimodularity, independent tile lengths, unique decodability, one-step injectivity, legal-swap-seed assumptions, a Euclidean-only internal space, or a finite collar bound as independent unproved hypotheses. Unique decodability follows from full incidence rank/defect-theorem reasoning at its proper scope.

Three kinds of claim must remain distinct:

| Label | Appropriate evidence | What it does **not** establish |
| --- | --- | --- |
| **Repository-proved or precisely imported** | Checkable proof with complete hypotheses; imported theorem with verified applicability | Stronger quantifier or unproved premise |
| **Exact family / finite-domain certificate** | Symbolic universal parameter proof, or exhaustive verified finite domain | Coverage outside that family or domain |
| **Finite replay / experimental evidence** | Deterministic oracle, corpus, hashes, CI receipts and negative controls | A universally quantified mathematical statement |

**Project-accepted for progression** may precede independent human review; this is not a claim that the review took place. Read [claim_governance.toml](claim_governance.toml) and [review/source notes](docs/project-onboarding-2026-10-23.md). Open PRs, queued CI, and proposals are not accepted theorem-bearing changes to `main`.

## 7. Reproduce results and navigate the repository

**Implementation policy:** [Mojo](kernel/) is the canonical executable research language; [Python oracles](oracles/) are independent differential checks and prototypes, not replacements for a missing canonical kernel. [Lean](proof/PscVerif/) and [TLA+](proof/tla/) record explicitly scoped formal obligations. Exact integers/rationals are preferred to floating-point acceptance arguments. See [AGENTS.md](AGENTS.md) for requirements, vendors, evidence receipts and review policy.

```bash
# Root: run the orchestrated verification, reporting absent tools as skipped.
./tools/verify_all.sh

# Canonical Mojo workspace.
cd kernel
pixi run test
pixi run verify
```

A skipped toolchain is **not** a passed proof. The generated [proof bank](docs/proof-bank.md), [claim map](docs/claim-status-and-source-map-2026-09-13.md) and [proof ladder](docs/proof-ladder.md) are the most useful starting points for evaluating a particular theorem.

| If you want to… | Start here |
| --- | --- |
| Understand the main theorem and live gaps | [Proof ladder](docs/proof-ladder.md), [direct attack map](docs/direct-attack-frontier-2026-10-23.md) |
| Audit a specific theorem's status | [Claim governance](claim_governance.toml), [proof bank](docs/proof-bank.md), [source map](docs/claim-status-and-source-map-2026-09-13.md) |
| Implement or review exact code | [Agent implementation policy](AGENTS.md), [Mojo kernel](kernel/), [independent oracles](oracles/) |
| Inspect the class-A graph frontier | [Canonical frontier](docs/class-a-boundary-consolidated-frontier-2026-10-31.md), [Y0 packet](docs/class-a-boundary-y0-every-child-2026-10-31.md) |
| Follow the **history** of the research | [Completion ledger](docs/completion-ledger-2026-10-26.md), [side-notes journal](docs/side-notes-ledger.md), [branch recovery audit](docs/branch-conjugate-audit-2026-10-30.md), PR history and [archive](archive/) |
| Explore non-load-bearing benchmarks | [Plastic-A/Padovan](docs/post-proof-padovan-plastic-a-conjectures-2026-09-23.md), [Penrose interface](docs/bridges/penrose-2d-to-psc-interface-program.md) |

**This README is a conceptual map, not the governed source of mathematical status.** It is intentionally organized by proof dependency and evidentiary force. Dated changes, superseded attempts and experimental chronology belong in the journals and archives linked above.
