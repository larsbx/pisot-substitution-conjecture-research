# Pisot Substitution Conjecture Research

This repository studies the Pisot Substitution Conjecture (PSC), with particular attention to exact overlap calculations and the non-unimodular case. It contains mathematical reductions, proofs for particular families, finite computations, and work toward the remaining general arguments. **The conjecture is still open.**

This page introduces the mathematics and the evidence behind it. Research and coding agents should use [README.llm.txt](README.llm.txt) and [AGENTS.md](AGENTS.md) for implementation and verification conventions.

The [current-state reconciliation of November 11](docs/current-state-reconciliation-2026-11-11.md) records the accepted mainline through #541, exact-revision verification receipts, the older integration queue, and the separate active research PRs. It distinguishes completed implementation work from the mathematical premises that remain open.

## The question

A substitution assigns a nonempty word to each letter of a finite alphabet. Iterating it produces symbolic sequences and, through a geometric realization, tiling dynamical systems. Its incidence matrix counts how often each letter appears in the image of another.

The Pisot condition requires a dominant eigenvalue greater than one whose other algebraic conjugates lie strictly inside the unit circle. The conjecture asks whether a primitive, irreducible Pisot substitution gives rise to a dynamical system with *pure discrete spectrum*. Informally, this means the spectral behavior is accounted for by eigenfunctions rather than a continuous spectral component.

The repository does not assume that the incidence matrix is unimodular. Its determinant may have absolute value greater than one. That distinction matters: a proof based only on Euclidean contracting coordinates may lose the finite-place information needed in the non-unit case.

The main method studies overlaps between substituted tiles. An overlap is called *productive* when a sequence of genuine substitution-child occurrences leads to a coincidence: equal tile types at zero displacement. An overlap is described not only by its displacement but also by the particular letters and occurrences that produce its descendants.

## The programme in the literature

The **two-letter** Pisot conjecture is proved. For three or more letters, the general problem—including the unimodular case—remains open, even though special families such as Arnoux–Rauzy systems and Pisot β-substitutions are settled. A Rauzy fractal, a domain exchange, or the existence of many eigenvalues does **not automatically** establish pure discrete spectrum.

The [literature-to-proof crosswalk](docs/motivations/psc-literature-crosswalk-2026-11-04.md) explains the published results, distinguishes **strong coincidence** from **overlap coincidence**, and shows why non-unimodular substitutions need additional care. In particular, Barge–Kwapisz gave geometric criteria, **not** a proof of the whole unimodular conjecture. A claimed 2024 general proof is **not imported** here; see the [Nakaishi source-level audit](docs/nakaishi-2024-first-entry-audit-2026-10-13.md).

The open problems in this project are [one-seed productivity #84](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/84), its [aligned #138](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/138) and [strict-zipper #139](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/139) obstructions, and the separate [ordered-child C4 target #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461). Finite-domain certificates and infinite-family theorems are real progress, not a proof for every substitution.

## The route to a proof

Several of the main implications are already available. The unresolved step is to show productivity of the overlaps reachable from a suitable initial swap seed:

```text
Primitive, irreducible Pisot substitution
    => bounded discrepancy                                     [PROVED]
    => finite seed-patch overlap graph                         [PROVED]
    => one swap seed has only productive reachable overlaps    [OPEN: issue #84]
    => coincidence density one / dense good set                [PROVED]
    => pure discrete spectrum                                 [IMPORTED theorem]
```

The final step uses a published density-to-spectrum theorem whose hypotheses have been checked for this setting. The [proof ladder](docs/proof-ladder.md) and [state-of-program manuscript](manuscripts/PSC_balanced_pair_state_2026-09-13.tex) give the precise statements.

The seed theorem requires one suitable seed for each substitution. Proving that every possible overlap is productive would be stronger, but is not necessary for this route.

### Two remaining obstructions

For ternary primitive irreducible Pisot substitutions, the repository's two-obstruction completion theorem reduces the productivity step to two questions.

**Aligned overlaps (A1′, [issue #138](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/138)).** The residual first-letter-fixed pair must eventually coincide. The theorem needs this statement in one direction; the stronger two-sided version is not an additional assumption.

**Strict-zipper overlaps (BH, [issue #139](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/139)).** Every relevant cyclic, seed-reachable strict-zipper overlap must have a descendant at zero displacement, obtained through an actual sequence of letter occurrences. For BH, the descendant need not yet be an equal-letter coincidence.

Together, these results would establish the missing seed productivity premise, [issue #84](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/84), and complete the route to pure discrete spectrum. Both universal assertions remain unproved. The [direct-attack analysis](docs/direct-attack-frontier-2026-10-23.md) explains their present formulations and the work still required.

There is also a useful distinction involving balanced-pair automata. The repository proves that pure discrete spectrum implies their finiteness (G1), along with termination with coincidence from every swap seed. These are implications, not unconditional proofs of G1. Finiteness and the associated strongly connected component arguments remain valuable parallel approaches; they are not prerequisites for the shorter route above.

## What the evidence establishes

The results are grouped here by how directly they bear on the conjecture, rather than by the order in which they were discovered.

### General results supporting the reduction

Bounded discrepancy and the finite seed-patch overlap construction make the problem finite for each fixed substitution, without assuming balanced-pair finiteness. If productivity were to fail, the obstruction results place strong restrictions on a surviving child-closed set. Those restrictions include full rational rank, inherited spectral information, and a distinction between aligned and strict-zipper configurations.

The arithmetic of a child overlap is exact. With offsets recorded as bottom minus top, its update is

```text
child offset = M × parent offset
             + Parikh(bottom proper prefix)
             − Parikh(top proper prefix)
```

where `M` is the incidence matrix. A coordinate update alone is insufficient: the selected prefixes must occur in the substitution words, and the resulting overlap must be geometrically strict. This is why the repository maintains independent occurrence-level checks alongside symbolic calculations.

The [onboarding notes](docs/project-onboarding-2026-10-23.md), [claim/source map](docs/claim-status-and-source-map-2026-09-13.md) and [proof bank](docs/proof-bank.md) document the supporting arguments and their precise hypotheses.

### Results for infinite families

The most developed boundary-hitting work concerns structured ternary determinant-two families. Class D has a completed boundary-hitting certificate at its stated scope, with corresponding finite balanced-pair consequences. See the [class-D assembly](docs/class-d-assembly-audit-2026-10-21.md) and [corollary](docs/class-d-g1-corollary-2026-10-22.md).

Classes A, B and C have substantial line, wedge and parameter-region results. The outstanding regions call for arguments uniform in the parameters: additional finite tables alone will not settle every gap. The [class-A run-index analysis](docs/p1b-class-a-run-index-2026-10-21.md) shows, in particular, why a parameter-independent bound on hitting depth is unavailable there.

The aligned branch has also been proved for large catch-up-free determinant-two sectors. Some non-crossing cases of Theorem K's family F remain open. Even a complete proof for these determinant-two families would still need to be extended to the full non-unit setting.

### Finite-domain theorems

[Theorem Ω](docs/audit-theorem-omega-2026-10-08.md) gives a complete box-automaton certificate of pure discrete spectrum for **145,806** ternary Pisot substitutions in its stated bounded domains: images of length at most four, or total image length at most eight. Its conclusion depends on the recorded overlap, Meyer-property and flow-to-symbolic imports.

This settles the specified finite domain, not substitutions of unrestricted image length.

### Computations and counterexamples

The standing short-image corpus contains **4,554** ternary primitive irreducible Pisot substitutions. Exact seed-patch overlap graphs were constructed throughout that corpus, with no nonproductive overlap found. The largest graph has 2,640 vertices, and the maximum recorded first-coincidence depth is 18. A separate census tested two-sided strong coincidence on **408,798** specimens of total image length at most ten.

These computations are useful checks on conjectures and implementations. Their sample sizes do not turn them into a general proof.

Negative examples have shaped the work just as much. Productive overlap graphs can contain directed cycles, so a rank cannot decrease strictly along every edge. Two affine states may coincide without supporting the same sequence of literal letter occurrences. The [direct-attack notes](docs/direct-attack-frontier-2026-10-23.md) and [side-notes ledger](docs/side-notes-ledger.md) record these and other unsuccessful approaches.

The [non-unit occupancy certificate](docs/c4-nonunit-residue-occupancy-2026-11-04.md) replaces a scratch observation with exact upper bounds for `0→1, 1→021, 2→001`. Counts in the four classes of `Z³/M²Z³` prove that all three Euclidean occupancies are below one half, while literal strong-coincidence witnesses exclude a fully strict balanced-pair system for this specimen. Low Euclidean occupancy therefore does not by itself diagnose a productivity obstruction. The certificate gives bounds, not exact fractal areas.

The companion [M-adic counting bridge](docs/c4-nonunit-madic-counting-bridge-2026-11-04.md) retains every compatible matrix-residue level. Its written proof extends the regular-window and strict-cut counting arguments to this explicitly constructed internal space, including the missing non-unit measure factor. Independent human review remains pending. A useful remaining target is an upper bound on a represented lifted overlap that contradicts the lower bound forced by strict cut frequency; the bridge alone does not establish general C4 or PSC.

The [bounded cylinder-overlap verifier](docs/c4-finite-cylinder-overlap-verifier-2026-11-04.md) makes the finite upper-bound side executable. It preserves complete occurrence addresses, certifies Euclidean outer rectangles and checks matrix-residue refinements and covolume normalization. For `1/021/001`, the complete depth-two cylinders prove that the lifted subtile for letter `2` is disjoint from those for `0` and `1`. The remaining `0`–`1` pair shares the origin at every even depth; its implemented rectangle bounds stay positive despite its separately witnessed null overlap. Both implemented substitutions are productive controls. No strict Pisot component or positive strict-cut density is supplied, so the verifier reports finite upper bounds and an explicit obstruction to invoking the contradiction criterion.

The [finite-carrier and exact-measure construction](docs/c4-finite-overlap-carrier-2026-11-05.md) gives an a priori finite domain for paired-occurrence overlap graphs: a preserved physical strip combines with a certified stable enclosure to bound every relevant integer offset. The written measure argument yields an exact nonnegative graph equation, so a positive strict subinvariant vector proves null overlap. The canonical Mojo certificate and independent full-row oracle establish all **36** distinct-letter lifted overlaps are null for the **12** sources `11/{012,021,102,120,201,210}/{01,10}`, with incidence polynomial `x³−x²−3x−2`. Through the strict-cut bridge, this excludes every finite fully strict child-closed noncoincident balanced-pair system for those sources, at the bridge's hypotheses. The construction supplies neither a general strict weight certificate nor a general extraction theorem. Independent human review remains pending; no general C4 or PSC status changes.

The [critical-component derivation](docs/c4-critical-overlap-components-2026-11-05.md) applies the classical Frobenius–Victory eigencone theorem to the exact overlap equation. A critical component can support a nonnegative solution only when every proper ancestor is subcritical; supercritical ancestors and critical predecessors force downstream mass to zero. A new canonical Mojo certificate proves the same twelve-source nullity without consuming the earlier weight vectors: **40,765** singleton components are excluded by the cubic degree and all **28** larger components have nonsingular `g(A)` over `F₁₀₁`. Independent complete-packet reconstruction passes. This adds an exact exclusion method and identifies what a surviving critical ray would require; it does not enlarge the certified source class or supply a general PSC conclusion.

The [literal inverse-row binding](docs/c4-literal-inverse-binding-2026-11-10.md) now reconstructs every one of the twelve-source graph's 253,395 occurrence slots, including both literal positions and normalization orientation. Canonical Mojo and an independent forward-position oracle agree on the full ordered inventory. Lean proofs derive row-count transport and discovery ancestry, and derive the full inverse overlap union from original tile equations under explicit action and range hypotheses. The [matrix-adic continuation](docs/c4-madic-residue-2026-11-11.md), accepted in #541, constructs the compact coherent inverse-limit carrier and proves integral range reflection for its product with a supplied stable factor. Authentic prefix tiles and their complete tile equations, complete finite ancestor coverage, product-Haar scaling and positive compact measure at a strict-cut root remain separate obligations. The complete serialized packet is not yet a closed Lean instance.

## Class A: an example of the overlap calculations

One family studied in detail is the *minus class-A* normal form. For integers `k,t ≥ 0`, let

```text
n = k + t + 3
d = 2n − 1 − k
A = n + d

x → x y^A x
c → c y^n x
y → x y^(n−1) c
```

The notation `(a,b,p,q,r)` describes an overlap with top letter `a`, bottom letter `b`, and Parikh offset `(p,q,r)`. Reversing the overlap swaps its letters and negates all three offset coordinates. Historical names such as T, Q or V are not unambiguous unless their full oriented states are given.

A *complete child star* lists every genuine outgoing occurrence of a state. A *selected coincidence path* gives one way to reach coincidence. A stronger *every-first-choice* result allows any genuine first child, then finds a coincidence path from there. None of these, by itself, shows that the entire reachable overlap graph satisfies BH.

The recovered P3 and T/X/Y0 classifications have outgoing images of 37 and 42 oriented labels respectively. They share 20 labels, giving a union of 59. That union is **not** known to be a forward-closed carrier. The [frontier audit](docs/class-a-boundary-consolidated-frontier-2026-10-31.md) explains which descendant stars are already classified and which require further checking.

Two more explicit states illustrate the progress:

- `Y0 = (y,y,1,-1,-1)` has a complete child classification and a selected coincidence exit. The [every-first-choice result](docs/class-a-boundary-y0-every-child-2026-10-31.md) gives a selected continuation after any genuine first child, within six edges from Y0.
- `CY = (c,y,0,-2,2)` has exactly `2n+1` indexed children per orientation, representing six distinct typed child labels. There is a genuine two-cycle between Y0 and CY, but also a route out to coincidence. The [CY derivation](docs/class-a-boundary-cy-carrier-2026-10-31.md) gives the full classification.

The mainline also records a [four-edge coincidence path from U](docs/class-a-boundary-U-hit-recovery-2026-10-31.md), [selected coincidence completion after every genuine CY first choice](docs/class-a-boundary-cy-every-child-2026-10-31.md) within seven edges from CY, and the [four-occurrence star of `CC = (c,c,0,-2,3)`](docs/class-a-boundary-cc-carrier-2026-10-31.md). The [CC every-first-choice result](docs/class-a-boundary-cc-every-child-2026-10-31.md) gives a selected completion within five edges from CC. These statements allow a selected continuation after the first choice; they do not require every subsequent path to terminate. The Y0 last-letter transition to this exact CC state is strict only when `t=0`.

The [accepted 22-specimen finite certificate](docs/completion-ledger-2026-11-02.md) supplies complete outgoing records and shortest-distance witnesses at its named parameters. Subsequent merged work gives a uniform one-generation target-predecessor description, finite-place digit-ladder interfaces and a Smith trichotomy. Their [separate evidence and scope record](docs/current-state-reconciliation-2026-11-11.md#class-a-implemented-pieces-and-open-gates) retains the historical failed workflows. Uniform entry into the predecessor segments, complete all-descendant coverage, native-to-Lean refinement and the non-unit realization transfer remain open.

The class-A calculations provide increasingly detailed information about the descendant graph. The remaining task is not merely to find more short paths, but to account for **all relevant cyclic strict-zipper states** through a uniform argument.

## The work ahead

The immediate goal is a general proof of BH. In the structured determinant-two families, this means finishing the class-A and class-C parameter regions and the class-B top layer while keeping every occurrence and endpoint condition. Beyond those families, the argument must work in the complete non-unit representation space, including the necessary finite-place coordinates.

The aligned A1′ problem is separate. Its remaining fixed-hub cases, including the non-crossing family-F residue, must also be resolved without adding hypotheses absent from the original conjecture.

When both obstructions are eliminated, the completion theorem will connect them to seed productivity and the density-to-spectrum implication. Other investigations—renewal finiteness, finite balanced-pair automata, component productivity and realization—may supply useful tools, but need not all be solved first.

The scope of each result matters. The standing assumptions are primitivity, nonzero determinant, irreducibility over the rationals, and the Pisot condition. A proof must not quietly assume unimodularity, independent tile lengths, injectivity, a uniform finite collar, or a Euclidean-only realization.

**Unique decodability:** repository-proved from full incidence rank when needed, rather than imposed separately.

## Reading the proofs and running the code

The mathematical entrypoints are the [proof ladder](docs/proof-ladder.md), [direct-attack analysis](docs/direct-attack-frontier-2026-10-23.md), and [state-of-program manuscript](manuscripts/PSC_balanced_pair_state_2026-09-13.tex). For the precise status and evidence behind a particular assertion, consult [claim governance](claim_governance.toml), the [claim/source map](docs/claim-status-and-source-map-2026-09-13.md), and the [proof bank](docs/proof-bank.md).

Executable research is primarily written in [Mojo](kernel/); [Python oracles](oracles/) provide independent checks. The repository also contains [Lean proofs](proof/PscVerif/) and [TLA+ models](proof/tla/) at their documented scopes.

The [overlap Lean layer](docs/c4-overlap-lean-interface-2026-11-05.md) verifies the deductive certificate interface: period-three compatibility with two-step refinement, exact integer subinvariant soundness, and null-overlap inference from complete occurrence covers and measure scaling. A [concrete packet binding](docs/c4-overlap-lean-packet-binding-2026-11-05.md) adds exhaustive kernel checks and full native/oracle parity as a separate replay gate. Its original acceptance scope is recorded separately. Later Lean modules construct the matrix-adic carrier and conditional literal covers; authentic compact tiles, complete finite geometric coverage and the measure bridge remain additional premises. This is not a complete Lean verification of PR #496 or PSC.

The main verification commands are:

```bash
./tools/verify_all.sh

cd kernel
pixi run test
pixi run verify
```

The verification script reports missing toolchains as skipped, not passed. Finite tests, symbolic proofs, hosted CI and independent review should be reported separately.

**Independent human review is a final validation gate, not a research-progress gate.** A result labelled `human review pending` may still be used at its exact recorded scope; the label stays until that review actually happens ([AGENTS.md](AGENTS.md#review-gate)).

For the history of the research, including superseded arguments, see the [completion ledger](docs/completion-ledger-2026-10-26.md), [side-notes journal](docs/side-notes-ledger.md), [branch recovery audit](docs/branch-conjugate-audit-2026-10-30.md) and [archive](archive/). The [Plastic-A/Padovan](docs/post-proof-padovan-plastic-a-conjectures-2026-09-23.md) and [Penrose](docs/bridges/penrose-2d-to-psc-interface-program.md) programmes provide related benchmarks and geometric comparisons, not missing premises of the direct PSC argument.

This README is an introduction. The governed claim records and the proofs themselves determine what has been established.
