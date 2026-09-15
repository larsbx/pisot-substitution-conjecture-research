# Response to the referee report

**Manuscript:** *The balanced-pair route to the Pisot substitution conjecture: finite obstructions, two open gates, and the current frontier* (`manuscripts/PSC_balanced_pair_state_2026-09-13.tex`).
**Referee report:** `manuscripts/codex-referee-report-2026-09-13.md` (Codex, review of commit `66e43cd` on pull request #65, posted 2026-09-13T03:13Z).
**Revision:** the manuscript as committed on the branch `claude/pisot-conjecture-manuscript-ax4m51` after the review, together with the recompiled PDF.

We thank the referee for a careful reading. All seven findings are accepted. Two of them (Findings 1 and 3) concern genuine overstatements in the first draft, and we are grateful that they were caught before the manuscript circulated further. The table below maps each finding to the edit made; details follow.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 1 | P1 | Concentration was described as "absorbed" although it is only equivalent to the higher-degree case | Accepted. Concentration restored as an explicit open problem; abstract, headline status, Section 5.7, the unresolved-statements list, and the discussion reworded | Abstract; §1.4 third bullet; §5.7 (new Open Problem "Concentration"); §8 items 6–8; §9 |
| 2 | P2 | "Closed" was defined too strongly for the "closed productive" cases discussed | Accepted. "Closed" now means every noncoincident child stays in the component; the equivalence "closed and nonproductive ⇔ closed with no coincidence child" is stated | Definition 2.11 |
| 3 | P1 | The claim "if \|det M\|>1 and \|C\|=3 then r ≥ 5" used ρ(S)=β without justification | Accepted. Claim removed; the three-state clause is split into the Perron-extremal case and the non-extremal case, and the unknown status of r ∈ {2,3} with ρ(S)<β is stated | Theorem 5.17 statement and proof sketch |
| 4 | P3 | f(−2) = −10, not −8 | Accepted and corrected | Example 4.8 |
| 5 | P2 | "Exhaustive enumeration at length 12" was not documented | Accepted. The word "exhaustive" and the minimality implication are removed; only the directly checkable witness is kept | Computational Proposition 6.3, limitation paragraph |
| 6 | P2 | K₂ was used both as a vector in Z^{d²} and as an element of Λ²Z³ | Accepted. The antisymmetry of K₂ on balanced pairs and the identification with (K₁₂,K₁₃,K₂₃) are stated before first use and recalled where the area identity is used | §5.5 (after the definition of K_r); Proposition 5.19(iii) |
| 7 | P2 | Placeholder citation for the Wielandt equality case | Accepted. Replaced by Horn–Johnson, *Matrix Analysis*, Thm 8.4.5; the equality-case argument now spells out the entrywise equality of the absolute value of S with N, the diagonal unitary similarity, the cycle-phase argument, and the reduction of the phases to ±1 | Proposition 5.13 proof; bibliography |

## Detailed responses

### Finding 1 (P1) — concentration

The referee is right. The wedge dichotomy (Proposition 5.20) proves: for a closed nonproductive component either K₂ ≡ 0 or the K₂ vectors span Λ²Q³, in which case the dominant projection is nonzero somewhere. This makes step (a) of the spectral route ("concentration") *equivalent* to the statement that no closed nonproductive component has K₂ ≡ 0; it does not make it automatic, because the K₂ ≡ 0 case is exactly the case the higher-degree sieves constrain without excluding. The first draft's phrase "absorbed" was therefore misleading.

Edits. (i) The abstract now says that the dichotomy shows concentration is equivalent to excluding closed nonproductive components with vanishing degree-two defect, and the final step is equivalent to excluding those with nonvanishing degree-two defect, and that both remain open. (ii) The headline status bullet in §1.4 says the same. (iii) Section 5.7 now states two open problems side by side, "Concentration" (no strict component with K₂ ≡ 0) and "Wedge productivity" (no strict component with K₂ ≢ 0), explains that (b) follows from (a) with no Galois argument, and says explicitly that we have found no proof of (a) or of (c). (iv) The unresolved-statements list (§8) has a separate "Concentration" item, and the "Higher first defects" item cross-references it. (v) The discussion no longer speaks of eliminating concentration as a gate; it says the spectral route splits the coincidence problem by first defect degree into the two open problems and that we regard this as a clarification, not progress. The referee's remark that the headline statements for G1b-2 and the Pisot substitution conjecture are accurate is noted with thanks; those statements are unchanged.

### Finding 2 (P2) — closed versus closed among noncoincident children

Accepted. Definition 2.11 now defines an SCC to be *closed* if every noncoincident child of every state lies in it, with coincidence children allowed, and records that a closed SCC is nonproductive if and only if no state in it has a coincidence child. With this definition the remark after Theorem 5.2 (closed productive components with ρ(N) < β) and Proposition 5.21 ("productive or not") are consistent, and a *strict component* (finite, closed, nonproductive, recurrent, noncoincident) has the meaning used throughout Section 5. The sink component produced in Theorem 5.1 is closed in the stronger sense as well, so that proof is unaffected; the Parikh intertwiner (Theorem 5.2) uses closedness together with nonproductivity, which is what it needs.

### Finding 3 (P1) — three-state higher-degree conclusion

Accepted. Proposition 5.13 gives diagonal similarity of S to ±N only in the Perron-extremal case ρ(S) = β, and the first draft used that similarity for |C| = 3 without the hypothesis. The sentence "if |det M| > 1 and |C| = 3 then r ≥ 5" has been removed. Theorem 5.17 now states, for |C| = 3: in the extremal case ρ(S) = β one has r ≡ 1 (mod 3), |det M| = 1, and the image of Q_r is the constituent det(M)^m ⊗ M; in the non-extremal case ρ(S) < β one has r ≡ 0 or 2 (mod 3). The proof sketch is rewritten accordingly, and it states that we do not know whether a three-state strict component can have ρ(S) < β with r ∈ {2, 3}; Theorem 5.16(ii),(iii) constrain but do not exclude those cases. The general statement "r = 4 forces |det M| = 1 and ρ(S) = β" is retained, since it uses only Theorem 5.15 and the degree-4 spectral floor and does not depend on |C|.

### Finding 4 (P3) — rational-root values

Corrected to −4, −2, −2, −10.

### Finding 5 (P2) — exhaustive enumeration

Accepted. The manuscript now presents the length-12 pair only as a directly checkable certificate that first defect degree four occurs for irreducible ternary balanced pairs, and explicitly makes no claim that the length is minimal. (Independently of the manuscript, we verified by exact computation that the displayed pair is balanced, irreducible, has vanishing defects through degree three, and has nonzero degree-four defect.)

### Finding 6 (P2) — degree-two identification

Accepted. Immediately after the definition of K_r in §5.5 the manuscript now proves that K₂ is antisymmetric on balanced pairs (K_aa = 0 and K_ab + K_ba = 0 because the two words have the same letter counts) and fixes the identification of K₂ with (K₁₂, K₁₃, K₂₃) ∈ Λ²Z³ for d = 3, noting that this is the instance Lie₂ = Λ² of Theorem 5.15 and that the identification is used in §5.6 and §5.7. Proposition 5.19(iii) recalls the identification before the equality area(u) − area(v) = 2K₂(T).

### Finding 7 (P2) — Wielandt citation

Accepted. The placeholder is replaced by Horn and Johnson, *Matrix Analysis* (Cambridge, 1985), Theorem 8.4.5, and the bibliography entry is added. The proof of Proposition 5.13 now states the equality case in full: if λ = βe^{iφ} is an eigenvalue of S of maximal modulus and |S| ≤ N with N irreducible, then |S| = N and S = e^{iφ} D N D⁻¹ for a diagonal unitary D; hence every edge sign is e^{iφ} d_i d_j⁻¹ and the sign product around a directed cycle of length L is e^{iφL} ∈ {±1}; when N is primitive the cycle lengths have greatest common divisor 1, so e^{2iφ} = 1 and e^{iφ} = ±1; since S and ±N are real with the same support and the graph is strongly connected, the phases d_i can be rescaled to ±1. This covers the three points the referee asked to be verified (irreducible N, complex peripheral phases, reduction to ζ = ±1).

## Changes made independently of the report

Before the review was received we corrected one sentence in Example 7.1: the period-3 leftmost-child cycle in the flipped-Tribonacci component runs through (12,21) → (213,312) → (1213,3121), not "the first three states" as an earlier version of this program stated; the state (13,31) has the single noncoincident child (12,21). This was verified by direct computation and does not affect any argument.

## Items not changed

No finding requested changes to the imported theorems, the computational propositions other than Finding 5, or the status statements for G1b-2 and the Pisot substitution conjecture; these are unchanged.

## Second round (re-review of `03d085a`)

The referee re-reviewed the revised head and posted two further findings; both are accepted.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 8 | P2 | The new equivalence "closed SCC nonproductive iff no coincidence child" fails for a coincidence singleton, which is closed, has no coincidence child, and is productive | Accepted. The equivalence is restricted to closed *noncoincident* SCCs, and the coincidence-singleton case is noted explicitly | Definition 2.11 |
| 9 | P3 | Unescaped bars in the Finding 7 table row of this document broke the Markdown table | Accepted. The cell is reworded without literal bars | This document, first table, row 7 |

### Finding 8 (P2)

Accepted. Under Definition 2.11 a reachable coincidence block $(a,a)$ is a terminal singleton SCC that is closed (it has no noncoincident children) and has no coincidence child, yet is productive by the empty path. The sentence now reads: a closed *noncoincident* SCC is nonproductive if and only if no state in it has a coincidence child, with the singleton case noted in parentheses. Every later use of the equivalence (Theorem 5.1, Section 5.2, Proposition 5.20, Proposition 5.21) already carried the noncoincidence hypothesis, so no other statement changes.

### Finding 9 (P3)

Accepted; the table cell is reworded.

---

## Third round (pull request #69, G1b-1 reconstruction)

The referee reviewed the bounded-discrepancy import and posted three findings; all are accepted. None concerns the mathematics of Theorem 4.4 or Proposition 4.11.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 10 | P1 | The Python census screened the corpus with floating-point roots and a tolerance, so "exact" was overstated | Accepted. Screening is now exact: rational-root test for irreducibility and Sturm sequences over the rationals for the Pisot property, mirroring the repository's exact procedure; the corpus size and every reported statistic are unchanged | `scripts/swap_discrepancy_census.py` |
| 11 | P1 | Proof-support computation was Python-only, against the Mojo-first policy | Accepted. Canonical Mojo kernel, census driver and deterministic regression added; the Python layer is retained as the independent oracle and both layers agree | `mojo/psc/swap_discrepancy.mojo`, `mojo/swap_discrepancy_census.mojo`, `mojo/tests/test_swap_discrepancy.mojo`; proof note, section 6 |
| 12 | P2 | The backward direction of the realization equivalence needs the realizing windows to be cofinal; it is not definitional | Accepted. The backward direction is restated with cofinal coverage as an explicit hypothesis and a new gap (G3) records it; the gap count in the conclusion is updated | `docs/source-imports/issue-45/realization-coincidence-rank-audit.md`, sections 2–3 |

### Finding 10 (P1)

Accepted. The floating-point Cardano/Newton screen with a `1e-9` margin is replaced by the exact criterion used by the canonical kernel: a monic integer cubic is irreducible iff it has no integer root dividing its constant term; it is Pisot iff Sturm counting over the rationals finds exactly one root above one and, in the three-real-root case, two roots in the open unit interval, while in the one-real-root case `beta |beta_2|^2 = det` reduces the condition to `chi(det) < 0`. The exact screen reproduces the corpus of 4,554 and the same maximum discrepancy, longest state and histogram.

### Finding 11 (P1)

Accepted. The kernel now exists in the canonical layer with a fixed three-coordinate accumulator and no floating point, and the regression pins the reduction step (blocks of an inflated seed inherit the swap-walk bound) and the example values (Tribonacci flat at 1; the level profile of the non-unimodular example up to level 18; reachable maxima 1 and 5). The Python module is kept as an independent oracle, as the policy allows, and the proof note names the Mojo implementation as canonical.

### Finding 12 (P2)

Accepted. Coincidence-freeness of windows implies coincidence-freeness of the tilings only when the windows cover every position of the pair. The audit now states the backward direction with cofinal coverage as a hypothesis, records it as gap (G3), renumbers collar completeness to (G4), and keeps the conclusion that the equivalence is a conjectural bridge.

---

## Fourth round (pull request #69)

One further finding on the realization audit; accepted.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 13 | P2 | The gap inventory omitted two forward-direction requirements named in the same note (transfer of non-coincidence to reductions; recurrence under G1), so the gap count was inconsistent | Accepted. Entries (G5) transfer of non-coincidence and (G6) recurrence added; conclusion now refers to (G0)–(G6); README and provenance summary synchronized to the seven obligations | `docs/source-imports/issue-45/realization-coincidence-rank-audit.md`, section 3; `README.md`; `docs/source-provenance-v16-later-audit-2026-09-12.md` |

### Finding 13 (P2)

Accepted. The two requirements were stated in section 2 as (b) and (c) but not carried into the table, so the "with (G0)–(G4) open" conclusion under-counted. They are now (G5) and (G6), both marked open with the note that neither has ever been written down in reachable history, so there is nothing to recover; the downstream summaries say seven obligations G0–G6.

---

## Fifth round (pull request #69)

Two further findings; both accepted.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 14 | P2 | The limitation paragraph of the discrepancy census called the level profile of the non-unimodular example "still increasing", although the exact computation shows the profile is bounded by the reachable maximum 5 and attains it at level 15 | Accepted. The paragraph now states the sharp fact (a swap walk splits at its zero returns into reachable states, so the level supremum never exceeds the reachable maximum, attained at level 15) and contrasts it with the far larger analytic constant, whose slow convergence is the only thing the second eigenvalue's modulus explains | Computation 6.3, limitation; proof note, section 6 |
| 15 | P2 | Claim-status rule 5 of the provenance audit still called the realization equivalence source-pending, contradicting the table row | Accepted. Rule 5 now classifies it as a conjectural bridge with the seven open obligations G0–G6 | `docs/source-provenance-v16-later-audit-2026-09-12.md`, rule 5 |

### Finding 14 (P2)

Accepted. The referee's argument is exactly the reduction step of the proof of Theorem 4.4 read in the other direction: the level-`n` supremum of a swap walk is the largest discrepancy among the depth-`n` descendants of the seed, all of which are reachable states, so for a finite automaton the profile is bounded by the maximal reachable discrepancy and, for the example in question, reaches it at level 15. The earlier sentence conflated the sharp value with the slow convergence of the analytic bound; they are now separated.

### Finding 15 (P2)

Accepted; rule 5 is rewritten to match the table and the audit note.

---

## Sixth round (pull request #69)

The referee re-reviewed the revised head and posted no findings. Findings 1–15 across the six rounds are all accepted and addressed; the review record above is complete for this revision.

---

## Seventh round (pull request #72, overlap route)

Two findings; both accepted. Neither concerns Theorem 4.22, Lemmas 5.30–5.31, or parts (i)–(v) of Theorem 5.32.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 16 | P1 | With coincidences terminal, the vertex set of the overlap graph is not "every occurring type", and the child-mass identity fails on sets containing a coincidence | Accepted. The occurrence statement is weakened to what is true: every vertex is an occurring type, every occurring non-coincidence type is a vertex, and the omitted occurring coincidences are exactly the descendants of coincidences. Corollary 5.33 now states the mass identity over the geometric children and restricts the closed-set consequence to sets of non-coincidence overlaps; the finiteness bound is restated for occurring types, which bounds the vertex count. Census counts are unchanged since the graph definition is unchanged | Section 4.7 (definition paragraph, Theorem 4.22), Corollary 5.33 and its proof; note Lemma 1.1, Theorem 2.1, Corollary 4.2 |
| 17 | P1 | "G1 becomes a consequence of PDS" does not follow from the density bridge: the imported theorem gives termination ⇒ PDS only, and G1 also involves illegal seeds | Accepted. All such sentences are replaced: a positive bridge would let PDS follow from overlap productivity for one legal seed without finiteness, but would not settle G1, whose status also depends on Open Problem 4.24 and on the unused converse of Imported Theorem 2.16 | Section 5.9 closing paragraph, headline status bullet, Section 8 item, Section 9 discussion; note section 6; README; conjecture ledger; proof ladder; pull-request description |

### Finding 16 (P1)

Accepted. The referee's Tribonacci example is exact: the coincidence `(1,1,0)` has geometric children that are the coincidences of the inflated tile, and the graph does not form them. The definition of the graph is kept (coincidences terminal, as for the balanced-pair automaton), and the statements are now those the definition supports.

### Finding 17 (P1)

Accepted. The inference reversed an implication that is used in one direction only and ignored the seedwise question; it is withdrawn everywhere it appeared.

---

## Eighth round (pull request #72)

The referee re-reviewed the revised head and posted no findings. Findings 16–17 are addressed; the record for the overlap-route revision (Theorem 4.22, Lemmas 5.30–5.31, Theorem 5.32, Corollary 5.33, Open Problems 5.34–5.35) is complete.

---

## Ninth round (pull request #77, density import)

Four findings; all accepted. None concerns Imported Theorem 5.37 or the hypothesis check preceding Theorem 5.38.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 18 | P1 | `G_m ⊆ G_{m+1}` is false as stated: subdivision points of an inflated common tile lie in the parent interior but in no child interior, and the proof of Lemma 5.36 (c)⇒(a) relied on it to pick a level `m ≥ N` | Accepted. The nesting claim is replaced by the true statement: `G_m \ G_{m'}` is finite for every `m' ≥ m` (finitely many subdivision points per level). The proof of (c)⇒(a) now picks any level `m` with `U ∩ G_m ≠ ∅`, notes that this open set is infinite, and passes to `m' = max(m, N)` by finiteness of the difference; the refinement of the inflated level-`N` tiles by the level-`m'` tilings is made explicit. (b)⇒(c) used only `G(s) ⊇ G_m(s)` and is unchanged | Section 5.9, good-set paragraph and proof of Lemma 5.36 |
| 19 | P2 | Note item 6.3, note Section 7 introduction, audit Section 7 and claim-map item 5 still call the transfer the remaining step and list a density-bridge open problem | Accepted. All four passages are rewritten: the transfer is unproved but not needed for sufficiency, the density bridge is the imported theorem, and the only open input of the route is Open Problem 5.35 | Note Sections 6 and 7; audit Section 7; claim map completion program item 5 |
| 20 | P2 | The sentence before the new material still says a positive answer to Open Problem 5.35 does not give PDS | Accepted. Replaced by: Imported Theorem 2.16 alone does not, since it needs termination; Theorem 5.38 supplies the bridge that does | Section 5.9, paragraph after Open Problem 5.35 |
| 21 | P3 | Ledger route comment still calls `DensityToPDSBridge` the separate open input | Accepted. Comment rewritten: `DensityToPDSBridge` is the imported theorem (proved) and `PDSOverlapRoute` is conditional on `OverlapProductivity` alone; TLC 10/10 PASS | `tla/Ledger.tla` overlap-route comment |

### Finding 18 (P1)

Accepted. The referee is right that the sets of interiors are not nested; a common tile with two or more children loses its subdivision points at the next level. What the argument needs is weaker and true: each `G_m` differs from every later `G_{m'}` by finitely many points, so an open set meeting `G_m` meets `G_{m'}`. The lemma statement is unchanged.

---

## Tenth round (pull request #77)

Two findings; both accepted. Neither concerns the manuscript.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 22 | P2 | The note's Lemma 8.1 still asserts that the `G_m(s)` increase and its proof still picks a witnessing level at least `N` without justification | Accepted. The note now carries the manuscript's finite-difference statement and the repaired proof of (c)⇒(a) verbatim in substance | Note Section 8, good-set paragraph and proof of Lemma 8.1 |
| 23 | P2 | The probe passed the heuristic window `14 + k` to `oa_types`, below the documented bound `(g(W) + l_max)/l_min` for large length ratios, so level-0 types could be missed | Accepted. The bound is now computed exactly in `Q(β)` (`oa_window`: least `n` with `n·l_min > g(W) + l_max`, decided by exact signs) and used by default; an explicit smaller window, or a prefix too short for the window, raises (fail closed). The same heuristic (`window = 14`, `k ≤ 8`) had been used for the Section 7 sample table, so both the sample and the probe were re-run with the exact window; the recomputation reproduced every reported figure exactly (same 22 failures, same least witnesses, same type counts), and the note now states the method with the exact window | `src/psc_research/oa_overlap_graph.py` (`oa_window`, `oa_types`, `type_inclusion_report`), both scripts, regression tests in `tests/test_oa_overlap_graph.py`; note Section 7 table and addendum |

### Finding 23 (P2)

Accepted. The referee's example is exact: for `1 → 2, 2 → 3, 3 → 133` the bound at `k = 24` is 87 against the 38 passed. Since a too-small window can only omit level-0 types, the earlier figures could over-report inclusion; they were withdrawn pending the exact-window rerun, which reproduced them exactly; they are restated with the exact method, still labelled exploratory and uncertified.

---

## Eleventh round (pull request #79)

The automated Codex review of commit `90663fb3af9c1f87f8cea7c5040e4afc90d75ecd`, containing the substantive exact-window restatement of the Section 7 figures, posted no findings. Findings 18–23 are recorded as addressed.

---

## Twelfth round (pull request #82, strong-coincidence revision)

Two findings from the automated Codex review of commit `68a392abcbccb0a874e7b090718a6d9233dab2af`; both accepted. Neither affects the identification of endpoint-aligned productivity with eventual coincidence, the hitting criterion (a)⇔(c), or the census values.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 24 | P2 | "For every ordered `i ≠ j`, `(i, j, 0)` is a seed overlap" does not match a graph seeded with one orientation per unordered pair; `(3,2,0)` is absent for `τ` | Accepted. Proposition 5.39 now states the top/bottom exchange `(a, b, t) ↦ (b, a, −t)` (commutes with inflation, preserves coincidences), fixes `(ij, ji)` as the seed of the unordered pair in the orientation used to generate the graph, and states the ordered claims for both orientations as consequences; (iii) is phrased per unordered pair. The depth API docstrings say that each pair is counted in the orientation that occurs and that the depth is orientation-independent; Computation 6.7 says so too | Proposition 5.39 and proof; Computation 6.7; `overlap_graph.py`, `overlap_seed_patch.mojo` docstrings; note Section 9 |
| 25 | P2 | Condition (b) admitted the bottom tile's right endpoint as a "boundary coincidence", where (c) fails; the example `1→2, 2→3, 3→12`, `O = (3,3,−1)`, level 1 is exact | Accepted. (b) now reads: some sub-tile of the inflated top tile and some sub-tile of the inflated bottom tile have the same left endpoint (a common boundary other than the right endpoint of either inflated tile); the proof of (a)⇔(b) is restated in terms of sub-tile left endpoints, and Corollary 5.41(iii) is restated accordingly. The propagated statements in the note, both ledgers, and the TLA ledger comment are corrected; the code measured the corrected notion already | Proposition 5.40 statement and proof; Corollary 5.41(iii); note Section 9; `docs/conjecture-ledger.md`, `docs/proof-ladder.md`; `tla/Ledger.tla` comment |

### Finding 25 (P2)

Accepted. The referee's example is exact: at level 1 the bottom tile `[−1, 1]` of `(3,3,−1)` ends at the internal top boundary `1`, no bottom sub-tile starts there, and `M w = −e_2` is not a difference of proper-prefix Parikh vectors. The equivalence (a)⇔(c) was never in doubt; (b) was the wrong paraphrase of it, and the census function measured (c).

---

## Thirteenth round (pull request #82)

One finding from the automated Codex review of commit `310f06c06bdf757745cdb9c19f4e0411d20a9cd5`; accepted. It concerns the Python oracle only.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 26 | P2 | The Python depth helper returned depths on a capped partial graph, unlike the canonical Mojo kernel | Accepted. `first_depths` now raises on a capped graph (so do the coincidence, left-aligned and strong-coincidence wrappers), matching `_first_depths` and `nonproductive`; regression test on `τ` with `max_states = 1` | `src/psc_research/overlap_graph.py`; `tests/test_swap_discrepancy.py` |

---

## Fourteenth round (pull request #82)

Two findings from the automated Codex review of commit `3dc397856ab8ceaf0298c34c3e1df8855e612f10`; both accepted. Both concern the census driver; no census value changes.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 27 | P2 | A nonproductive graph would raise in the depth validations before being counted, so a counterexample would surface as `FAILED` with the nonproductive count still zero | Accepted. The driver now records and prints a nonproductive specimen immediately after the productivity check and skips the depth statistics for it, which are undefined on such a graph | `mojo/swap_overlap_census.mojo` |
| 28 | P2 | The prefix and suffix strong-coincidence scans each recomputed the coincidence depths, three reverse searches per graph | Accepted. `strong_coincidence_depth_from(depths, ...)` takes the precomputed vector (length-checked); `strong_coincidence_depth` wraps it; the census passes the one vector it already holds. The Python oracle takes an optional `depths` argument likewise. Census lines unchanged | `mojo/psc/overlap_seed_patch.mojo`, `mojo/swap_overlap_census.mojo`, `mojo/tests/test_overlap_seed_patch.mojo`, `src/psc_research/overlap_graph.py`, `scripts/overlap_depth_census_oracle.py` |

---

## Fifteenth round (pull request #82)

Two findings from the automated Codex review of commit `2288163613668619be3185e97b1474ca059f3dc2`; both accepted. Both concern the Mojo census path; no census value changes.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 29 | P2 | `strong_coincidence_depth_from` accepted a capped automaton with a length-matching vector | Accepted. It now raises on a capped automaton before consuming the depths, like `_first_depths`; regression test with a capped graph | `mojo/psc/overlap_seed_patch.mojo`, `mojo/tests/test_overlap_seed_patch.mojo` |
| 30 | P2 | The census rebuilt the exact tables for the endpoint scans after `build_seed_overlap_graph` had built them | Accepted. `build_seed_overlap_graph_from_tables(tables, cap)` is the builder; `build_seed_overlap_graph(sigma, cap)` wraps it; the census builds the tables once per specimen and passes them to the graph construction and both scans | `mojo/psc/overlap_seed_patch.mojo`, `mojo/swap_overlap_census.mojo` |

---

## Sixteenth round (pull request #87, contracting bound)

Three findings from the automated Codex review of commit `3b8e6d42acfac4c1d9c23abe6f5190e6656e0ce8`; all accepted.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 31 | P1 | The contracting-bound kernel and census existed only in the Python layer | Accepted. Canonical Mojo implementation: `mojo/psc/real_root_sign.mojo` (exact Sturm–Tarski queries over unbounded rationals: root counting, isolation, sign at an isolated root) and `mojo/psc/overlap_contracting.mojo` (field norm, discriminant, increment set, `ContractingBound.least_level`, capped graphs rejected; all field arithmetic in Q[x]/(χ) over unbounded rationals with every sign a Sturm–Tarski query at an isolated root, the Perron root included, since the fixed-width Perron oracle fails closed on the coefficient growth of the level tests); `mojo/tests/test_overlap_contracting.mojo` pins the same values as the Python oracle; `mojo/overlap_contracting_census.mojo` is the census driver, asserted line by line in CI; the Python module is the oracle and prints the same nine summary lines (without the specimen-count header) | `mojo/psc/real_root_sign.mojo`, `mojo/psc/overlap_contracting.mojo`, `mojo/tests/test_overlap_contracting.mojo`, `mojo/overlap_contracting_census.mojo`, `mojo/pixi.toml`, `.github/workflows/ci.yml` |
| 32 | P1 | "Dominated by a scale-free combinatorial part" and "cannot come from a contraction argument" do not follow from `b ≥ m_0`, since the excess includes the slack of the triangle and Cauchy–Schwarz steps | Accepted. Every such sentence is replaced by the statement the executable result supports: this magnitude bound accounts for at most 7 of the up to 17 inflations and leaves a gap of up to 14, the gap includes the slack of the bound, and whether a sharper contracting-space argument explains part of it is not decided | Computation 6.7 "Meaning"; note Section 10; `docs/conjecture-ledger.md`, `docs/proof-ladder.md`, `README.md`, `docs/README.md`; pull-request description |
| 33 | P1 | `N(c)/c` and `N(t)/t` are undefined at the zero increment and at offset-zero vertices, while the code excluded them silently | Accepted. Proposition 5.42 now defines `m_0(0) = 0` separately, states the complex-pair display for `t ≠ 0`, and takes `K` over `F \ {0}` (the zero increment contributes nothing to `C_ς`); the proof and the note say the same, and both implementations match the statement | Proposition 5.42 statement and proof; note Section 10 |

---

## Seventeenth round (pull request #87, canonical-implementation revision)

Two findings from the automated Codex review of commit `7d74aa42c3ce138afe85b332b4964e30f58dacd2`; both accepted.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 34 | P1 | The rational Horner evaluator lived in `real_root_sign.mojo` instead of the designated adapter | Accepted. `eval_q_poly_at_q` now lives in `mojo/psc/exact.mojo` next to the integer Horner helper; `real_root_sign.mojo` imports it and keeps only polynomial algebra (trim, derivative, product, remainder) and the Sturm–Tarski queries | `mojo/psc/exact.mojo`, `mojo/psc/real_root_sign.mojo` |
| 35 | P1 | The complex-pair test decided the Cauchy–Schwarz relaxation `N(t)/t ≤ K m Σ ρ^s`, which is one-way, so the census was not a census of the stated `m_0` (example: `1→2, 2→33, 3→213`, offset `(−8, −2, 5/2)`: relaxation 5, defining inequality 6) | Accepted. Both implementations now decide the defining inequality exactly: with `ρ = β/D`, `(Σ_{s≤m} ρ^{s/2})² = A_m + ρ^{1/2} B_m` with `A_m, B_m ∈ Q(β)` (`n_k = min(k−1, 2m+1−k)` pairs), so `N(t)/t ≤ K(A_m + ρ^{1/2}B_m)` iff `N(t)/t ≤ K A_m`, or `N(t)/t > K A_m` and `(N(t)/t − K A_m)² ≤ K² ρ B_m²`: at most two sign tests at `β`, no relaxation. Proposition 5.42 and its proof state this formulation; every mention of Chebyshev or Cauchy–Schwarz is removed from statement, proof, "Meaning", note Section 10, and both implementations. The referee's example is pinned in both regression suites (`m_0 = 6`), and the census was rerun with the exact test in both implementations and repinned in CI, Computation 6.7, the note, the ledgers, and the READMEs (the largest `m_0` rises from 7 to 8, attained on 12 vertices of 6 substitutions; the largest excess stays 14; the totally real specimens are unchanged) | Proposition 5.42 statement and proof; Computation 6.7; note Section 10; `mojo/psc/overlap_contracting.mojo`, `src/psc_research/overlap_contracting.py`, `mojo/tests/test_overlap_contracting.mojo`, `tests/test_oa_overlap_graph.py`, `.github/workflows/ci.yml` |

---

## Eighteenth round (pull request #87, exact-test revision)

One finding from the automated Codex review of commit `0b989e0ccc07d5690d5413e16fc8fe07484dd590`; accepted.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 36 | P2 | `B_1 = 0`, so "`A_m` and `B_m` positive at `β`" is false for `m = 1` | Accepted. The statement now reads "`A_m > 0` and `B_m ≥ 0` at `β` (`B_1 = 0`)"; the proof already used only `ρ^{1/2} B_m ≥ 0`; the note says the same | Proposition 5.42 statement; note Section 10 |

---

## Nineteenth round (pull request #87, nonnegativity revision)

One finding from the automated Codex review of commit `059c4c5536cc4f0f9252a55a628ca90e7ea0bdf4`; accepted.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 37 | P1 | `least_level` rebuilt the level tables `A_m`, `B_m` (complex pair) and the β-powers and `G_m` (real conjugates) for every shift and level, although they depend only on the substitution | Accepted. The constructor now builds `A_m`, `B_m` for `m ≤ max_level` (complex pair) and `β^m`, `G_r[m]` (real conjugates) once per substitution; `least_level` indexes them. The Python oracle precomputes `A_m`, `B_m` the same way (its real branch already did). Census rerun: identical lines | `mojo/psc/overlap_contracting.mojo`, `src/psc_research/overlap_contracting.py` |

---

## Twentieth round (pull request #87, level-table revision)

The automated Codex review of commit `eb0615f609` posted no findings. Findings 31–37 are recorded as addressed.

---

## Twenty-first round (pull request #92, obstruction normal form)

One finding from the automated Codex review of commit `e61628428e`; accepted.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 38 | P2 | Proposition 5.44(ii) called the forward-invariant aligned-pair sets "unions of cycles", which forward invariance does not give | Accepted. The statement now says that every orbit under the first-/last-letter map is eventually periodic and stays in the set, so a nonempty `A_±(S)` contains a cycle of pairs of distinct letters; the proof cites eventual periodicity of forward orbits under a self-map of a finite set together with forward invariance; the sentence after the proposition says the same | Proposition 5.44(ii) and proof; following paragraph |

---

## Twenty-second round (pull request #92, forward-invariance revision)

The automated Codex review of commit `4e68dcdc7d` posted no findings. Finding 38 is recorded as addressed.

---

## Twenty-third round (pull request #92, manuscript-source guard)

Two findings from the automated Codex review of commit `d2adbb9b97`; both accepted.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 39 | P2 | A PDF truncated after its `%PDF-` header passed the guard | Accepted. The guard now requires `%%EOF` within the last 1024 bytes, a `startxref` offset before the final `%%EOF`, and that the offset lies inside the file and points at an `xref` table or a cross-reference stream object; tests cover a header-only PDF and a bad `startxref` | `scripts/check_manuscript_source.py`, `tests/test_check_manuscript_source.py` |
| 40 | P2 | Missing or renamed manuscript files passed silently; an empty directory reported success | Accepted. `manuscripts/MANIFEST` lists the required files; the guard fails on a missing manifest, an empty manifest, any listed file that is absent, and a manifest without a `.tex` and a `.pdf`; tests cover a deleted PDF and an empty directory | `manuscripts/MANIFEST`, `scripts/check_manuscript_source.py`, `tests/test_check_manuscript_source.py` |



---

## Twenty-fourth round (pull request #95, hardened guard)

Two findings from the automated Codex review of commit `be9dfc3abf`; both accepted.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 41 | P2 | `PSC_PROOF_next_source_audit.tex` is tracked but was absent from the manifest, so deleting it passed | Accepted. Added to `manuscripts/MANIFEST` | `manuscripts/MANIFEST` |
| 42 | P2 | An in-range `startxref` pointing at any ordinary object passed | Accepted. When the offset points at an object, its dictionary must contain `/Type /XRef`; a test rewrites the offset to an ordinary object and expects failure | `scripts/check_manuscript_source.py`, `tests/test_check_manuscript_source.py` |


---

## Twenty-fifth round (pull request #95, manifest and XRef revision)

Two findings from the automated Codex review of commit `ea83b495c5`; both accepted.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 43 | P2 | With several trailers in the last 1024 bytes the guard validated the first, not the one before the final `%%EOF` | Accepted. The guard locates the final `%%EOF`, takes the last `startxref` before it, and requires the text between them to be exactly the offset; a test appends a corrupt trailer after the valid one and expects failure | `scripts/check_manuscript_source.py`, `tests/test_check_manuscript_source.py` |
| 44 | P2 | An XRef-typed object without a stream body passed | Accepted. An object-pointing offset must lead to a dictionary containing `/Type /XRef` followed by a `stream` keyword and a later `endstream`; a classic `xref` table must be followed by `trailer`; a test builds a PDF whose only object is XRef-typed with no stream and expects failure | `scripts/check_manuscript_source.py`, `tests/test_check_manuscript_source.py` |


---

## Twenty-sixth round (pull request #95, trailer revision)

Two findings from the automated Codex review of commit `c6032e3dad`; both accepted. The guard now parses the cross-reference structure instead of matching delimiter tokens.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 45 | P2 | A classic table was accepted from the bare `xref` and `trailer` keywords | Accepted. The table is parsed: `xref`, one or more `start count` subsections, exactly `count` entries of 20 bytes matching `nnnnnnnnnn ggggg n/f`, at least one entry in total, then `trailer` and a dictionary containing `/Size` and `/Root`; tests cover a minimal valid classic PDF and the entryless one | `scripts/check_manuscript_source.py`, `tests/test_check_manuscript_source.py` |
| 46 | P2 | An empty or corrupted cross-reference stream body was accepted | Accepted. The stream dictionary must contain `/Type /XRef`, `/Size`, `/Root`, `/W` and a direct `/Length`; the body must have exactly `/Length` bytes followed by `endstream`; a Flate body must inflate (other filters fail closed); the payload must be a positive multiple of the `/W` row width (plus one under a PNG predictor); tests cover an empty stream and a one-byte mutation of the repository PDF's compressed payload | `scripts/check_manuscript_source.py`, `tests/test_check_manuscript_source.py` |


---

## Twenty-seventh round (pull request #95, structural parser)

Three findings from the automated Codex review of commit `3a9d53ee10`; all accepted.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 47 | P2 | `/Length 4 0 R` was read as the direct length 4 | Accepted. The `/Length` token is parsed with an optional trailing `g R` group, and an indirect reference fails explicitly; test with `/Length 4 0 R` | `scripts/check_manuscript_source.py`, `tests/test_check_manuscript_source.py` |
| 48 | P2 | Only divisibility of the payload by the row width was checked, not the declared row count | Accepted. The number of rows must equal the sum of the `/Index` subsection counts, or `/Size` without `/Index`; tests with `/Size 100` and `/Index [0 3]` against a one-row payload, and a passing one-row stream | same |
| 49 | P2 | The array form `/Filter [/FlateDecode]` was not recognized | Accepted. `/Filter` is parsed as a name or an array of names; the chain must be exactly `[FlateDecode]`, any other form or chain fails closed; tests inflate an array-form Flate stream and reject `[/LZWDecode]` | same |


---

## Twenty-eighth round (pull request #95, length, row-count and filter revision)

Four findings from the automated Codex review of commit `a9242e36aa`; all accepted.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 50 | P2 | A file truncated right after `endstream` passed | Accepted. The stream must be closed by `endstream` followed by `endobj`; test truncates after `endstream` | `scripts/check_manuscript_source.py`, `tests/test_check_manuscript_source.py` |
| 51 | P2 | `/Index` start values and odd-length arrays were ignored | Accepted. `/Index` must be a nonempty array of start/count pairs with positive counts whose ranges lie within `/Size`; tests with `[999 1]`, `[0 1 2]`, `[0 0]` | same |
| 52 | P2 | `/W [4]` was accepted as a row width | Accepted. `/W` must have exactly three fields; test with `/W [4]` | same |
| 53 | P2 | Classic in-use entries were checked only for their textual shape | Accepted. Every `n` entry must point inside the file at the header `num gen obj` of its own object number (subsection start plus index) and generation; tests alter the offset to 8 and to 9999999999 and the generation to 1 | same |


---

## Twenty-ninth round (pull request #95, endobj, index, arity and entry revision)

Two findings from the automated Codex review of commit `9256ace9d9`; both accepted.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 54 | P2 | A classic subsection could exceed the trailer's `/Size` | Accepted. `/Size` is parsed and every subsection must satisfy `start + count ≤ /Size`; test changes the minimal classic fixture's `/Size 2` to `/Size 1` | `scripts/check_manuscript_source.py`, `tests/test_check_manuscript_source.py` |
| 55 | P2 | Cross-reference stream rows were counted but not decoded | Accepted. Every row is decoded per `/W` (type defaulting to 1 when the first field is absent); type-1 entries must point inside the file at the header `num gen obj` of their object, type-2 entries must name an object stream below `/Size`, other types fail; PNG row prediction (filters 0–4) is undone first, an unknown filter fails; tests cover an out-of-file offset, a wrong offset, an unknown type, an out-of-range object stream, and a predicted stream that decodes correctly; the passing fixtures now describe object 1 at its real offset | same |


---

## Thirtieth round (pull request #95, subsection-range and row-decoding revision)

Three findings from the automated Codex review of commit `f158aab509`; all accepted. Each is another part of the cross-reference format that the hand-written structural checks did not model, so the guard now also parses the whole file with a real PDF parser (pypdf 6.1.3, strict mode, pinned as a dev dependency and installed in the provenance CI job), dereferences every object including object-stream members, and reads the page tree; the structural checks stay in front of it because the parser repairs some offset and `/Size` mangling silently. A missing parser is a failure, not a skip.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 56 | P2 | `/Prev` chains were not followed | Accepted. The full parse follows `/Prev`; test adds `/Prev 999999` to a complete classic PDF and expects failure | `scripts/check_manuscript_source.py`, `tests/test_check_manuscript_source.py`, `pyproject.toml`, `.github/workflows/ci.yml` |
| 57 | P2 | A type-2 entry was accepted on the numeric bound alone | Accepted. The full parse resolves every object-stream member; test points object 1 at the page-tree object as its container and expects failure | same |
| 58 | P2 | Predictor parameters were not validated | Accepted. The full parse validates the predictor and its geometry; tests with `/Predictor 99` and `/Columns 999` expect failure, and a correct predictor-12 stream passes | same |
\n


---

## Thirty-first round (pull request #95, full-parse revision)

Two findings from the automated Codex review of commit `22716cd7a0`; both accepted. Both were verified before the fix: on the repository PDF the highest object number is 1132 against `/Size 1133`, and pypdf's decoder returns empty data, without raising, on a Flate payload with one flipped byte.

| # | Priority | Finding (short) | Action | Where in the revision |
| --- | --- | --- | --- | --- |
| 59 | P2 | An oversized `/Size` was accepted | Accepted. `/Size` must equal one more than the highest object number reachable through the whole cross-reference chain (type-1 and type-2 entries alike); tests inflate `/Size` to 99 on a complete classic PDF and on a cross-reference stream with a consistent `/Index` and expect failure | `scripts/check_manuscript_source.py`, `tests/test_check_manuscript_source.py` |
| 60 | P2 | Ordinary streams were dereferenced but not decoded | Accepted. Every stream object is decoded: the filter chain must be empty or exactly `/FlateDecode`, a Flate body must inflate with zlib to the end of the deflate member with no trailing bytes, and pypdf's decode (with predictors) is then applied; test flips one byte in the first content stream of the repository PDF, leaving offsets and lengths intact, and expects failure | same |
