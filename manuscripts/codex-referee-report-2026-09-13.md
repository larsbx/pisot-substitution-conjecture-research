# Codex referee report on `PSC_balanced_pair_state_2026-09-13.tex`

**Reviewer:** Codex (OpenAI), invoked as the pull-request reviewer configured on this repository, via the comment `@codex review` on pull request #65 with referee-style instructions.
**Reviewed commit:** `66e43cdbf2ccd659646bab1052a8bf107f03f35f` (first draft). The only difference between that commit and the head reviewed for content, `e452b6c`, is the correction of the flipped-Tribonacci cycle description in Example 7.1.
**Review posted:** 2026-09-13T03:13:48Z, as one review with seven inline comments on `manuscripts/PSC_balanced_pair_state_2026-09-13.tex`.
**Nature of the review:** the referee instructions requested an academic referee-style critique (mathematical correctness, hidden hypotheses, circularity, literature alignment, overinterpretation of finite evidence, notation and exposition, publishability). The reviewer's findings are reproduced verbatim below, in the order posted, with the reviewer's own priority badges (P1 = major, P2 = moderate, P3 = minor). Nothing has been edited or omitted.

---

## Review summary comment

> ### 💡 Codex Review
>
> Here are some automated review suggestions for this pull request.
>
> **Reviewed commit:** `66e43cdbf2`

---

## Finding 1 (P1) — line 584

> **Restore concentration as an unresolved implication**
>
> Proposition 5.20 proves dominant-wedge nonvanishing only after assuming \(K_2\not\equiv0\); it does not prove the former concentration/aux-B assertion that the relevant closed nonproductive carrier actually satisfies that premise. When \(K_2\equiv0\), the higher-degree sieves merely constrain a hypothetical component and do not establish productivity, so describing concentration as “absorbed” suppresses rather than discharges its missing implication. The headline statements that G1b-2 and the Pisot substitution conjecture remain open are accurate, but the abstract, this discussion, and the unresolved-statements list should retain concentration as open or explicitly say it has been abandoned in favor of unresolved higher-degree cases.

## Finding 2 (P2) — line 408

> **Use a distinct term for noncoincident-closed SCCs**
>
> Definition 2.10 declares an SCC closed only when every child remains in it; a closed noncoincident SCC under that definition cannot leak a coincidence child and therefore cannot be productive. The remark nevertheless discusses “closed productive SCCs” with a nonzero leak term, and Proposition 5.21 similarly allows a closed recurrent noncoincident SCC to be productive. Introduce a separate notion such as “closed among noncoincident children” for the leaky case, or remove the productive alternatives, so the mass-balance hypotheses and the meaning of a strict component are unambiguous.

## Finding 3 (P1) — line 543

> **Remove the unsupported three-state higher-degree conclusion**
>
> The proof claims that when \(|\mathcal C|=3\), the signed matrix \(S\) has the irreducible characteristic polynomial of \(\pm M\), but Proposition 5.13 yields diagonal similarity to \(\pm N_{\mathcal C}\) only under the additional extremal hypothesis \(\rho(S)=\beta\). For first defect degree two or three, the induced constituent can have spectral radius strictly below \(\beta\), so that hypothesis has not been established. Consequently the asserted exclusion leading to “if \(|\det M|>1\) and \(|\mathcal C|=3\), then \(r\ge5\)” does not follow; it must be removed or restricted to the Perron-extremal/gauge or anti-gauge case.

## Finding 4 (P3) — line 293

> **Correct the rational-root evaluations**
>
> For \(f(x)=x^3-x^2-2x-2\), the values at the possible rational roots \(1,-1,2,-2\) are \(-4,-2,-2,-10\), not the listed \(-4,-2,-2,-8\). The irreducibility conclusion remains valid because none is zero, but the explicit arithmetic should be corrected.

## Finding 5 (P2) — line 656

> **Qualify the unsupported exhaustive-enumeration claim**
>
> The displayed length-12 pair is itself an exact certificate that first defect degree four occurs, but the parenthetical claim of “exhaustive enumeration at length 12” does not specify the enumerated universe, quotient conventions, algorithm, or completeness certificate. A repository-wide search finds the witness preserved only as a Python regression fixture, not a canonical Mojo enumeration proving exhaustiveness; either document and regress the complete search or remove “exhaustive,” retaining only the directly checkable counterexample.

## Finding 6 (P2) — line 555

> **Define the degree-two identification used by the area identity**
>
> Earlier \(K_2(u,v)\) is defined as a vector in \(\mathbb Z^{d^2}\), whereas \(\operatorname{area}(w)\) is a three-coordinate element of \(\Lambda^2\mathbb Z^3\); thus the displayed equality \(\operatorname{area}(u)-\operatorname{area}(v)=2K_2(T)\) is currently ill-typed. State explicitly that balancedness and the shuffle identities identify the Lie-valued defect with the coordinates \((K_{12},K_{13},K_{23})\), under which \(K_{ji}=-K_{ij}\), before using the same symbol in the mid-area and wedge propositions.

## Finding 7 (P2) — line 508

> **Replace the placeholder Wielandt citation**
>
> The central equality-case argument for Proposition 5.13 cites `\cite[Thm.~2.2.x]{BermanPlemmons}`, which is an unverifiable placeholder rather than an exact literature reference. Since the gauge/anti-gauge conclusion depends on the equality characterization in the signed Wielandt comparison—not merely the elementary bound \(|S|\le N_{\mathcal C}\)—the manuscript must give the actual theorem number and verify that it covers irreducible \(N_{\mathcal C}\), complex peripheral phases, and the subsequent primitive-period reduction to \(\zeta=\pm1\).

---

## Reviewer's statement on the headline status claims

Within Finding 1 the reviewer states: "The headline statements that G1b-2 and the Pisot substitution conjecture remain open are accurate."

No finding contests the correctness of Lemma 2.4, Theorem 2.8, Theorem 3.1, Theorem 4.13, Theorem 5.1, Theorem 5.2, Lemma 5.4, Theorem 5.5, Theorem 5.12, Theorem 5.15, Theorem 5.16, Propositions 5.19–5.21, Theorems 5.24–5.25, Proposition 5.27, or Proposition 4.9, the imported citations, or the statement of the computational propositions beyond Finding 5.

---

# Second round: re-review of the revised manuscript

**Reviewed commit:** `03d085ac8f214e9ff45d7b93506225b8d3e604cc` (revision after the first report).
**Review posted:** 2026-09-13T03:23:25Z, one review with two inline comments. Reproduced verbatim.

## Finding 8 (P2) — `PSC_balanced_pair_state_2026-09-13.tex`, line 177

> **Restrict the equivalence to noncoincident SCCs**
>
> When a coincidence block `(a,a)` is reachable, it is itself a terminal singleton SCC: it is closed and has no coincidence child, but it is productive via the length-zero path to itself under the preceding definition. Thus the new “if and only if” is false as stated; qualify it with “closed noncoincident SCC” (as the subsequent uses already do).

## Finding 9 (P3) — `response-to-reviewers-2026-09-13.md`, line 17

> **Escape the matrix-norm bars in the response table**
>
> In Markdown table rendering, the unescaped bars in `|S| = N` are interpreted as column separators, so the Finding 7 row has more cells than the five-column header and the action/location mapping is rendered incorrectly. Escape these bars or express the equality without literal unescaped pipes inside the table cell.

No other findings were posted in the second round.

---

# Third round: review of the G1b-1 reconstruction (pull request #69)

**Reviewed commit:** `f0de05fcde21abcbf458edd12004e246f91435fc` (bounded-discrepancy theorem, realization audit, ledger and TLA changes).
**Review posted:** 2026-09-13T12:25:55Z, one review with three inline comments. Reproduced verbatim.

## Finding 10 (P1) — `scripts/swap_discrepancy_census.py`, lines 53–58

> **Use exact Pisot screening for the claimed exact census**
>
> The new discrepancy census is presented in the manuscript and proof note as an exhaustive exact computation, but corpus membership is decided from floating-point Cardano/Newton roots with an arbitrary `1e-9` margin. For a polynomial whose conjugate is close to the unit circle, numerical error or the tolerance can include or exclude substitutions and invalidate the reported corpus size and discrepancy histogram. Use the repository's exact Pisot/root-isolation machinery, or provide an exact separation certificate for every screened characteristic polynomial.
>
> AGENTS.md reference: AGENTS.md:L31-L32

## Finding 11 (P1) — `src/psc_research/swap_discrepancy.py`, line 28

> **Add the canonical Mojo discrepancy implementation**
>
> The new swap-walk algorithm, corpus driver, and theorem-contract regressions are Python-only; a repository-wide search for swap-discrepancy code found no Mojo counterpart or documented blocker. This leaves the proof-support computation in the secondary oracle layer rather than the repository's canonical executable layer, so the PR does not satisfy the Mojo-first review gate. Implement the discrepancy kernel and deterministic regression in `mojo/` first, retaining this module only as an independent oracle if useful.
>
> AGENTS.md reference: AGENTS.md:L16-L16

## Finding 12 (P2) — `docs/source-imports/issue-45/realization-coincidence-rank-audit.md`, lines 47–50

> **Require cofinal realized windows for the reverse implication**
>
> The proposed definition only says that a fibre pair has windows at every level reducing into the component; it does not require those windows to be nested, exhaustive, or relatively dense. A pair can therefore satisfy the stated condition in one persistent noncoincident region while still sharing coincident tiles elsewhere, so “the two tilings never coincide” does not follow and the implication to `cr(sigma) > 1` is not definitional. The realization audit should record cofinal coverage as an additional hypothesis/gap rather than declaring this direction automatic.

No finding contests Theorem 4.4, Lemmas 4.5–4.8, or Proposition 4.11 of the manuscript.

---

# Fourth round: re-review of the round-three revision (pull request #69)

**Reviewed commit:** `6024fcd5ccf2a3a1fbf3e8aefe9d7dca64d355ea`.
**Review posted:** 2026-09-13T12:40:45Z, one review with one inline comment. Reproduced verbatim.

## Finding 13 (P2) — `docs/source-imports/issue-45/realization-coincidence-rank-audit.md`, lines 65–69

> **Add the missing forward-direction gaps**
>
> Section 2 explicitly identifies transfer of non-coincidence and recurrence as separate unproved requirements (lines 30–44), but the supposedly complete G0–G4 inventory contains neither: G1 covers reachability and G2 only window existence/density. Consequently the conclusion that G0–G4 are the outstanding gaps drops two obligations needed for the forward implication and leaves downstream summaries with an inconsistent gap count. Add explicit entries for requirements (b) and (c), then synchronize the README and provenance summary.

No other findings were posted in the fourth round.

---

# Fifth round: re-review of the round-four revision (pull request #69)

**Reviewed commit:** `31516caded547a255277c08598f9b4f58ac8416e`.
**Review posted:** 2026-09-13T12:49:24Z, one review with two inline comments. Reproduced verbatim.

## Finding 14 (P2) — `PSC_balanced_pair_state_2026-09-13.tex`, line 705

> **Correct τ's already-attained profile maximum**
>
> The profile is not merely “still increasing” with an unknown attainment point: `test_tau_profile_and_reachable_maximum` builds τ's complete uncapped automaton and establishes that every reachable state's discrepancy is at most 5, while the displayed profile reaches 5 at level 15. Because every inflated swap walk decomposes at zero returns into reachable states and resets to zero between blocks, its supremum can never exceed that reachable maximum at later levels. This sentence therefore contradicts the exact computation and should state that the profile attains 5 by level 15, while distinguishing that sharp value from the much larger analytic `D_sigma`.
>
> AGENTS.md reference: AGENTS.md:L55-L55

## Finding 15 (P2) — `docs/source-provenance-v16-later-audit-2026-09-12.md`, line 29

> **Synchronize the remaining realization status rule**
>
> Fresh evidence after `31516ca` is the unchanged claim-status rule at line 61 of this same audit: the new table declares the realization equivalence “NOT SOURCE-PENDING,” while that rule still says it “remains a source-pending reformulation.” These mutually exclusive classifications leave the provenance policy ambiguous for downstream ledgers and manuscript updates; update rule 5 to classify it as the conjectural bridge established by the new audit.

No other findings were posted in the fifth round.

---

# Sixth round: re-review of the round-five revision (pull request #69)

**Reviewed commit:** `96af25700158e65c736be1d35d431a3ebe228540`.
**Review posted:** 2026-09-13T12:55:33Z. Reproduced verbatim.

> Codex Review: Didn't find any major issues. Can't wait for the next one!

No findings were posted in the sixth round.

---

# Seventh round: review of the overlap-route revision (pull request #72)

**Reviewed commit:** `01b5281cd033c1006318dad0e8545a29634469d4` (finiteness of the seed-patch overlap graph, coincidence density, Level 3 without G1).
**Review posted:** 2026-09-13T15:10:10Z, one review with two inline comments. Reproduced verbatim.

## Finding 16 (P1) — `PSC_balanced_pair_state_2026-09-13.tex`, line 411

> **Preserve descendants of coincidence vertices**
>
> Declaring coincidences terminal contradicts the claim later in this same line that the graph contains every overlap type occurring at every level, and it invalidates Corollary 5.33's child-mass identity for sets containing a coincidence: for Tribonacci, `(1,1,0)` is reachable, but inflating it produces the occurring coincidence `(2,2,0)`, which the terminal traversal omits; its graph row is therefore zero rather than having child mass `beta*lambda`. Either retain the geometric children of coincidence vertices (and update the census counts) or weaken the occurrence statement and restrict the mass identity to noncoincident child-closed sets.
>
> AGENTS.md reference: AGENTS.md:L49-L55

## Finding 17 (P1) — `PSC_balanced_pair_state_2026-09-13.tex`, line 760

> **Do not infer G1 from the density bridge**
>
> Even if Open Problem 5.35 is answered positively, it supplies only `delta=1 => PDS`, while Imported Theorem 2.16 supplies `termination => PDS`; neither implication can be reversed to obtain termination from PDS. In particular, G1 concerns the union over every seed, including illegal seeds, and lines 433–437 explicitly leave that seedwise implication open. The claim that G1 would become a consequence of PDS—also repeated in the README and the new note—therefore still requires Open Problem 4.24 and should not be attributed to the density bridge.
>
> AGENTS.md reference: AGENTS.md:L49-L55

No other findings were posted in the seventh round.

---

# Eighth round: re-review of the round-seven revision (pull request #72)

**Reviewed commit:** `5275b4568a83818cf9fc56971d52f5e6adf6edcf`.
**Review posted:** 2026-09-13T15:22:38Z. Reproduced verbatim.

> Codex Review: Didn't find any major issues. Delightful!

No findings were posted in the eighth round.

---

# Ninth round: review of the density-import revision (pull request #77)

**Reviewed commit:** `930f817e1a38a7c921fc13ce499df688b7bab8c2` (Lemma 5.36, Imported Theorem 5.37, Theorem 5.38: main theorem without finiteness).
**Review posted:** 2026-09-14T04:55:34Z, one review with four inline comments. Reproduced verbatim.

## Finding 18 (P1) — `PSC_balanced_pair_state_2026-09-13.tex`, line 767

> **Repair the claimed nesting of the good sets**
>
> With `G_m` defined as a union of individual tile interiors, `G_m \subseteq G_{m+1}` is generally false: if a common tile inflates to two or more common tiles, every new internal subdivision boundary belongs to the rescaled parent interior in `G_m` but to no child interior in `G_{m+1}`. This also leaves the proof of Lemma 5.36 without its stated justification for choosing the witnessing level `m >= N`. The argument can likely be repaired by treating boundary points separately and proving that every tail union is dense, but the current pointwise nesting claim and proof are not valid as written.

## Finding 19 (P2) — `docs/overlap-finiteness-and-coincidence-density-2026-09-13.md`, line 273

> **Finish propagating the resolved bridge status through the notes**
>
> Although this heading now declares the bridge resolved, lines 283–295 still call the Sirvent–Solomyak coverage transfer the remaining step and list density bridge as Open Problem 5.36, while the Section 7 introduction repeats that reduction. The same stale conclusion remains in `docs/seed-patch-to-literature-overlap-audit-2026-09-13.md` lines 169–173 and the completion program in `docs/claim-status-and-source-map-2026-09-13.md` lines 125–126. These are active status/roadmap documents, so leaving the former bridge marked as an open proof obligation contradicts the status introduced by this commit.

## Finding 20 (P2) — `PSC_balanced_pair_state_2026-09-13.tex`, line 785

> **Remove the opposite conclusion preceding Theorem 5.38**
>
> Immediately before this new theorem, line 765 still says that overlap productivity does not by itself give PDS because the older bridge needs finiteness. That is the exact conclusion Theorem 5.38 now reverses via the imported dense-eventual-coincidence theorem, so the manuscript presents contradictory mathematical status within the same subsection.

## Finding 21 (P3) — `tla/Ledger.tla`, line 181

> **Update the stale open-input description in the TLA ledger**
>
> The new comment records `DensityToPDSBridge` as imported, but the route description at lines 162–170 still explicitly calls it the separate open input for the G1-free route. This contradicts both `ProvedDef` and the reduced `OverlapGateAssumed`, making the ledger's explanatory dependency documentation disagree with the model it describes.

No other findings were posted in the ninth round.

---

# Tenth round: re-review of the round-nine revision (pull request #77)

**Reviewed commit:** `5a876aec40fce9b3f980b4ea651438fb4b7f591a`.
**Review posted:** 2026-09-14T05:05:14Z, one review with two inline comments. Reproduced verbatim.

## Finding 22 (P2) — `docs/overlap-finiteness-and-coincidence-density-2026-09-13.md`, line 343

> **Apply the good-set correction to the companion note**
>
> Although the manuscript was corrected, this newly added companion proof still calls the sets `G_m(s)` increasing. A common tile's internal subdivision points belong to its rescaled interior at level `m` but to no child interior at level `m+1`, so this assertion is false; consequently, lines 351–354 still cannot assume that the arbitrary witnessing level is at least the overlap level `N`. Replace the nesting assertion and abridged proof with the manuscript's finite-difference argument so this active proof note actually supports Lemma 5.36.

## Finding 23 (P2) — `scripts/oa_failures_probe.py`, line 36

> **Compute a valid overlap-enumeration window**
>
> For inputs where tile lengths have a sufficiently large ratio, `14 + k` violates `oa_types`' documented requirement that `window` exceed `(g(W) + l_max) / l_min`. For example, the corpus substitution `{1:(2,), 2:(3,), 3:(1,3,3)}` at `k=24` needs a bound of about 86.6 while this passes 38. The enumeration may therefore omit valid level-zero overlap types and falsely report `first_inclusion_(q,c,k)` or `union_all_productive`; derive and verify the geometric bound instead of using this heuristic without failing closed.
>
> AGENTS.md reference: AGENTS.md:L31-L32

No other findings were posted in the tenth round.

---

# Eleventh round: automated review of the exact-window restatement (pull request #79)

**Reviewed commit:** `90663fb3af9c1f87f8cea7c5040e4afc90d75ecd`.
**Review posted:** 2026-09-14T17:34:10Z. Reproduced verbatim.

> Codex Review: Didn't find any major issues. :rocket:

The automated Codex review of the substantive exact-window restatement posted no findings.

---

# Twelfth round: review of the strong-coincidence revision (pull request #82)

**Reviewed commit:** `68a392abcbccb0a874e7b090718a6d9233dab2af` (Propositions 5.39–5.40, Corollary 5.41, depth census).
**Review posted:** 2026-09-14T21:58:22Z, one automated Codex review with two inline comments. Reproduced verbatim.

## Finding 24 (P2) — `PSC_balanced_pair_state_2026-09-13.tex`, line 810

> **Match the ordered-pair claim to the graph's seed orientation**
>
> This is not true for every ordered `i≠j` in the canonical graph being censused: `_seed_states_with_cache` constructs only the `a<b` presentation, while overlap states are oriented and are not normalized under swapping top and bottom. For the tested substitution `1→2, 2→132, 3→112`, the exact graph contains `(2,3,0)` but not `(3,2,0)`, contradicting this sentence when `i=3,j=2`. One canonical orientation per unordered pair is sufficient for the strong-coincidence consequence, but the proposition and depth API must either restrict to that orientation, normalize overlap states, or seed both presentations.
>
> AGENTS.md reference: AGENTS.md:L49-L55

## Finding 25 (P2) — `PSC_balanced_pair_state_2026-09-13.tex`, line 816

> **Exclude the bottom right endpoint from boundary coincidences**
>
> When the bottom tile's right endpoint lands on an internal top boundary, (b) is true as written, but no bottom subtile starts there, so (c) is false and the proof's strict inequality for the bottom tile fails. For the PIP substitution `1→2, 2→3, 3→12`, the overlap graph contains `O=(3,3,-1)`; at level 1, `x=1` is an internal top boundary and the bottom right endpoint, whereas `P_1(3)={0,e_1}`, `w=-e_1`, and `Mw=-e_2` is not in `P_1(3)-P_1(3)`. Thus the code's `first_left_aligned_depths` measures common boundaries that are proper on both sides, while the manuscript, propagated docs, and TLA ledger assert the broader false equivalence; (b) should exclude the right endpoints of both inflated tiles.
>
> AGENTS.md reference: AGENTS.md:L55-L55

No other findings were posted in the twelfth round.

---

# Thirteenth round: re-review of the round-twelve revision (pull request #82)

**Reviewed commit:** `310f06c06bdf757745cdb9c19f4e0411d20a9cd5`.
**Review posted:** 2026-09-14T22:06:17Z, one automated Codex review with one inline comment. Reproduced verbatim.

## Finding 26 (P2) — `src/psc_research/overlap_graph.py`, line 240

> **Reject capped graphs before computing target depths**
>
> When `OverlapGraph` reaches `max_states`, `_build()` leaves a partial graph whose adjacency lists are empty, but this helper still computes apparently meaningful depths. For example, `OverlapGraph(TAU, max_states=1)` is capped while `first_left_aligned_depths` returns `[0]` and `strong_coincidence_depths` reports `{(1, 2): -1}`, potentially misclassifying an inconclusive truncation as mathematical evidence. Add the same capped-graph rejection used by the canonical Mojo `_first_depths` and `nonproductive()`.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the thirteenth round.

---

# Fourteenth round: re-review of the round-thirteen revision (pull request #82)

**Reviewed commit:** `3dc397856ab8ceaf0298c34c3e1df8855e612f10`.
**Review posted:** 2026-09-14T22:20:51Z, one automated Codex review with two inline comments. Reproduced verbatim.

## Finding 27 (P2) — `mojo/swap_overlap_census.mojo`, line 102

> **Record nonproductive graphs before validating depths**
>
> When a graph contains any nonproductive state, its coincidence depth is `-1`; its left-aligned depth is either also `-1` (triggering the first clause here) or nonnegative (triggering `left[d] > depths[d]`). Thus every nonproductive specimen throws before the counters at lines 126–129 are updated, causing a mathematical counterexample to be reported only as `FAILED` while the advertised nonproductive count remains zero. Record `bad` before these validations or omit the depth histograms for nonproductive graphs.

## Finding 28 (P2) — `mojo/swap_overlap_census.mojo`, line 112

> **Reuse the already-computed coincidence depths**
>
> On every specimen, each of these calls invokes `first_coincidence_depths`, rebuilding the reverse adjacency and running another full BFS even though line 88 already computed the same depth vector. Across the reported 1,118,850 vertices this performs the coincidence traversal three times per graph; pass the existing depths into the endpoint scan or compute both prefix and suffix maxima together.
>
> AGENTS.md reference: AGENTS.md:L30-L30

No other findings were posted in the fourteenth round.

---

# Fifteenth round: re-review of the round-fourteen revision (pull request #82)

**Reviewed commit:** `2288163613668619be3185e97b1474ca059f3dc2`.
**Review posted:** 2026-09-14T22:27:01Z, one automated Codex review with two inline comments. Reproduced verbatim.

## Finding 29 (P2) — `mojo/psc/overlap_seed_patch.mojo`, line 384

> **Reject capped automata in the reused-depth helper**
>
> When the newly added reuse API is called directly with a capped `SeedOverlapAutomaton` and any vector matching the truncated state count, this length check passes and the helper returns an apparently valid strong-coincidence depth from a partial graph. Unlike `strong_coincidence_depth`, this path bypasses `_first_depths` and its cap guard, so the inconclusive construction can be misclassified as mathematical evidence; check `a.capped` before consuming the supplied depths. This new Mojo `_from` overload is the fresh path not covered by the addressed Python cap fix.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 30 (P2) — `mojo/swap_overlap_census.mojo`, line 118

> **Reuse substitution tables across graph and depth scans**
>
> In the checked `swap_overlap_census.mojo` path, every PIP specimen already calls `build_seed_overlap_graph` at line 78, which internally calls `build_seed_overlap_tables`; this added line rebuilds the exact Perron field, tile lengths, and prefix positions for the same `sigma` solely for the endpoint scan. That repeats substitution-local exact setup across all 4,554 specimens despite the repository's explicit once-per-specimen rule; build the tables once and pass them into graph construction and the strong-coincidence scans.
>
> AGENTS.md reference: AGENTS.md:L26-L26

No other findings were posted in the fifteenth round.

---

# Sixteenth round: review of the contracting-bound revision (pull request #87)

**Reviewed commit:** `3b8e6d42acfac4c1d9c23abe6f5190e6656e0ce8` (Proposition 5.42 and the census against the first left-aligned depth).
**Review posted:** 2026-09-15T00:23:22Z, one automated Codex review with three inline comments. Reproduced verbatim.

## Finding 31 (P1) — `src/psc_research/overlap_contracting.py`, line 149

> **Add the canonical Mojo contracting-bound implementation**
>
> This class is the new exact kernel supporting Proposition 5.42 and the reported 1,118,850-vertex census, but a repo-wide search finds no corresponding contracting-bound implementation or regression under `mojo/`, nor any documented blocker. Consequently the manuscript's new numerical result depends solely on the secondary Python layer, contrary to the repository's explicit requirement that new theorem-support algorithms and census drivers land in Mojo first.
>
> AGENTS.md reference: AGENTS.md:L5-L16

## Finding 32 (P1) — `docs/overlap-finiteness-and-coincidence-density-2026-09-13.md`, line 531

> **Avoid attributing the residual depth to combinatorics**
>
> The census establishes only `b >= m_0`, where `m_0` comes from triangle and Cauchy–Schwarz upper bounds; therefore `b-m_0` also includes all slack in those inequalities and does not isolate a scale-free combinatorial contribution. A sharper contracting-space argument using actual digit correlations, joint embeddings, or cancellation could still explain the residual, so neither "dominated by" nor "cannot come from a contraction argument" follows from the executable result. State only that this particular magnitude bound leaves an unexplained gap.
>
> AGENTS.md reference: AGENTS.md:L64-L70

## Finding 33 (P1) — `PSC_balanced_pair_state_2026-09-13.tex`, line 852

> **Define the complex-pair formula at zero**
>
> The set `F` necessarily contains zero (for example, choose the first subtile on both sides, so `p=q=0`), and the overlap graph also contains offset-zero vertices, but this display forms both `N(c)/c` and `N(t)/t`; these are undefined in precisely those cases. The Python implementation silently repairs the discrepancy by removing zero digits and returning `m_0(0)=0`, so the stated theorem is not the theorem used by the census. Restrict the maximum to `F \setminus {0}`, state the complex formula only for `t != 0`, and define `m_0(0)=0` separately.
>
> AGENTS.md reference: AGENTS.md:L64-L70

No other findings were posted in the sixteenth round.

---

# Seventeenth round: review of the canonical-implementation revision (pull request #87)

**Reviewed commit:** `7d74aa42c3ce138afe85b332b4964e30f58dacd2` (canonical Mojo contracting bound, zero case, wording).
**Review posted:** 2026-09-15T00:53:39Z, one automated Codex review with two inline comments. Reproduced verbatim.

## Finding 34 (P1) — `mojo/psc/real_root_sign.mojo`, line 29

> **Centralize the new Horner helper in exact.mojo**
>
> This newly introduced polynomial evaluator is a PSC-specific Horner helper over the vendored rational type, but the repository's exact-arithmetic authority requires such helpers to live in `mojo/psc/exact.mojo` and nowhere else. Keeping another implementation in `real_root_sign.mojo` splits the rejection/adapter conventions across modules; move this helper into the designated adapter and import it here.
>
> AGENTS.md reference: AGENTS.md:L44-L48

## Finding 35 (P1) — `mojo/psc/overlap_contracting.mojo`, line 249

> **Test the inequality that actually defines m0**
>
> For complex-pair inputs, this returns the least level satisfying the Cauchy–Schwarz relaxation, not `m_0` as defined in Proposition 5.42 by the original triangle-inequality bound: `(sum r^s)^2 <= m sum r^(2s)` is one-way, so passing this larger RHS does not imply that the defining inequality holds. For example, for `1→2, 2→33, 3→213`, the reachable Mojo-scaled shift `CubicElt(-16, -4, 5)` returns 5 here, while the original inequality first holds at level 6 (at level 5 the normalized left side is about 37.1156, versus 36.8236 for the original RHS and 37.1173 for this relaxed RHS). Thus the reported histograms are not a census of the manuscript's stated `m_0`; either compute the defining inequality or redefine and consistently relabel the weaker bound.
>
> AGENTS.md reference: AGENTS.md:L64-L70

No other findings were posted in the seventeenth round.

---

# Eighteenth round: review of the exact-test revision (pull request #87)

**Reviewed commit:** `0b989e0ccc07d5690d5413e16fc8fe07484dd590` (exact complex-pair test, Horner helper in `exact.mojo`).
**Review posted:** 2026-09-15T01:22:33Z, one automated Codex review with one inline comment. Reproduced verbatim.

## Finding 36 (P2) — `PSC_balanced_pair_state_2026-09-13.tex`, line 850

> **Describe B_m as nonnegative**
>
> For the allowed case `m = 1`, the defining sum for `B_m` runs from `j = 1` to `m - 1` and is empty, so `B_1 = 0`; thus the statement that both `A_m` and `B_m` are positive is false. The proof correctly uses only `rho^{1/2} B_m >= 0`, so describe `B_m` as nonnegative (or qualify strict positivity by `m >= 2`) to make the proposition accurate.

No other findings were posted in the eighteenth round.

---

# Nineteenth round: review of the nonnegativity revision (pull request #87)

**Reviewed commit:** `059c4c5536cc4f0f9252a55a628ca90e7ea0bdf4` (finding 36 and the merge of `main`).
**Review posted:** 2026-09-15T01:31:48Z, one automated Codex review with one inline comment. Reproduced verbatim.

## Finding 37 (P1) — `mojo/psc/overlap_contracting.mojo`, line 269

> **Precompute level terms before scanning offsets**
>
> In the checked `mojo/overlap_contracting_census.mojo` path, every uncached shift calls `least_level`, but this line rebuilds the `A_m`/`B_m` tables from exact field operations for every attempted level and shift even though they depend only on the substitution and `max_level`; the real-conjugate branch similarly rebuilds `G` and the beta powers per shift. Across the 1,118,850-vertex census this causes substantial repeated allocation and exact arithmetic, so precompute both sets of level tables once in the constructor and index them here.
>
> AGENTS.md reference: AGENTS.md:L26-L27

No other findings were posted in the nineteenth round.

---

# Twentieth round: review of the level-table revision (pull request #87)

**Reviewed commit:** `eb0615f609` (finding 37).
**Review posted:** 2026-09-15T02:04:58Z. The automated Codex review of commit `eb0615f` posted no findings ("Didn't find any major issues").

---

# Twenty-first round: review of the obstruction normal form (pull request #92)

**Reviewed commit:** `e61628428e` (Propositions 5.43–5.44, Lemma 5.45).
**Review posted:** 2026-09-15T12:34:32Z, one automated Codex review with one inline comment. Reproduced verbatim.

## Finding 38 (P2) — `PSC_balanced_pair_state_2026-09-13.tex`, line 883

> **Do not call forward-invariant pair sets unions of cycles**
>
> Closure under the first-/last-letter self-map does not imply that every element lies on a cycle: a finite self-map may have preperiodic pairs feeding into a cycle, and the preceding argument establishes neither injectivity nor surjectivity on `A_+(S)` or `A_-(S)`. The supported conclusion is only that every pair eventually enters a cycle (and therefore that each nonempty aligned-pair set contains a cycle); as written, Proposition 5.44 asserts a stronger, unproved structural property.

No other findings were posted in the twenty-first round.

---

# Twenty-second round: review of the forward-invariance revision (pull request #92)

**Reviewed commit:** `4e68dcdc7d` (finding 38).
**Review posted:** 2026-09-15T12:38:40Z. The automated Codex review of commit `4e68dcd` posted no findings ("Didn't find any major issues").

---

# Twenty-third round: review of the manuscript-source guard (pull request #92)

**Reviewed commit:** `d2adbb9b97` (guard against byte-mangled manuscript sources).
**Review posted:** 2026-09-15T15:32:16Z, one automated Codex review with two inline comments. Reproduced verbatim.

## Finding 39 (P2) — `scripts/check_manuscript_source.py`, line 45

> **Reject PDFs truncated after their header**
>
> When a PDF is truncated or corrupted anywhere after its first five bytes while retaining `%PDF-`—even a file containing only those five bytes—`check_pdf` returns success, so the provenance section of `verify_all.sh` reports the artifact as intact despite the docstring promising that truncated files never pass. Validate at least the complete PDF trailer/xref structure, or invoke a parser, before accepting the file.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 40 (P2) — `scripts/check_manuscript_source.py`, line 50

> **Require the expected manuscript inventory**
>
> When a canonical `.tex` or `.pdf` is deleted or renamed, this enumerates only artifacts that still exist and never compares them with an expected inventory; an empty directory even exits successfully with `0 files checked`. Consequently the fail-closed provenance check cannot distinguish intact sources from missing sources, so it should require the known manuscript files (or a checked-in manifest) before reporting success.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the twenty-third round.

