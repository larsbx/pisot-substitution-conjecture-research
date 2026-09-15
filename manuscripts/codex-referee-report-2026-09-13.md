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



---

# Twenty-fourth round: review of the hardened guard (pull request #95)

**Reviewed commit:** `be9dfc3abf` (findings 39–40, rebased onto `main`).
**Review posted:** 2026-09-15T15:38:04Z, one automated Codex review with two inline comments. Reproduced verbatim.

## Finding 41 (P2) — `manuscripts/MANIFEST`, line 1

> **Include every tracked manuscript source in the manifest**
>
> Add `PSC_PROOF_next_source_audit.tex` to this inventory. It is a tracked 745-line manuscript described in `docs/source-provenance-v16-later-audit-2026-09-12.md` as the new manuscript, but deleting it still makes this guard exit successfully because only manifest entries are required and only files that remain are inspected. This leaves the missing-source failure mode that the manifest is intended to close.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 42 (P2) — `scripts/check_manuscript_source.py`, line 63

> **Verify that an object is an XRef stream**
>
> When a corrupted in-range `startxref` happens to point at any ordinary indirect object, this branch accepts the PDF because it checks only the generic `N N obj` header. For example, rewriting the repository PDF's offset to its ordinary `/Producer` object at byte 523231 makes `check_pdf` return no problems even though the pointer no longer identifies a cross-reference section. Require the referenced object's dictionary to identify a cross-reference stream (such as `/Type /XRef`) rather than accepting every object.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the twenty-fourth round.


---

# Twenty-fifth round: review of the manifest and XRef revision (pull request #95)

**Reviewed commit:** `ea83b495c5` (findings 41–42).
**Review posted:** 2026-09-15T15:43:06Z, one automated Codex review with two inline comments. Reproduced verbatim.

## Finding 43 (P2) — `scripts/check_manuscript_source.py`, line 55

> **Select the startxref preceding the final EOF**
>
> When an incrementally updated PDF has multiple trailers within the last 1024 bytes, `re.search` selects the first matching `startxref ... %%EOF`, not the trailer preceding the final EOF. If the newest trailer contains a corrupt offset while the prior trailer remains in the window, the guard validates the old offset and returns success. Fresh evidence beyond finding 39 is that a tail containing a valid `startxref 9` followed by a final `startxref 999999` produces no problems; select and validate the last trailer instead.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 44 (P2) — `scripts/check_manuscript_source.py`, line 68

> **Require an actual stream in XRef objects**
>
> When a cross-reference stream loses its `stream` keyword and data while retaining the object dictionary and final trailer, this branch treats the entire 4096-byte window as the dictionary and accepts `/Type /XRef`; it never requires an actual stream body. Consequently a malformed file containing only an XRef-typed object and `startxref`/`%%EOF` returns success. Fresh evidence beyond finding 42 is this type-only-object path; validate the stream structure rather than only its type marker.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the twenty-fifth round.


---

# Twenty-sixth round: review of the trailer revision (pull request #95)

**Reviewed commit:** `c6032e3dad` (findings 43–44).
**Review posted:** 2026-09-15T15:48:39Z, one automated Codex review with two inline comments. Reproduced verbatim.

## Finding 45 (P2) — `scripts/check_manuscript_source.py`, line 70

> **Validate the classic cross-reference table contents**
>
> When the final trailer uses a classic table, this accepts any bytes beginning with `xref` as long as the word `trailer` occurs later; for example, `%PDF-1.4\nxref\ntrailer\nstartxref\n9\n%%EOF\n` returns success despite containing no cross-reference subsection or trailer dictionary. Fresh evidence beyond finding 44 is this entryless classic-table path, so validate the table and trailer structure before reporting the PDF intact.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 46 (P2) — `scripts/check_manuscript_source.py`, line 74

> **Validate data in the XRef stream body**
>
> When an XRef object contains the literal pair `stream\nendstream` but no stream data, this condition passes and the function returns success; it also accepts a corrupted Flate payload because neither `/Length` nor decoding is checked. Fresh evidence beyond finding 44 is that an empty `/Type /XRef` stream, or a one-byte mutation in the repository PDF's compressed XRef payload that makes zlib reject it, still produces no problems, so validate the stream payload rather than only its delimiter tokens.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the twenty-sixth round.


---

# Twenty-seventh round: review of the structural parser (pull request #95)

**Reviewed commit:** `3a9d53ee10` (findings 45–46 and the test fixtures).
**Review posted:** 2026-09-15T15:56:08Z, one automated Codex review with three inline comments. Reproduced verbatim.

## Finding 47 (P2) — `scripts/check_manuscript_source.py`, line 118

> **Reject indirect references for direct /Length**
>
> Fresh evidence beyond finding 46 is that `/Length 4 0 R` is accepted as the direct length `4`: the `\s*` can backtrack to zero, leaving whitespace where the negative lookahead expects a digit. An XRef stream with a four-byte body therefore passes even though its declared length is an unresolved indirect reference, defeating the promised fail-closed direct-length check; parse the complete value token or explicitly reject a following generation/reference pair.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 48 (P2) — `scripts/check_manuscript_source.py`, line 140

> **Enforce the XRef stream's declared row count**
>
> Fresh evidence beyond finding 46 is that, without `/Index`, `/Size 100 /W [1 2 1] /Length 4` and a single four-byte row passes this check. A stream without `/Index` must contain `/Size` rows, while one with `/Index` must contain the sum of its subsection counts; checking only divisibility therefore misses payloads truncated by one or more complete rows.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 49 (P2) — `scripts/check_manuscript_source.py`, line 129

> **Handle filter arrays before validating payload bytes**
>
> Fresh evidence beyond finding 46 is an XRef stream using the valid array form `/Filter [/FlateDecode]`: this search finds no filter and validates the compressed bytes as though they were the decoded payload. If their byte count happens to be a multiple of the row width, even a corrupted compressed stream passes; otherwise an intact PDF is rejected. Parse supported filter arrays, or fail whenever a `/Filter` key is present in an unrecognized form.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the twenty-seventh round.


---

# Twenty-eighth round: review of the length, row-count and filter revision (pull request #95)

**Reviewed commit:** `a9242e36aa` (findings 47–49).
**Review posted:** 2026-09-15T16:16:23Z, one automated Codex review with four inline comments. Reproduced verbatim.

## Finding 50 (P2) — `scripts/check_manuscript_source.py`, line 136

> **Require the XRef indirect object to terminate**
>
> When a PDF is truncated immediately after `endstream`, the body, row count, and trailer checks all succeed because nothing requires the XRef stream's indirect object to end with `endobj`. Such a truncated object is syntactically incomplete but `check_pdf` returns success, so validate the delimiter following `endstream` before accepting the stream.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 51 (P2) — `scripts/check_manuscript_source.py`, line 127

> **Reject invalid /Index ranges**
>
> Fresh evidence beyond finding 48 is that `/Size 1 /Index [999 1]` with one decoded row passes: only the count fields are summed, while the starting object numbers are ignored. Odd-length arrays such as `[0 1 2]` also pass because the unmatched value is silently discarded. Require complete start/count pairs whose ranges fit within `/Size` before using their counts.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 52 (P2) — `scripts/check_manuscript_source.py`, line 112

> **Require exactly three fields in /W**
>
> When an XRef stream declares `/W [4]`, this code treats it as a four-byte row width and accepts a matching one-row payload, even though `/W` must be an array of exactly three nonnegative integers describing the entry type, offset, and generation/index fields. Validate the array cardinality rather than accepting any nonempty list whose sum is positive.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 53 (P2) — `scripts/check_manuscript_source.py`, line 81

> **Validate in-use classic xref offsets**
>
> For PDFs using a classic xref table, changing an in-use entry from offset `0000000009` to `0000000008` or even `9999999999` still passes because entries are checked only for their textual shape. The resulting entry no longer identifies its declared indirect object, so a byte-mangled cross-reference table is reported as intact; validate each `n` entry against the file bounds and the object number/generation at its referenced offset.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the twenty-eighth round.


---

# Twenty-ninth round: review of the endobj, index, arity and entry revision (pull request #95)

**Reviewed commit:** `9256ace9d9` (findings 50–53).
**Review posted:** 2026-09-15T16:22:36Z, one automated Codex review with two inline comments. Reproduced verbatim.

## Finding 54 (P2) — `scripts/check_manuscript_source.py`, line 100

> **Enforce classic subsection ranges against /Size**
>
> The trailer check only requires `/Size` to be present, so the minimal classic fixture still passes after changing `/Size 2` to `/Size 1`, even though its `0 2` subsection contains object 1 and therefore exceeds the declared object-number space. This allows a mangled `/Size` value to be reported as intact; parse the value and reject any subsection whose `start + count` exceeds it.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 55 (P2) — `scripts/check_manuscript_source.py`, line 174

> **Validate XRef stream entry contents**
>
> Fresh evidence beyond finding 53 is that only classic-table entries are dereferenced: an uncompressed stream with `/Size 2 /Index [1 1] /W [1 2 1]` and the row `01 ff ff 00` passes because its row count is correct, even though the type-1 entry for object 1 points beyond the file instead of at the XRef object's header. Decode each row according to `/W` and reject invalid entry types or type-1 offsets that do not identify the declared object, as is already done for classic entries.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the twenty-ninth round.


---

# Thirtieth round: review of the subsection-range and row-decoding revision (pull request #95)

**Reviewed commit:** `f158aab509` (findings 54–55).
**Review posted:** 2026-09-15T16:30:06Z, one automated Codex review with three inline comments. Reproduced verbatim.

## Finding 56 (P2) — `scripts/check_manuscript_source.py`, line 105

> **Validate classic trailer `/Prev` chains**
>
> When a classic trailer belongs to an incrementally updated PDF, this returns success without inspecting `/Prev`; adding `/Prev 999999` to the otherwise valid classic fixture still passes even though the earlier cross-reference section is unreachable. Follow each `/Prev` offset, reject out-of-range or cyclic links, and validate every referenced section before accepting the PDF.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 57 (P2) — `scripts/check_manuscript_source.py`, line 151

> **Dereference in-range type-2 object-stream targets**
>
> Fresh evidence beyond finding 55 is that a type-2 row is accepted whenever its second field is numerically below `/Size`: a standalone `/Size 2 /Index [1 1]` stream whose object-1 row points to object stream 1 passes, although object 1 is the XRef object itself and no `/Type /ObjStm` exists. Resolve the named container through the cross-reference data, require it to be an object stream, and validate the third-field index rather than checking only the number bound.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 58 (P2) — `scripts/check_manuscript_source.py`, line 180

> **Reject inconsistent PNG predictor parameters**
>
> When a Flate stream's decode parameters are mangled, this treats every `/Predictor` value greater than or equal to 10 identically and ignores `/Columns`, `/Colors`, and `/BitsPerComponent`; for example, the one-row fixture still passes with `/Predictor 99` or `/Predictor 12 /Columns 999`. Validate the supported predictor range and require the declared decode geometry to match the `/W` row width before undoing prediction, otherwise corrupted stream dictionaries are reported as intact.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the thirtieth round.
\n


---

# Thirty-first round: review of the full-parse revision (pull request #95)

**Reviewed commit:** `22716cd7a0` (findings 56–58).
**Review posted:** 2026-09-15T16:41:20Z, one automated Codex review with two inline comments. Reproduced verbatim.

## Finding 59 (P2) — `scripts/check_manuscript_source.py`, line 266

> **Reject an inflated trailer size**
>
> When `/Size` is increased without changing the cross-reference rows, this condition accepts the file because it only rejects `seen >= size`. For example, changing the repository XRef stream from `/Size 1133` to `/Size 9999` while retaining `/Index [0 1133]` leaves its length, offsets, and decoded rows intact, passes the structural upper-bound check, and leaves `seen < size`, even though `/Size` no longer equals one greater than the highest object number. Fresh evidence beyond finding 54 is this oversized rather than undersized `/Size` path; validate the exact object-number extent across the cross-reference chain.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 60 (P2) — `scripts/check_manuscript_source.py`, line 257

> **Decode ordinary streams while dereferencing objects**
>
> When an ordinary encoded stream is corrupted, `get_object` only constructs the stream object and retains its encoded bytes; pypdf does not apply `/Filter` decoding until `get_data()` is called. Consequently, flipping a byte in a non-object-stream `/FlateDecode` payload such as object 177 in the repository PDF leaves all offsets and lengths unchanged, and this loop plus `len(reader.pages)` can still report success. Decode every encountered stream so malformed content, font, and image payloads fail the claimed full-file integrity check.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the thirty-first round.


---

# Thirty-second round: review of the exact-extent and stream-decoding revision (pull request #95)

**Reviewed commit:** `7d557ac9f8` (findings 59–60).
**Review posted:** 2026-09-15T16:48:33Z, one automated Codex review with one inline comment. Reproduced verbatim.

## Finding 61 (P2) — `scripts/check_manuscript_source.py`, line 285

> **Include free entries when validating /Size**
>
> For a valid PDF whose highest-numbered cross-reference entry is free, `reader.xref`/`xref_objStm` contains only dereferenceable type-1/type-2 objects, so `top` is lower than `/Size - 1` and this check rejects the file. For example, a classic table with objects 1–3 in use, object 4 free, and `/Size 5` has the required exact extent but is reported inconsistent. Derive the maximum from all cross-reference entries, including type-0/free entries, while still rejecting a `/Size` that merely has no corresponding entry.

No other findings were posted in the thirty-second round.


---

# Thirty-third round: review of the chain-extent revision (pull request #95)

**Reviewed commit:** `7ec39a90c0` (finding 61).
**Review posted:** 2026-09-15T16:57:25Z, one automated Codex review with two inline comments. Reproduced verbatim.

## Finding 62 (P2) — `scripts/check_manuscript_source.py`, line 94

> **Validate classic xref free entries**
>
> When an `f` entry is corrupted, this branch validates only its textual shape and skips its free-list pointer and generation fields; the full-parse stage cannot recover this because pypdf does not retain free entries. For example, changing object 0's pointer from `0000000000` to the out-of-range `9999999999` leaves the extent unchanged and is reported as intact, despite producing an invalid cross-reference free list. Validate free-entry bounds and required free-list invariants before accepting the table.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 63 (P2) — `scripts/check_manuscript_source.py`, line 85

> **Reject empty classic xref subsections**
>
> A zero-count subsection contributes no cross-reference entries, but it is still added to `ranges` and the return expression treats `start - 1` as an actual object number. Thus an otherwise valid four-entry table can append `9999 0` and declare `/Size 9999`; the structural walk reports object 9998 as present, and the later exact-size comparison succeeds even though no such entry exists. Reject zero counts or exclude them from the computed extent.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the thirty-third round.


---

# Thirty-fourth round: review of the free-list revision (pull request #95)

**Reviewed commit:** `30d16e00e8` (findings 62–63).
**Review posted:** 2026-09-15T17:04:50Z, one automated Codex review with two inline comments. Reproduced verbatim.

## Finding 64 (P2) — `scripts/check_manuscript_source.py`, line 278

> **Permit unlinked free entries in xref streams**
>
> When a valid cross-reference stream does not maintain the optional free-object linked list, its type-0 entries may use `0` as the next-free field. With more than one free object, this code rejects the file because only object 0 is walked and every other free entry is classified as stray; for example, appending a free object 5 with fields `(0, 0, 0)` to the existing `xref_pdf` fixture makes `_xref_chain` return `free entries [5] are not on the free list`. Track whether entries came from a classic table and enforce full-list coverage only where the list is required.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 65 (P2) — `scripts/check_manuscript_source.py`, line 170

> **Preserve the encoded xref generation value**
>
> When the third `/W` field is one byte wide, an encoded value of `255` means generation 255, not a saturated representation of 65535. This conversion therefore lets a malformed object-0 entry pass the required-generation check; the default `xref_pdf` fixture itself encodes `ff` in a one-byte field and `_xref_chain` accepts it as generation 65535. Keep the decoded integer unchanged and encode 65535 using a sufficiently wide field in fixtures.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the thirty-fourth round.


---

# Thirty-fifth round: review of the provenance revision (pull request #95)

**Reviewed commit:** `99cc3be753` (findings 64–65).
**Review posted:** 2026-09-15T17:14:04Z, one automated Codex review with three inline comments. Reproduced verbatim.

## Finding 66 (P2) — `scripts/check_manuscript_source.py`, line 281

> **Validate classic free lists before stream entries supersede them**
>
> Fresh evidence beyond finding 64 is a mixed incremental chain: when a newer cross-reference stream replaces object 0 with an unlinked `(0, 0, generation)` row and inherits a free object from the preceding classic table through `/Prev`, that older entry retains `classic=True` and is rejected here even though its classic section's original object-0 entry linked it correctly and stream free-list coverage is optional. Validate the classic list against the effective table at that historical section, rather than applying entry provenance after newer sections have overwritten its head.

## Finding 67 (P2) — `scripts/check_manuscript_source.py`, line 228

> **Bound xref row counts before materializing them**
>
> When a damaged cross-reference stream declares a very large `/Size` without `/Index`, this eagerly constructs that many Python integers before the code reads or compares the actual payload; `/Size 1000000000` can therefore exhaust the verifier process instead of returning a guarded failure. The `/Index` comprehension has the same problem for a huge count. Derive the available row count from the decoded payload first and reject inconsistent declarations before materializing object numbers.

## Finding 68 (P2) — `scripts/check_manuscript_source.py`, line 173

> **Reject oversized generations on in-use stream rows**
>
> Fresh evidence beyond finding 65 is the type-1 path: the 65535 bound is applied only to free rows, so a `/W` field encoding generation 65536 is accepted whenever the target header is also `num 65536 obj`; the subsequent strict parse uses that integer as the object's generation rather than supplying the missing range check. Generation numbers are limited to 65535 for in-use objects as well, so apply the bound before branching on the row type.

No other findings were posted in the thirty-fifth round.


---

# Thirty-sixth round: review of the per-section revision (pull request #95)

**Reviewed commit:** `f89f2b61d7` (findings 66–68).
**Review posted:** 2026-09-15T17:23:51Z, one automated Codex review with three inline comments. Reproduced verbatim.

## Finding 69 (P2) — `scripts/check_manuscript_source.py`, line 248

> **Cap decoded xref rows independently of declarations**
>
> Fresh evidence beyond finding 67 is a compressed payload that actually matches a hostile declaration: `/Size 1000000000` with four billion highly compressible row bytes permits this call to allocate toward the entire attacker-controlled `expected_rows * row` limit, after which line 260 also materializes a billion object numbers. The small-payload regression fails quickly, but a matching compression bomb can still exhaust the provenance runner instead of producing a guarded failure; impose a repository-appropriate absolute row/decoded-byte ceiling before inflation.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 70 (P2) — `scripts/check_manuscript_source.py`, line 128

> **Walk companion /XRefStm sections structurally**
>
> When a classic trailer describes a hybrid-reference PDF, this return retains `/Prev` but discards `/XRefStm`, so the companion cross-reference stream never reaches `_xref_stream` or the effective-table checks. The pypdf fallback cannot close that gap because `reader.xref` and `xref_objStm` expose in-use and compressed entries but not type-0/free rows; therefore a malformed free pointer or free-list row in the companion stream can still be accepted. Parse and merge the `/XRefStm` section alongside the classic table.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 71 (P2) — `scripts/check_manuscript_source.py`, line 320

> **Validate /Size for every historical section**
>
> In an incremental PDF, only the final merged extent is compared with the final trailer's `/Size`; each replayed historical section is checked only for its free list. Consequently, an older revision with objects 0–3 and a corrupt `/Size 5` passes if a later revision introduces object 4 and also declares `/Size 5`, because the later entry masks the older trailer's inflated extent. Carry each section's `/Size` into this replay and compare it with that prefix's effective table before applying the next update.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the thirty-sixth round.


---

# Thirty-seventh round: review of the ceiling and hybrid revision (pull request #95)

**Reviewed commit:** `a76630a9ed` (findings 69–71).
**Review posted:** 2026-09-15T17:33:35Z, one automated Codex review with three inline comments. Reproduced verbatim.

## Finding 72 (P2) — `scripts/check_manuscript_source.py`, line 334

> **Check the companion stream's own /Size**
>
> When a hybrid PDF's `/XRefStm` companion has a corrupt `/Size` but an explicit `/Index`, only `companion[0]` is retained here and the companion's size is discarded. For example, changing the companion in `hybrid_pdf()` from `/Size 6` to `/Size 7` leaves `_xref_chain` successful because replay checks only the classic trailer's `/Size 6`; the full-parse comparison likewise reads the final classic trailer. Fresh evidence beyond finding 71 is this companion-section path, so validate the companion's `/Size` against the same effective table before discarding its metadata.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 73 (P2) — `scripts/check_manuscript_source.py`, line 114

> **Bound historical object offsets to their revision**
>
> When an older revision's in-use entry is corrupted to point at a matching object header introduced by a later incremental update, this global-file check accepts it even though that target did not exist in the historical revision. If the newer section also supersedes that object, pypdf exposes only the effective newer entry, so the malformed old offset is never dereferenced and the guard succeeds. Validate an entry against the byte boundary of the revision containing its cross-reference section, not merely against the final file.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 74 (P2) — `scripts/check_manuscript_source.py`, line 256

> **Cap decoded xref bytes, not only row count**
>
> When an XRef stream keeps its row count below 1,000,000 but declares a very large `/W`, this limit remains attacker-controlled: for example, `/Size 1 /W [1 1000000000 1]` permits zlib to produce roughly 1 GB before the guard rejects anything. `MAX_STREAM_BYTES` is applied only during the later full parse, after this inflation. Fresh evidence beyond finding 69 is that the new row ceiling does not bound `expected_rows * row`; impose an absolute decoded-byte ceiling here before calling zlib.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the thirty-seventh round.


---

# Thirty-eighth round: review of the revision-bound revision (pull request #95)

**Reviewed commit:** `273d95fb7d` (findings 72–74).
**Review posted:** 2026-09-15T17:42:51Z, one automated Codex review with two inline comments. Reproduced verbatim.

## Finding 75 (P2) — `scripts/check_manuscript_source.py`, line 402

> **Decode streams from superseded revisions**
>
> When an incremental update replaces a stream at the same object number and generation, pypdf's effective `reader.xref` mapping contains only the newest entry, so this list never includes the historical stream. `_xref_chain` retains no historical object offsets for the full-parse stage, meaning a flipped byte in the superseded Flate body is never passed to `_inflate_strictly` and the corrupted historical revision is reported intact. Fresh evidence beyond finding 60 is this superseded-object path; retain and decode in-use streams from each replayed revision.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 76 (P2) — `scripts/check_manuscript_source.py`, line 324

> **Bound classic entry offsets before the xref section**
>
> When an older classic entry points to a matching `N G obj` sequence embedded in its own trailer, its offset remains below this following `startxref` limit and passes the structural check. If a later revision supersedes that object, pypdf ignores the bogus historical target and the malformed file is accepted. Fresh evidence beyond finding 73 is this same-revision target inside the classic xref/trailer region; classic in-use offsets must precede the xref table itself, not merely the revision's `startxref`.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the thirty-eighth round.


---

# Thirty-ninth round: review of the superseded-stream revision (pull request #95)

**Reviewed commit:** `bb3f62c23f` (findings 75–76).
**Review posted:** 2026-09-15T17:51:10Z, one automated Codex review with three inline comments. Reproduced verbatim.

## Finding 77 (P2) — `scripts/check_manuscript_source.py`, line 350

> **Reject unparsable filters on superseded streams**
>
> When a superseded stream contains a `/Filter` key whose value does not match this regex, such as `/Filter 9 0 R` or a malformed array, `flt` becomes `None` and the stream is treated as unfiltered. Corrupt encoded bytes can therefore pass because pypdf only inspects the effective newer object. Fresh evidence beyond the earlier filter findings is this newly added historical-stream path; fail whenever `/Filter` is present but cannot be parsed as the supported chain.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 78 (P2) — `scripts/check_manuscript_source.py`, line 354

> **Validate decode parameters on superseded streams**
>
> For a superseded `/FlateDecode` stream, this only inflates the raw deflate member and never validates or applies `/DecodeParms`; a zlib-valid stream with `/Predictor 99` or inconsistent `/Columns` therefore passes, while pypdf never opens that historical object. Fresh evidence beyond the earlier predictor finding is the new `_superseded_streams` path, which needs the same decode-parameter validation as effective streams.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 79 (P2) — `scripts/check_manuscript_source.py`, line 348

> **Require superseded stream objects to end with endobj**
>
> When a historical stream is superseded, replacing or deleting its `endobj` token leaves this check successful because it requires only `endstream`; the final pypdf pass reads only the newer effective object. Fresh evidence beyond the earlier XRef-object termination finding is this newly inspected superseded-stream path, which should require `endstream` followed by `endobj` before accepting the historical revision.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the thirty-ninth round.


---

# Fortieth round: review of the superseded-stream discipline revision (pull request #95)

**Reviewed commit:** `7394ee76d2` (findings 77–79).
**Review posted:** 2026-09-15T17:57:59Z, one automated Codex review with three inline comments. Reproduced verbatim.

## Finding 80 (P2) — `scripts/check_manuscript_source.py`, line 347

> **Validate TIFF predictor row geometry**
>
> When a superseded Flate stream declares `/Predictor 2`, this condition skips all checks involving `/Columns`, `/Colors`, and `/BitsPerComponent`; for example, one inflated byte with `/Predictor 2 /Columns 999` is accepted even though it cannot contain a complete TIFF-predicted row. Since pypdf only sees the replacement object, require the inflated length to be a whole number of TIFF rows before accepting the historical stream.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 81 (P2) — `scripts/check_manuscript_source.py`, line 370

> **Reject malformed superseded stream markers**
>
> Fresh evidence beyond finding 76 is that changing the historical object's `stream` keyword to `streaX` makes `body` false and this branch silently treats the malformed object as a non-stream. Because pypdf dereferences only the newer replacement, the corrupted historical revision still passes; structurally validate every superseded object through `endobj` rather than continuing when stream recognition fails.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 82 (P2) — `scripts/check_manuscript_source.py`, line 383

> **Parse the entire superseded filter name**
>
> Fresh evidence beyond finding 77 is that this regex accepts only a prefix of a PDF name: `/Filter /FlateDecode#58` represents the unsupported name `/FlateDecodeX`, but the match stops before `#58`, records `FlateDecode`, and accepts a zlib-valid historical body. As pypdf never parses the superseded object, require a valid name delimiter after the match and handle PDF `#xx` name escapes before comparing the filter chain.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the fortieth round.


---

# Forty-first round: review of the whole-name revision (pull request #95)

**Reviewed commit:** `f427597e50` (findings 80–82).
**Review posted:** 2026-09-15T18:07:43Z, one automated Codex review with three inline comments. Reproduced verbatim.

## Finding 83 (P2) — `scripts/check_manuscript_source.py`, line 212

> **Resolve superseded type-2 cross-reference entries**
>
> When a later revision replaces an object that was type 2 in an older cross-reference stream, this branch only checks that the alleged object-stream number is below `/Size`; `_superseded_streams` skips the old non-type-1 entry and pypdf sees only the effective replacement. Fresh evidence beyond the addressed type-2 finding is that an old object-4 row `(2, 2, 0)` naming an ordinary page-tree object, followed by a classic update supplying object 4 in use, makes `_xref_chain` succeed. Resolve each historical type-2 row against that revision and validate the container type and member index.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 84 (P2) — `scripts/check_manuscript_source.py`, line 366

> **Reject malformed predictor field values**
>
> When a superseded stream has a predictor field with the wrong PDF value type, this helper treats the field as absent and silently substitutes its default; `/Predictor /Bogus` becomes predictor 1, and `/Predictor 2 /Columns -1` becomes one column, so a zlib-valid historical stream passes because pypdf ignores its superseded object. Fresh evidence beyond the addressed decode-parameter finding is this malformed-value path; distinguish an absent key from a present value that is not a whole nonnegative integer.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 85 (P2) — `scripts/check_manuscript_source.py`, line 397

> **Parse superseded non-dictionary object bodies**
>
> When a superseded object is not a dictionary, any bytes containing `endobj` before the next apparent header are accepted without parsing a PDF object; for example, replacing the historical body with `not-a-PDF-object\nendobj` still makes `_xref_chain` succeed, while pypdf reads only the newer replacement. Fresh evidence beyond the addressed malformed-marker finding is that closure alone does not reject an invalid primitive body, so parse exactly one complete historical object before accepting it.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the forty-first round.


---

# Forty-second round: review of the one-object-parse revision (pull request #95)

**Reviewed commit:** `026cdcd882` (findings 83–85).
**Review posted:** 2026-09-15T18:15:08Z, one automated Codex review with three inline comments. Reproduced verbatim.

## Finding 86 (P2) — `scripts/check_manuscript_source.py`, line 400

> **Parse superseded dictionaries structurally**
>
> Fresh evidence beyond finding 84 is that dictionary objects are still considered complete solely by balancing `<<` and `>>`, without parsing their key/value contents. A superseded body such as `<< /Type >>` or `<< garbage >>` therefore passes `_xref_chain`, while pypdf reads only the newer replacement. Parse the dictionary as a PDF object and reject missing values or non-name keys before accepting the historical revision.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 87 (P2) — `scripts/check_manuscript_source.py`, line 498

> **Match type-2 entries to object-stream members**
>
> Fresh evidence beyond finding 83 is that the new check only proves `index < /N`; it never reads `/First` or verifies that the indexed object-stream header names the type-2 entry's object number. In an older revision, changing member header `5 0` to `9 0` while a later classic update supplies object 5 still makes `_xref_chain` succeed, and pypdf ignores the superseded type-2 entry. Parse the historical object stream's header and require the indexed member to be the referenced object.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 88 (P2) — `scripts/check_manuscript_source.py`, line 156

> **Validate historical trailer roots**
>
> When an incremental PDF has a malformed `/Root` in an older trailer, this only checks that the value looks like an indirect reference and never verifies that it is within that revision's `/Size` or resolves to a catalog. For example, changing the first trailer in `superseded_pdf()` to `/Root 9 0 R` leaves `_xref_chain` successful because the latest trailer supplies the valid root that pypdf reads. Resolve each trailer's root against its historical effective table before accepting the revision.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the forty-second round.


---

# Forty-third round: review of the structural-dictionary revision (pull request #95)

**Reviewed commit:** `b4a3799157` (findings 86–88).
**Review posted:** 2026-09-15T18:27:33Z, one automated Codex review with three inline comments. Reproduced verbatim.

## Finding 89 (P2) — `scripts/check_manuscript_source.py`, line 554

> **Parse compressed members before accepting type-2 entries**
>
> Fresh evidence beyond finding 87 is a malformed member body: this check verifies only that the indexed header pair names `num`, without parsing the bytes at that member offset as one complete PDF object bounded by the next member. If an older object stream contains `5 0 not-a-object` and a later revision replaces object 5, `_xref_chain` succeeds; pypdf sees only the replacement and decoding the still-effective container does not parse its unused member. Parse every referenced historical member before accepting the entry.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 90 (P2) — `scripts/check_manuscript_source.py`, line 583

> **Require a top-level /Type on historical catalogs**
>
> Fresh evidence beyond finding 88 is that this regex scans the complete serialized dictionary, including nested values and strings, so `<< /Pages 2 0 R /Foo << /Type /Catalog >> >>` is accepted as a catalog even though its top-level dictionary has no `/Type`. If a later revision replaces that root object with a valid catalog, pypdf reads only the replacement and the malformed historical root passes the guard. Inspect the structurally parsed top-level key/value entries rather than searching the raw dictionary bytes.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 91 (P2) — `scripts/check_manuscript_source.py`, line 612

> **Revalidate inherited type-2 entries after container updates**
>
> When an incremental revision replaces an object-stream container but inherits its members' type-2 rows, `_object_streams` receives only the current section's `entries`, so those inherited rows are never checked against the replacement container in that historical revision. A subsequent revision can replace the member itself, leaving pypdf only the final direct object; a middle revision where inherited object 5 now points to a replacement container whose indexed member is object 9 therefore passes. Revalidate all effective type-2 rows after each merge, or at least every inherited row whose container changed.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the forty-third round.


---

# Forty-fourth round: review of the member-parse revision (pull request #95)

**Reviewed commit:** `b961e70914` (findings 89–91).
**Review posted:** 2026-09-15T18:38:05Z, one automated Codex review with two inline comments. Reproduced verbatim.

## Finding 92 (P2) — `scripts/check_manuscript_source.py`, line 161

> **Read classic trailer keys only from the top level**
>
> Fresh evidence beyond finding 90 is the classic-trailer path: when an older revision contains `<< /Size 4 /Foo << /Root 1 0 R >> >>` but no top-level `/Root`, these searches accept the nested reference and replay validates it as the historical root; a later trailer with a valid top-level root then lets the malformed historical revision pass. Extract `/Size`, `/Root`, `/Prev`, and `/XRefStm` from `_dict_items` instead of scanning the serialized dictionary recursively.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 93 (P2) — `scripts/check_manuscript_source.py`, line 577

> **Reject overlapping object-stream member offsets**
>
> Fresh evidence beyond finding 89 is an object-stream header such as `5 0 6 0`: because the bound is chosen only from strictly greater offsets, both members are parsed against the same body bytes and effective type-2 rows for indices 0 and 1 are accepted. This treats one serialized object as two declared members, so require member offsets to be distinct and ordered before parsing their bounded bodies.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the forty-fourth round.


---

# Forty-fifth round: review of the top-level-keys revision (pull request #95)

**Reviewed commit:** `dff1e3ac05` (findings 92–93).
**Review posted:** 2026-09-15T18:49:33Z, one automated Codex review with three inline comments. Reproduced verbatim.

## Finding 94 (P2) — `scripts/check_manuscript_source.py`, line 504

> **Read superseded stream lengths from top-level items**
>
> Fresh evidence beyond the top-level-key fixes is the superseded-stream path: this regex still scans the serialized dictionary recursively and accepts integer prefixes, so a historical stream with only `<< /Foo << /Length 1 >> >>` or with `/Length 1.5` is treated as having direct length 1. When a later revision replaces that object, pypdf never checks the old stream and the malformed revision passes; obtain `Length` from `_dict_items(d, 0)` and require `_int_value` to succeed.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 95 (P2) — `scripts/check_manuscript_source.py`, line 576

> **Apply predictors before parsing object-stream members**
>
> Fresh evidence beyond the predictor-parameter validation is that `_decode_parms` only validates the inflated bytes and its result is discarded, after which the still predictor-encoded `data` is parsed as the object-stream header and members. For example, a valid Flate object stream using `/Predictor 12` with a PNG filter byte at the start of its row is rejected as not having `/N` integer pairs; TIFF prediction can likewise make the encoded bytes differ from the objects. Undo the declared predictor before applying `/First` and parsing the header and members.

## Finding 96 (P2) — `scripts/check_manuscript_source.py`, line 282

> **Reject overlapping or unordered /Index ranges**
>
> Fresh evidence beyond the earlier `/Index` validation is that each pair is checked only in isolation, so `/Index [0 3 1 1]` passes even though object 1 occurs twice; `_xref_rows` then silently overwrites its first row in the dictionary. Descending ranges are accepted similarly. This lets a malformed cross-reference stream pass the structural walk, so require the ranges to be strictly ordered and non-overlapping before decoding rows.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the forty-fifth round.


---

# Forty-sixth round: review of the predictor and index revision (pull request #95)

**Reviewed commit:** `b084115186` (findings 94–96).
**Review posted:** 2026-09-15T18:59:24Z, one automated Codex review with three inline comments. Reproduced verbatim.

## Finding 97 (P2) — `scripts/check_manuscript_source.py`, line 448

> **Reject duplicate keys while parsing PDF dictionaries**
>
> When a dictionary repeats a key, assigning into `items` silently keeps the last value instead of rejecting the malformed dictionary. This is observable on a superseded stream: an old object containing duplicate `/Length` keys with the same usable value passes `_xref_chain`, while pypdf only parses its replacement and cannot catch the historical duplicate. Detect an already-present decoded key before assignment so every structurally inspected dictionary fails closed.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 98 (P2) — `scripts/check_manuscript_source.py`, line 680

> **Require /Prev to point to an earlier section**
>
> When `/Prev` is greater than the current cross-reference offset, the loop follows it and later reverses the collected sections without validating their physical chronology. A file whose final `startxref` points at section A and whose A trailer points forward to section B therefore passes the structural walk with B treated as the older revision, defeating the premise that each replayed prefix was once a complete file. Reject any non-earlier `/Prev` before following it.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 99 (P2) — `scripts/check_manuscript_source.py`, line 162

> **Reject overlapping classic xref subsections**
>
> When two classic subsections cover the same object number, this assignment silently replaces the first row in `table`. For example, appending a `1 1` subsection duplicating object 1 to the otherwise valid classic fixture makes `_xref_chain` return success, even though a cross-reference section must not contain competing entries for one object. Check each new subsection against the accumulated ranges before decoding it rather than accepting the overwritten table.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the forty-sixth round.


---

# Forty-seventh round: review of the chronology revision (pull request #95)

**Reviewed commit:** `caf7c77d0d` (findings 97–99).
**Review posted:** 2026-09-15T19:09:48Z, one automated Codex review with three inline comments. Reproduced verbatim.

## Finding 100 (P2) — `scripts/check_manuscript_source.py`, line 693

> **Validate the companion stream's /Prev**
>
> When a classic trailer uses `/XRefStm`, this merge discards `companion[2]`, so a `/Prev` in the companion stream can point to itself, forward, or to a non-xref object without reaching the new backwards-link check at line 684. Since pypdf follows the classic trailer's chain, it also does not expose this malformed companion link during the full parse; validate the companion's `/Prev` and its consistency with the classic trailer before discarding it.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 101 (P2) — `scripts/check_manuscript_source.py`, line 602

> **Reject duplicate object-stream member numbers**
>
> When an object stream declares a header such as `5 0 5 13`, both member bodies can parse and the type-2 row for object 5 can select index 0, leaving the duplicate member at index 1 unexamined by `_object_streams`; pypdf likewise dereferences only the indexed member. The guard consequently accepts two declarations of the same compressed object, so require the object numbers in `pairs` to be unique.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 102 (P2) — `scripts/check_manuscript_source.py`, line 667

> **Validate each historical catalog's page tree**
>
> When an older root object is a `/Catalog` whose `/Pages` reference is missing or invalid and a later revision replaces that catalog with a valid one, this type-only check accepts the historical root while the final pypdf pass reads only the replacement's page tree. For example, an old catalog containing `/Pages 9 0 R` followed by an update restoring `/Pages 2 0 R` passes the replay, so resolve and walk `/Pages` against each revision's effective table before treating that historical revision as intact.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the forty-seventh round.


---

# Forty-eighth round: review of the page-tree revision (pull request #95)

**Reviewed commit:** `bddda784b3` (findings 100–102).
**Review posted:** 2026-09-15T19:19:29Z, one automated Codex review with four inline comments. Reproduced verbatim.

## Finding 103 (P2) — `scripts/check_manuscript_source.py`, line 608

> **Match every object-stream member to an xref entry**
>
> When an object stream declares an otherwise valid, uniquely numbered member that has no matching effective type-2 row—for example, a second member numbered 4 while object 4 remains the direct stream container—this check accepts it and `_object_streams` only visits the referenced member. Pypdf likewise enumerates compressed objects from `xref_objStm`, so the hidden member is never dereferenced even though the guard promises to inspect every object; verify the reverse mapping from every header pair to the effective `(container, index)` entry.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 104 (P2) — `scripts/check_manuscript_source.py`, line 743

> **Validate terminators for every historical revision**
>
> When an incremental PDF's older `startxref` or `%%EOF` marker is removed or corrupted, the historical xref section still parses because its end offset is discarded here; replay follows `/Prev` directly, and the final pypdf pass only requires the newest terminator. This accepts a revision that was never a complete PDF despite the replay contract, so require each non-companion section to be followed by a `startxref` pointing back to that section and an `%%EOF` before the next revision.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 105 (P2) — `scripts/check_manuscript_source.py`, line 694

> **Reject a /Parent on the page-tree root**
>
> When a historical root `/Pages` node carries a `/Parent` entry, this condition skips validation because `parent` is `None`; if a later revision replaces that node, pypdf only walks the repaired tree and the malformed historical tree passes. The root of a page tree must not have a parent, so explicitly reject a top-level `/Parent` instead of checking only non-root nodes.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 106 (P2) — `scripts/check_manuscript_source.py`, line 666

> **Reject streams used as historical page-tree dictionaries**
>
> When a superseded historical catalog or page-tree node is a valid stream whose dictionary contains `/Type /Catalog`, `/Pages`, or `/Type /Page[s]`, `_resolve` returns its dictionary items without noticing the following `stream` body. `_superseded_streams` then accepts the stream structurally and pypdf sees only the later replacement, so an invalid stream object is treated as a catalog/page node; require resolved in-use nodes to be dictionary objects followed by `endobj`, not stream objects.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the forty-eighth round.

# Forty-ninth round: review of the member-mapping revision (pull request #95)

**Reviewed commit:** `8df488e563` (findings 103–106).
**Review posted:** 2026-09-15T19:27:51Z, one automated Codex review with three inline comments. Reproduced verbatim.

## Finding 107 (P2) — `scripts/check_manuscript_source.py`, line 644

> **Decode object streams even when no type-2 row references them**
>
> Fresh evidence after the claimed reverse-mapping fix is an introduced `/ObjStm` with no effective type-2 entries at all: the first loop never calls `_objstm`, so its offset is absent from `cache` and this branch silently skips every declared member. For example, changing object 5's row in `objstm_pdf()` from type 2 to a free row leaves the stream header declaring object 5 while `_xref_chain` returns success; pypdf also discovers compressed members from the type-2 table and will not inspect this hidden member. Decode each introduced in-use object stream before performing the reverse check rather than relying on a cache populated by forward references.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 108 (P2) — `scripts/check_manuscript_source.py`, line 884

> **Restrict manifest entries to files that are actually checked**
>
> A manifest entry may escape the manuscript directory, and existence is the only validation applied to that resolved path. For example, after removing the required manuscript PDF, replacing its entry with `../archive/2026-09-08/README_READ_FIRST_2026_09_08.pdf` satisfies both `is_file()` and the required `.pdf` suffix, while `present` contains no PDF and the external file is never passed to `check_pdf`; the integrity command consequently succeeds without checking any manuscript PDF. Reject absolute or parent-traversing entries and run the format check on every required file directly.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 109 (P2) — `scripts/check_manuscript_source.py`, line 765

> **Require a boundary after each historical EOF marker**
>
> Fresh evidence after the revision-terminator fix is that this regex accepts `%%EOFX` as `%%EOF` because it does not require a token or line boundary after the marker. An incremental file built from an older revision ending in `%%EOFX` followed by a valid update therefore makes `_xref_chain` succeed even though that historical revision never had its own valid EOF marker. Require the marker to end at a valid line boundary before accepting the revision.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the forty-ninth round.

# Fiftieth round: review of the unreferenced-object-stream revision (pull request #95)

**Reviewed commit:** `621133b1e3` (findings 107–109).
**Review posted:** 2026-09-15T19:38:09Z, one automated Codex review with one inline comment. Reproduced verbatim.

## Finding 110 (P2) — `scripts/check_manuscript_source.py`, line 190

> **Use the declared pixel width for PNG predictors**
>
> Fresh evidence beyond the prior predictor fix is that PNG Sub, Average, and Paeth prediction use the previous *pixel*, whose byte width is `ceil(Colors × BitsPerComponent / 8)`, but this implementation always uses the immediately preceding byte. With `/Colors 3 /BitsPerComponent 8`, a historical object stream can therefore be crafted to decode as valid header/member bytes only under this incorrect one-byte rule; after a later revision replaces the member, pypdf decodes the surviving stream but never parses that obsolete member, so the malformed historical revision can pass. Pass the declared bytes-per-pixel into `_unpredict` and use `j - bpp` for the left and upper-left samples.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the fiftieth round.

# Fifty-first round: review of the pixel-width revision (pull request #95)

**Reviewed commit:** `998cf89ae0` (finding 110).
**Review posted:** 2026-09-15T19:48:16Z, one automated Codex review with one inline comment. Reproduced verbatim.

## Finding 111 (P2) — `scripts/check_manuscript_source.py`, line 242

> **Include the xref-stream object in /Size validation**
>
> When a cross-reference stream omits its own entry, this regex discards the indirect object's number, so the later `/Size` check considers only decoded rows. For example, an object `99 0 obj` with `/Size 5 /Index [0 3 4 1]` and valid rows for objects 0–2 and 4 makes `_xref_chain` return success even though `/Size` excludes object 99; pypdf can open the stream through `startxref` without adding the unlisted object to `reader.xref`, so the full-parse extent check also misses it. Capture the xref-stream object's number and require the revision's `/Size` and cross-reference entries to account for it.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the fifty-first round.

# Fifty-second round: review of the self-listing revision (pull request #95)

**Reviewed commit:** `98d583269e` (finding 111).
**Review posted:** 2026-09-15T19:55:27Z, one automated Codex review with one inline comment. Reproduced verbatim.

## Finding 112 (P2) — `scripts/check_manuscript_source.py`, line 801

> **Revalidate the companion after applying table precedence**
>
> Fresh evidence beyond finding 111 is the hybrid-reference path: a companion stream can list its own object correctly and pass `_xref_stream`, but the classic table can list that object as free; this merge then replaces the companion's in-use row with the classic row without rechecking the invariant. With object 0's free-list link adjusted accordingly, `_xref_chain` accepts the revision, while pypdf can still open the companion directly through `/XRefStm`, so the full parse does not expose the inconsistency. After applying classic-table precedence, require the effective entry for the companion's object number to remain `(1, xrefstm, generation)`.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the fifty-second round.

# Fifty-third round: review of the companion-precedence revision (pull request #95)

**Reviewed commit:** `8c4ad88fb2` (finding 112).
**Review posted:** 2026-09-15T20:02:54Z, one automated Codex review with one inline comment. Reproduced verbatim.

## Finding 113 (P2) — `scripts/check_manuscript_source.py`, line 86

> **Treat NUL as PDF whitespace in object tokens**
>
> When a superseded direct object contains a NUL between name characters, such as `/Bad\x00Name`, Python's `\s` does not include NUL even though PDF classifies byte 0 as whitespace, so `_NAME` and `_TOKEN` consume this as one valid name. `_superseded_streams` consequently accepts the malformed historical object while the final pypdf pass sees only its replacement; use the explicit PDF whitespace byte set throughout the lexer.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the fifty-third round.

# Fifty-fourth round: review of the white-space revision (pull request #95)

**Reviewed commit:** `c2a67ae3c9` (finding 113).
**Review posted:** 2026-09-15T20:11:20Z, one automated Codex review with two inline comments. Reproduced verbatim.

## Finding 114 (P2) — `scripts/check_manuscript_source.py`, line 537

> **Bound superseded objects to their historical revision**
>
> When an older in-use object begins before its xref section but remains unterminated until bytes appended after that revision's `%%EOF`, `_object_end` scans across the xref, trailer, and later bytes and accepts the eventual closure. A later update can then replace the object, so the final pypdf pass sees only the replacement and `_xref_chain` accepts a revision that was never a complete PDF; bound parsing to the historical section offset rather than the entire file.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 115 (P2) — `scripts/check_manuscript_source.py`, line 542

> **Require a PDF token boundary after endobj**
>
> When a superseded direct object ends with `endobj\x0b`, this `\b` succeeds because Python treats vertical tab as a non-word byte, although vertical tab is neither PDF whitespace nor a delimiter. The historical object is therefore accepted as closed while pypdf reads only its later replacement; use the explicit PDF whitespace/delimiter boundary here as well.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the fifty-fourth round.

# Fifty-fifth round: review of the object-extent revision (pull request #95)

**Reviewed commit:** `426c06dd38` (findings 114–115).
**Review posted:** 2026-09-15T20:23:00Z, one automated Codex review with one inline comment. Reproduced verbatim.

## Finding 116 (P2) — `scripts/check_manuscript_source.py`, line 930

> **Reject manifest symlinks that escape manuscripts**
>
> Fresh evidence beyond finding 108 is that the bare-name check does not prevent the resulting path from being a symlink: replacing the required manuscript PDF with a same-named symlink to `../archive/2026-09-08/README_READ_FIRST_2026_09_08.pdf` makes `is_file()` succeed and causes `check_pdf` to validate the archive target, so the guard reports success although the required manuscript source is absent. Reject symlinks or require each resolved path's parent to remain the resolved manuscript directory.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the fifty-fifth round.

# Fifty-sixth round: review of the symbolic-link revision (pull request #95)

**Reviewed commit:** `156822e056` (finding 116).
**Review posted:** 2026-09-15T20:30:04Z, one automated Codex review with one inline comment. Reproduced verbatim.

## Finding 117 (P2) — `scripts/check_manuscript_source.py`, line 925

> **Reject a symlinked manuscripts directory**
>
> When the `manuscripts` directory itself is replaced by a symlink, each child reports `p.is_symlink() == False`, while `p.resolve().parent == directory.resolve()` remains true by construction. The guard therefore validates the symlink target and can succeed even though the entire canonical manuscript source directory has been replaced, contrary to this helper's stated “no symbolic link at any step” contract; reject a symlinked directory before accepting its manifest or children.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the fifty-sixth round.

# Fifty-seventh round: review of the linked-directory revision (pull request #95)

**Reviewed commit:** `ee3e4b8f3f` (finding 117).
**Review posted:** 2026-09-15T20:36:37Z, one automated Codex review with one inline comment. Reproduced verbatim.

## Finding 118 (P2) — `scripts/check_manuscript_source.py`, line 384

> **Reject indirect objects omitted from cross-reference sections**
>
> This loop examines only objects already listed in the section, so an unlisted indirect object is invisible to both structural validation and the later pypdf dereference loop. For example, inserting `99 0 obj\nnot-a-PDF-object\nendobj` immediately before the xref section of the valid classic fixture, while leaving `/Size 4` and its rows unchanged, makes `_xref_chain` return success; pypdf likewise has no object ID through which to inspect object 99. Reject indirect-object definitions that are not accounted for by the applicable cross-reference section, otherwise byte-mangled or malformed content can still pass the integrity guard.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the fifty-seventh round.

# Fifty-eighth round: review of the coverage revision (pull request #95)

**Reviewed commit:** `c472c2b3c8` (finding 118).
**Review posted:** 2026-09-15T20:44:28Z, one automated Codex review with one inline comment. Reproduced verbatim.

## Finding 119 (P2) — `scripts/check_manuscript_source.py`, line 565

> **Require separator comments to end before the next object**
>
> When a listed object's offset is immediately preceded on the same line by `%` (for example, `% hidden 1 0 obj`), this full match accepts `% hidden ` as a complete separator even though the PDF comment continues through the object's header until the next line ending. `_section_at` then parses from the cross-reference offset, so the guard can accept a revision whose apparent indirect-object declaration is actually commented out. Require each separator comment before an object or cross-reference section to include its terminating line ending.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the fifty-eighth round.

# Fifty-ninth round: review of the separator-comment revision (pull request #95)

**Reviewed commit:** `d4ce42bb76` (finding 119).
**Review posted:** 2026-09-15T20:50:58Z, one automated Codex review with one inline comment. Reproduced verbatim.

## Finding 120 (P2) — `scripts/check_manuscript_source.py`, line 827

> **Require line-delimited revision terminators**
>
> When an older revision writes `startxref 184 %%EOF\n` on one line, this regex accepts it because every separator is the unrestricted PDF-whitespace class, even though a complete PDF terminator requires `startxref`, its offset, and `%%EOF` on separate lines. A later valid incremental update can reference that section through `/Prev`; the structural walk succeeds and pypdf follows the xref chain without validating the superseded terminator, so a revision that was never properly terminated passes the guard. Require the appropriate line endings between all three components.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the fifty-ninth round.

# Sixty-first round: review of the sentinel revision (pull request #95)

**Reviewed commit:** `e59444dfba` (findings 121–122 and their tests).
**Review posted:** 2026-09-15T21:08:22Z, one automated Codex review with two inline comments. Reproduced verbatim.

## Finding 123 (P2) — `scripts/check_manuscript_source.py`, line 44

> **Count backslash parity before stripping TeX comments**
>
> Fresh evidence beyond the new single-escaped-`\%` test is a line such as `\\%\end{document}`: TeX reads `\\` as its own control sequence, so the following `%` starts a comment, but this negative lookbehind treats any immediately preceding backslash as escaping the percent and counts the commented sentinel as active. Determine whether the consecutive backslash run has odd parity before preserving `%`; otherwise a mangled source can still pass the fail-closed guard.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 124 (P2) — `scripts/check_manuscript_source.py`, line 47

> **Preserve within-line ordering of document sentinels**
>
> When the only occurrences are on one line as `\end{document} \begin{document}`, both searches return the same line index, so `e < b` is false and the source passes despite the commands being reversed. Compare character positions in the comment-stripped text, or compare columns when the line indices match, so the advertised ordering invariant fails closed.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the sixty-first round.

# Sixty-second round: review of the parity revision (pull request #95)

**Reviewed commit:** `b8ea3754c5` (findings 123–124).
**Review posted:** 2026-09-15T21:16:16Z, one automated Codex review with two inline comments. Reproduced verbatim.

## Finding 125 (P2) — `scripts/check_manuscript_source.py`, line 274

> **Keep the /W width when Predictor is 1**
>
> When `/DecodeParms` specifies `/Predictor 1` with geometry different from `sum(/W)`, this assignment changes the row width even though predictor 1 performs no prediction. For example, a five-entry `/W [1 2 1]` stream with `/Predictor 1 /Columns 8` can contain the 20 real entry bytes followed by 20 arbitrary bytes: `_xref_chain` counts five eight-byte rows, but `_xref_rows` consumes only the first five four-byte rows, so the surplus data is never validated. Keep the `/W` width for predictor 1.
>
> AGENTS.md reference: AGENTS.md:L31-L31

## Finding 126 (P2) — `scripts/check_manuscript_source.py`, line 660

> **Reject data in zero-member object streams**
>
> When an introduced `/ObjStm` declares `/N 0 /First 0`, `data[:first]` yields no tokens and the subsequent pair, offset, and member checks are all vacuous, so a nonempty arbitrary stream body is accepted when no type-2 row references it. The full parse treats that container as an ordinary stream and likewise never parses the hidden payload; require `/First` to be in bounds and the bytes following it to be only permitted padding when `/N` is zero.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the sixty-second round.

# Sixty-third round: review of the predictor-one revision (pull request #95)

**Reviewed commit:** `4967a92624` (findings 125–126).
**Review posted:** 2026-09-15T21:24:29Z, one automated Codex review with one inline comment. Reproduced verbatim.

## Finding 127 (P2) — `scripts/check_manuscript_source.py`, line 661

> **Require a token boundary at /First**
>
> When a historical object-stream member is later superseded, a payload such as `5 0true` with `/N 1 /First 3` passes because splitting the artificially truncated `data[:first]` treats `0` as a complete integer, while `_object_end` separately accepts `true` as the member. In the actual PDF byte stream, `0true` is one regular token because no whitespace or delimiter separates the final header integer from the member, so this malformed historical object stream escapes the fail-closed check; validate a real PDF token boundary at `/First` before accepting the header.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the sixty-third round.

# Sixty-fourth round: review of the token-boundary revision (pull request #95)

**Reviewed commit:** `873ff91650` (finding 127).
**Review posted:** 2026-09-15T21:30:19Z, one automated Codex review with one inline comment. Reproduced verbatim.

## Finding 128 (P2) — `scripts/check_manuscript_source.py`, line 47

> **Reject an end sentinel before the document begins**
>
> Fresh evidence beyond the prior within-line ordering fix is a source containing an active `\end{document}` before an otherwise valid `\begin{document}`/`\end{document}` pair: `rfind` selects the final end sentinel, so `e < b` is false and the malformed source passes even though TeX reaches the earlier end first. Compare the begin position with the first active end sentinel, or explicitly reject any active end before the begin sentinel.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the sixty-fourth round.

# Sixty-fifth round: review of the first-end-sentinel revision (pull request #95)

**Reviewed commit:** `319b7f7f53` (finding 128).
**Review posted:** 2026-09-15T21:34:51Z, one automated Codex review with one inline comment. Reproduced verbatim.

## Finding 129 (P2) — `scripts/check_manuscript_source.py`, line 48

> **Reject escaped document sentinels**
>
> When the only sentinels are written as `\\begin{document}` and `\\end{document}`, each `find` matches starting at the second backslash and `check_tex` returns success. TeX instead consumes the paired backslashes as the `\\` control sequence, so neither document-environment command is executed; account for the parity of the consecutive backslash run before each sentinel, as is already done for comment markers, so a source without a real document body fails closed.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the sixty-fifth round.

# Sixty-sixth round: review of the sentinel-parity revision (pull request #95)

**Reviewed commit:** `95d3a614f7` (finding 129).
**Review posted:** 2026-09-15T21:40:57Z, one automated Codex review with one inline comment. Reproduced verbatim.

## Finding 130 (P2) — `scripts/check_manuscript_source.py`, line 52

> **Require executable document sentinels**
>
> When the only occurrences are stored in macro definitions, such as `\newcommand{\fake}{\begin{document}}` and `\newcommand{\stop}{\end{document}}`, these searches still make `check_tex` succeed even though LaTeX does not execute either replacement body and the source has no document environment. Fresh evidence beyond the backslash-parity fix is that a 500-line source using exactly those definitions returns no problems; require the sentinels to be actual top-level commands (for example, standalone uncommented lines) rather than arbitrary token occurrences.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the sixty-sixth round.

# Sixty-seventh round: review of the standalone-sentinel revision (pull request #95)

**Reviewed commit:** `174114be1e` (finding 130).
**Review posted:** 2026-09-15T21:47:15Z, one automated Codex review with one inline comment. Reproduced verbatim.

## Finding 131 (P2) — `scripts/check_manuscript_source.py`, line 51

> **Reject sentinels inside multiline macro definitions**
>
> Fresh evidence beyond finding 130 is that standalone-line matching still accepts sentinels stored in multiline macro bodies, such as `\newcommand{\fake}{` followed on the next line by `\begin{document}` and likewise for `\end{document}`. A 500-line source containing only those two uninvoked definitions makes `check_tex` return no problems even though neither document command executes, so the guard still does not fail closed on a source without a document environment; track brace/macro context or otherwise require top-level sentinels.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the sixty-seventh round.

# Sixty-eighth round: review of the brace-depth revision (pull request #95)

**Reviewed commit:** `4f7ca64ce0` (finding 131).
**Review posted:** 2026-09-15T21:53:53Z, one automated Codex review with one inline comment. Reproduced verbatim.

## Finding 132 (P2) — `scripts/check_manuscript_source.py`, line 54

> **Ignore sentinels in inactive TeX conditionals**
>
> A 500-line source whose only standalone sentinels appear between `\iffalse` and `\fi` passes `check_tex`, because those lines remain at brace depth zero even though TeX skips both commands and never opens a document environment. Track inactive conditional regions (or otherwise verify that the commands are executable) before accepting these matches, so the provenance guard continues to fail closed.
>
> AGENTS.md reference: AGENTS.md:L31-L31

No other findings were posted in the sixty-eighth round.
