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
