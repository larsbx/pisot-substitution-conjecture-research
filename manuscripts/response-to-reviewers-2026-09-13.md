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
