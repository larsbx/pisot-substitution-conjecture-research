# Issue #138: historical GitHub closure, existing reopening, and narrower live A1′ (2026-10-23)

**Outcome:** #138 **was closed and subsequently reopened** before this audit. The GitHub issue is **open**; one-sided residual hub-edge coincidence **A1′ is not yet proved**. No new reopening was necessary or performed during this reconciliation.

**Evidence, not inference:** GitHub [issue #138](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/138) event history records:

| UTC date | Github event | Mathematical effect |
| --- | --- | --- |
| 2026-09-26 06:15:09 | `closed` | None established; historical closure is real. |
| 2026-10-01 20:50:15 | `reopened` | Restored open tracker; opening/closing are not mathematical proofs. |
| 2026-10-23 audit | `open`, reason `reopened` | Consistent with README, proof ladder and two-obstruction completion theorem. |

The issue's October 1 [reopening comment](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/138#issuecomment-5940285934) explicitly says the previous closure had **no theorem-bearing artifact attached** and the universal aligned-branch theorem remained unproved. No retrospective explanation of *why* it was closed is asserted.

## Precise scope: what #138 must now prove

The **original issue body** describes a stronger goal: for every ternary primitive irreducible Pisot substitution, *every* pair of distinct letters eventually coincides for both the substitution and its reversal. That remains a meaningful strengthening, but the live October 19 [#138 update](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/138#issuecomment-6269090857) and [one-sided refinement](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/138#issuecomment-6269139534) explicitly narrow the *necessary completion premise* to **A1′**:

> In the residual bad-hub configuration after the established ternary endpoint-map/Barge–Diamond good-pair and squaring reductions, if the first-letter map fixes the two letters of the remaining bad hub edge, that pair must be eventually coincident.

The completion argument uses **universal A1′** on the left/aligned side *after* **universal BH (#139)** forces the relevant cyclic strict-zipper overlap to an offset-zero descendant. The reversed/suffix theorem is not a separate third universal premise. The statement must hold in the entire ternary PIP regime, **without** secretly adding legality, finite injectivity, independent tile lengths or unimodularity.

The October 19 [Barge–Zamboni / fixed-rays comment](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/138#issuecomment-6269786183) identifies a possible conditional reformulation through proximality of the two fixed rays; it is an **attack interface**, not a proved universal proximality or strong-coincidence theorem. Subsequent finite address/length-window constraints in draft PR #295 are likewise not an accepted A1′ closure.

## Relationship to #139 (different administrative histories)

* **#138:** closed September 26, reopened October 1, **already open** on October 23. This action updates the historical note, issue title and scope banner **without changing its state**.
* **#139:** closed October 23 at 10:09:55 UTC, reopened October 23 at 17:45:32 UTC after the closure/ledger mismatch was found. See [#139 reconciliation](issue-139-tracker-mathematics-reconciliation-2026-10-23.md).
* **#84:** seedwise overlap productivity remains open. The ternary two-obstruction completion theorem needs *both* universal A1′ and universal BH; no issue's historic `closed` flag satisfies either premise.

## Verified settled inputs and remaining gate

Established structures in the repository include the Barge–Diamond good-edge existence input, the C/D/E/F endpoint normal forms, fixed/alternating template reduction, and finite family certificates at their recorded quantifiers. These are **not** the desired universal residual hub-edge coincidence theorem.

**Completion criterion:** a full-domain, hypothesis-exact and source-backed proof of A1′, integrated through the governed proof-dependency and evidence pipeline, or a genuinely new valid alternative proving the required aligned branch. Merely obtaining a finite census, candidate geometric witness, proposed local word-growth route, or fixed-ray reformulation is insufficient.

**Action taken:** preserve the existing open issue state, update its title and add an explicit historical scope banner while preserving the original issue text; add this dated audit and link it from current README/onboarding/roadmap, companion high-degree comparison and #139 audit. Append a correction to the side-notes ledger. Do not edit historic receipts or generated proof ledger; no theorem promotion, source-code change, CI result or independent human mathematical review is claimed.
