# G1 is necessary for PDS: closed implication versus open universal assertion (2026-10-23)

**Disposition:** restore an important proof-status distinction in the discussion and repo documentation. The implication **pure discrete spectrum (PDS) ⇒ G1** is **repository-proved** (project-accepted for progression, independent human validation outstanding). This is an already-closed theorem claim, **not** an additional open G1 premise. The separate assertion that **every** primitive irreducible Pisot substitution satisfies G1 remains **open**, just as general PSC remains open.

**Pinned live source:** `main@c762210e0a7c7f59ec7345fe107af423173ff931`, `docs/claim-status-and-source-map-2026-09-13.md`, `docs/conjecture-ledger.md`, `docs/proof-ladder.md`, `tools/make_ledger.py`, generated `docs/ledger-index.md`, `docs/p1b-vertex-coincidence-box-2026-10-02.md` §5.1, `docs/audit-2026-10-04.md`, and `docs/side-notes-ledger.md` §7.

## 1. Exact established result

For each substitution `sigma` in the repository's primitive irreducible Pisot regime:

```text
PDS(sigma)
    => no strict-zipper periodic-pair obstruction from any swap seed
       [Theorem S, coincidence-rank import and realization/fibre lemmas]
    => G1(sigma): finite balanced-pair automaton from every swap seed
       [Proposition 5.47, half-coincidence route]
```

The repository claim `PDSImpliesRepoG1` is **Repository-proved**, dependency closure **complete** (audited October 4; explicit theorem-side dependencies added October 5). The proof relies on `CoincidenceRankFibreTheorems` (import), `ReturnModuleFullRank`, `PeriodicPairOneFibre` and `StrictZipperPeriodicPairForm` (repo nodes). The argument passes through *legal realized* periodic tiling pairs in a shared maximal-equicontinuous-factor fibre; existence of a persistent strict zipper would force coincidence rank ≥2, contradicting PDS. It respects non-unimodular substitutions. Independent human review is still pending, not a new mathematical hypothesis.

A second *already-proved implication* is
`PDSImpliesSeedwiseTermination`: PDS implies the repository's balanced-pair algorithm terminates **with coincidence** from **every** swap seed `(ab,ba)`, regardless of whether `ab` is a legal substitution-language factor. This uses `PDSImpliesRepoG1` and the imported `StrongCoincidenceFromPDS`, as recorded in the machine dependency ledger. Thus the formerly stated Open Problem 4.24 is resolved *as an implication*.

## 2. What was not closed

These four propositions have distinct truth statuses:

| Mathematical statement | Source-record status | Logical meaning |
| --- | --- | --- |
| **For each sigma, PDS(sigma) ⇒ G1(sigma)** | **Repository-proved**: `PDSImpliesRepoG1`, dependency complete | Necessity theorem; closed. |
| **For each sigma, PDS(sigma) ⇒ seedwise BPA termination with coincidence** | **Repository-proved**: `PDSImpliesSeedwiseTermination`, dependency complete | Stronger consequence of PDS; closed. |
| **For each sigma, G1(sigma)** | **Open universal gate**: `G1` | Cannot apply the implication without proving PDS for that sigma or providing another sufficient premise. |
| **For each sigma, PDS(sigma)** | **Open PSC target** | The implication above does not discharge its own premise. |

The machine ledger keeps `G1` explicitly `status:open`. Its alternative sufficient proof routes are `G1FromRenewal` (G1b-2, [#44](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/44)), `G1OverlapRoute` (all-seed productivity), `G1HalfCoincidenceRoute` (all-seed strict-zipper exclusion / BH), and `G1FormalProductivityRoute`; the relevant universal premises have not all been discharged. **No change to these machine statuses is justified.**

This does **not** represent a contradiction: `∀sigma (PDS(sigma) ⇒ G1(sigma))` is a theorem even if neither `∀sigma PDS(sigma)` nor `∀sigma G1(sigma)` is currently proved. Moreover, PDS established for a *specific* finite-domain specimen or family gives G1 there by the already-proved implication. The accepted class-D `b=0` G1 corollary is also a separate scoped result and does not require this general implication to be newly proven.

## 3. Relationship to #138, #139 and #84

For the ternary completion programme:
* Universal **BH (#139)** would give G1 as a consequence by the half-coincidence bound; **BH remains open** and was tracker-reopened on 2026-10-23. Its statement cannot be deduced from `PDS ⇒ G1` without already knowing PDS.
* Universal **A1′ (#138)** is the residual aligned bad-hub coincidence obligation for productivity/PDS; it is **not** a needed extra premise for G1. #138 was historically closed 2026-09-26 but **already reopened** 2026-10-01.
* The shortest **#84 one-seed overlap-productivity route** proves PDS without presupposing G1. Once PDS is proved, the necessity theorem independently derives G1, all-seed BPA finiteness and seedwise termination. Using that derived G1 to justify #84's PDS premise *before* proving productivity would be circular.

## 4. Audit of status surfaces and decision

The `main` claim/source map has separate `Finite BPA, G1` (open) and `PDS implies G1` (repository-proved) rows; `docs/ledger-index.md` independently says `PDSImpliesRepoG1` complete but `G1` incomplete. The proof ladder, README and October 16 completion ledger make the same distinction. The earlier conversation repeatedly said only "G1 remains open", which was **incomplete without acknowledging this established closure**; conversely, saying "G1 is universally proved by PDS" would assume the still-open conjecture.

**Decision:** preserve both claims as recorded and explicitly annotate the current documentation. Do not re-open `PDSImpliesRepoG1`, re-close unconditional `G1`, change issue #44, or regenerate/alter governance/TLA surfaces. Keep the existing internal/adversarial-audit and outstanding independent-human-review labels separate.
