# v16/later source-provenance audit — issue #45

**Status:** authoritative repository audit of reachable Git history as of 2026-09-12. This record imports the surviving sources without upgrading source-pending claims.

## Audit scope and method

Repository: `larsbx/pisot-substitution-conjecture-research`.

Audit base: `main@ebe53e2cef40d5dff60dc39f14696137da77e1ac`.

The audit examined all 68 named remote branches (69 remote refs including `origin/HEAD`) and all 319 commits reachable from those refs. It searched:

- every reachable object path for manuscript versions `v16` and later and for Galois, wedge, concentration/aux-B, realization, and coincidence-rank names;
- every reachable text revision for the corresponding theorem phrases;
- commit messages, additions, and deletion history;
- Issue #45, PR #47, the two-gate audit branches, the P1-A branch, and the preserved 2026-09-08 archive.

No reachable branch or commit contains a `PSC_PROOF_v16` (or later) source, and no deletion record identifies such a file. The first reachable occurrence of “v16” is a status/provenance report, not a manuscript: commit `1009dccba6bd802c80e989ace1508572c06bfdda`.

This is a negative result about the accessible repository record, not a claim that no source ever existed outside GitHub.

## Imported source map

| Claim or obligation | Reachable authoritative material | Imported location | Audit status |
| --- | --- | --- | --- |
| G1b-1 bounded discrepancy | The 2026-09-11 ledger at `1009dcc` records the estimate `Disc(sigma w) <= c Disc(w) + 2 E_sigma`, but supplies no detailed proof; v15 predates this rung | ledger remains at `docs/completion-ledger-2026-09-11.md` | **SOURCE-PENDING**; do not mark repository-proved |
| Galois wedge-nonvanishing propagation | The preserved v34 certificate at `25ed126` contains related Galois-transitivity arguments for rational wedge factors; the later carrier-level propagation theorem first appears only as a status assertion at `1009dcc` | `archive/2026-09-08/certificates_patched/PROOF_CERTIFICATE.md` | **PARTIAL PREDECESSOR SOURCE ONLY**; exact later theorem remains source-pending |
| concentration / aux-B | Exact research target introduced at `af46a0e`; sharpened v34 inheritance/escape audit at `1297174` | `docs/source-imports/issue-45/p1a-concentration-aux-b-program.md`; `docs/source-imports/issue-45/p1a-v34-concentration-audit.md` | **OPEN CONJECTURAL GATE**; formulation imported, no proof claimed |
| realization / coincidence-rank equivalence | The equivalence first occurs in reachable history as a status-level assertion at `1009dcc`; no detailed proof source occurs on any reachable ref | ledger and corrected source-audit manuscript | **SOURCE-PENDING**; formal recurrence, global realization, and collar evidence remain distinct |
| v15 theorem/citation baseline | Preserved verbatim by remediation commit `25ed126`; archive provenance identifies v15 as the last imported canonical manuscript | `archive/2026-09-08/manuscripts/PSC_PROOF_v15.tex` | historical baseline; known P0 defects retained only in the immutable archive |
| P0 corrections | Checklist introduced at `cb2de9f`, incorporated in the two-gate ledger at `1009dcc` | `docs/manuscript-p0-corrections-2026-09-11.md`; `manuscripts/PSC_PROOF_next_source_audit.tex` | repaired in the new working manuscript without theorem promotion |

## File-level provenance

The two files under `docs/source-imports/issue-45/` are byte-for-byte source imports:

- `p1a-concentration-aux-b-program.md` from commit `af46a0e`, path `docs/p1a-concentration-aux-b-program.md`;
- `p1a-v34-concentration-audit.md` from commit `1297174`, path `docs/p1a-v34-concentration-audit.md`.

The new manuscript `manuscripts/PSC_PROOF_next_source_audit.tex` is derived from the archived v15 source and therefore is not represented as the missing v16 manuscript. Its front-page notice identifies that fact and freezes the four source boundaries above.

## Claim-status rules

1. “Theorem-grade in the v16 track” is historical status metadata until the detailed proof is imported; it is not `RepositoryProved`.
2. The v34 Galois calculations may be cited only for their exact rational-factor/transitivity statements. They do not stand in for the missing carrier-level nonvanishing theorem.
3. Concentration/aux-B is an open implication from a closed recurrent nonproductive carrier to nonzero dominant wedge projection.
4. Span-rich/productivity conclusions that use concentration remain explicitly conditional.
5. The realization/coincidence-rank chain remains a source-pending reformulation under the finiteness hypothesis; a formal BPA cycle, a globally realized component, and finite collar survival are not interchangeable.
6. G1b-1 remains distinct from G1b-2: bounded discrepancy does not imply finite BPA state space.
7. No source here assumes unimodularity, finite injectivity, or discreteness of `pi_s(Z^A)`.

## Manuscript repairs applied

The new working manuscript:

- removes the false primitivity-alone aperiodicity assertion;
- separates primitive+aperiodic Mossé recognizability from Pisot-specific inputs;
- distinguishes Barge–Diamond strong coincidence, Hollander–Solomyak balanced-pair/two-symbol PDS, and Sirvent–Solomyak symbolic/tiling-action algorithm results;
- restricts mass-balance language to closed nonproductive carriers where no leakage is used;
- keeps concentration-dependent span-rich conclusions conditional;
- derives UD from nonzero determinant/full incidence rank rather than assuming it;
- retracts the phase-state-to-total-padding inference;
- preserves the non-unimodular and realization/computational-completeness firewalls.

## What is still required to clear the source-pending tags

For each source-pending result, import either:

- the original detailed manuscript/note with its original version identity and authorship metadata; or
- a fresh self-contained proof, separately audited and clearly identified as a reconstruction rather than the missing historical source.

Until then, the prose and TLA ledgers must continue to encode these nodes as unavailable to the no-assumption proof path.
