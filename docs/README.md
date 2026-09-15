# Documentation index

This directory separates live proof status, source provenance, mathematical
exposition, exact finite certificates, and historical snapshots. Start with
the section matching the question you are asking.

## Current status

1. `claim-status-and-source-map-2026-09-13.md` — concise authoritative
   classification of every load-bearing claim and its exact source.
2. `conjecture-ledger.md` — live prose dependency ledger.
3. `proof-ladder.md` — shortest honest path from established results to the
   remaining theorem.
4. `current-proof-architecture-2026-09-11.md` — detailed architecture, including the original two-gate assembly and the later G1-free overlap/density alternative; updated beyond its filename date.
5. `../manuscripts/PSC_balanced_pair_state_2026-09-13.tex` — publication-form
   state-of-program exposition.

When these disagree, do not choose the strongest wording. Check the latest
merged commit, the claim/source map, the proof note, and `tla/Ledger.tla`,
then repair all status surfaces together.

## Cross-program engineering

- `library-extraction-candidates-2026-09-14.md` — ranked audit of code that
  could move into shared libraries with NLAP-JT (exact arithmetic,
  substitution kernel, intervals, linear algebra, proof records, audits);
  engineering only, no claim status changes.
- `cross-program-bridge-psc-nlapjt-2026-09-12.md` — structural comparison
  with the NLAP-JT finite Mandelbrot program.

## Source provenance

- `archive-tarball-audit-2026-09-13.md` — uploaded archive digest, identity check, and warning about contradictory v34 closing status language.
- `source-provenance-v16-later-audit-2026-09-12.md` — exhaustive reachable
  Git-history audit and imported-source checksums.
- `galois-aux-b-source-resolution-2026-09-13.md` — separates the historical
  degree-three seed theorem, the reconstructed degree-two carrier theorem, and
  open concentration.
- `source-imports/issue-45/g1b1-bounded-discrepancy-reconstruction.md` —
  self-contained proof replacing dependence on the unrecovered contraction
  estimate.
- `source-imports/issue-45/realization-coincidence-rank-audit.md` — G0–G6
  decomposition of the open realization bridge.
- `source-imports/issue-45/p1a-concentration-aux-b-program.md` and
  `p1a-v34-concentration-audit.md` — preserved formulation and inheritance
  audits, not proofs of concentration.

The missing `PSC_PROOF_v16` file is a historical provenance fact. It is not a
current dependency for G1b-1 or degree-two carrier-span propagation.

## Exact finite-domain results

- `p1a-degree3-partial-theorem.md` — no strict `K2=0`, first-`K3`
  component in the exact 4,554-member short-image corpus.
- `p1a-degree2-wedge-productivity.md` — no closed nonproductive recurrent
  nonzero-`K2` component in the same corpus.
- Canonical executable certificates live in `../mojo/` and are enforced by
  GitHub Actions.

These are theorems over their enumerated finite domain. They are evidence, not
general concentration or wedge-productivity theorems. Certificates must fail
closed on caps and retain a replayable record for every survivor.

## Level 2: finiteness

- G1b-1 bounded discrepancy: repository-proved.
- Seed-patch overlap-graph finiteness: repository-proved from bounded discrepancy.
- Overlap productivity remains open; the density-to-PDS bridge is an imported theorem (Barge–Štimac–Williams), so overlap productivity for one seed already implies PDS (manuscript Theorem 5.38). Its endpoint-aligned case is the two-sided strong coincidence condition of Arnoux–Ito, and under strong coincidence it is a hitting statement for prefix Parikh vectors (Propositions 5.39–5.40, Corollary 5.41; note Section 9); the contracting lower bound on the hitting level (Proposition 5.42) explains at most 7 of the up to 17 inflations observed (note Section 10).
- G1b-2 renewal finiteness: open and now equivalent to G1.
- `bpa-literature-bridge.md`: interface audit between literature algorithms
  and the normalized all-seed repository graph.
- Renewal, address, and countermodel notes should preserve non-unimodularity
  and must not treat the projected integer module as a lattice.

## Level 3: productivity

- `sink-scc-reduction.md`: finite obstruction extraction under G1.
- Endpoint, signing, first-defect, ordered-area, recognizability, and hierarchy
  notes provide supporting structure.
- General concentration (`K2=0` branch) remains open.
- General wedge productivity (`K2!=0` branch) remains open.
- Full rational wedge span does not imply productivity.

## Realization and collar experiments

The realization/MEF track is an open bridge and parallel certification route.
A formal recurrent BPA component, a globally realized tiling component, and a
component surviving a finite collar radius are not interchangeable. Use the
G0–G6 audit before citing an equivalence.

## Historical material

- `../archive/2026-09-08/README_READ_FIRST_2026_09_08.md` explains the
  preserved archive.
- `../archive/2026-09-08/manuscripts/PSC_PROOF_v15.tex` is the last imported
  canonical predecessor manuscript.
- `../archive/2026-09-08/certificates_patched/PROOF_CERTIFICATE.md` contains
  the restricted degree-three seed theorem.
- Dated completion ledgers are snapshots, not automatically current.

Historical files are immutable evidence. Correct their live interpretation in
the current ledgers rather than rewriting the archive.

## Verification and implementation

- `verification-architecture.md` describes the responsibilities and limits of
  Mojo, TLA+, Lean, and Python.
- `../AGENTS.md` is the implementation policy.
- Mojo is canonical for executable research.
- TLA+ records dependency/state-machine claims.
- Lean checks deductive finite algebra.
- Python is an independent oracle or prototype, not the executable source of
  truth once Mojo exists.

Run all available verification layers with:

```bash
./scripts/verify_all.sh
```

A skipped unavailable toolchain must be reported; it is not a passing proof.

## Status-change checklist

When a theorem status changes:

1. identify the exact statement and hypotheses;
2. classify it using the claim/source vocabulary;
3. attach the proof, import, finite certificate, or named open obligations;
4. update the claim/source map, conjecture ledger, proof ladder, detailed
   architecture, README, manuscript status table, and TLA ledger as applicable;
5. update citations and distinguish mathematical sources from Git provenance;
6. retain finite-domain parameters and countermodel behavior;
7. run verification and obtain review before merge.
