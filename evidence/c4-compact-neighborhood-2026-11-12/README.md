# Compact-neighborhood transfer: local evidence

**The complete local isolated source build and compiled axiom audit passed.**
The accepted code revision is 6915e8d592b7ea5cb7c6950249811e354dc6c3e7, tree c79e97bdae1224068895afa9dcf6cca6d7fe9fbb. The process ended at
2026-11-12T19:37:14.200269+00:00 with exit code zero and unchanged HEAD, tree and
recorded source bytes. This is local acceptance; no hosted success or
independent human review is asserted.

## Completed acceptance records

| Record | Observed result |
| --- | --- |
| gate/process-terminal.json | Unchanged ./tools/check_lean.sh completed with exit zero |
| gate/isolated-lean.log.gz | Complete raw audit: 6628 compiled constants, 4850 compiled theorem constants |
| gate/compiled-audit-inspection.json | Independent inspection passed against exact committed sources |
| gate/compiled-new-declarations.log.gz | 39 new-module owned constants, 31 theorem constants; all 23 explicit theorems and eight definitions matched |
| gate/inspect-compact-audit.py | Exact inspector source used for the recorded inspection |
| artifact-manifest.json and SHA256SUMS | Complete archive byte verification with no self-reference cycle |

Compressed logs preserve the original bytes, including empty final tab fields.
Attempt 03 supplies this acceptance. The first attempt remains terminal-unknown,
the second remains failed, and the retained-workspace import is diagnostic only.
Both start receipts and the first partial log remain historical snapshots.
Detailed source and log digests are in receipt.json.

## Exact source and gate chronology

| Role | Commit | Tree |
| --- | --- | --- |
| Merged baseline after PR #557 | `bdf033f647f73f911a47260e8bdad5f2e96f3c7a` | `73201424138427d63ddf05c9c1102f424af5b1af` |
| Pre-code literature GO | `571c8df9b5223aeef6b7f137c49b4495590d090e` | `9bdb1e1a896f4f29b570d843693d8672de29d06b` |
| Code under the isolated gate | `6915e8d592b7ea5cb7c6950249811e354dc6c3e7` | `c79e97bdae1224068895afa9dcf6cca6d7fe9fbb` |

The code commit's direct parent is the literature gate, whose parent is the
baseline. The gate note is unchanged between the decision and code commits.
`gate/chronology.json` records the original commit metadata and note digest;
`gate/literature-go.md` is the committed decision itself. The later code
contains deductive topology and formal counterexamples within that decision.

`source-manifest.json` hashes the source/configuration files identified when
the gate started, plus the implementation commit's changed files and the
literature note. All 132 records were read from Git objects at the exact
code revision; every gate-start hash was checked against those objects.
`source-inventory.json` binds the explicit declarations to the same committed
source blobs. Neither manifest is a compilation result.

## Archive integrity

`SHA256SUMS` pins every file in this packet except itself, including
`artifact-manifest.json` and all preserved nested histories. Every checksum
path starts with `./`, so nested entries remain packet-relative under
`tests/test_recorded_data_integrity.py`. The artifact manifest excludes
itself and `SHA256SUMS`; generation therefore follows artifact bytes, then
manifest, then checksums without a self-reference cycle. Historical
`files.sha256` records retain their original names and bytes. The complete
first-attempt packet is stored in `history/attempt-01.tar.gz`; its restore
instructions are in `history/README.md`. The outer checksum set pins that
container and all remaining direct records.
These integrity records do not supply a terminal acceptance result.

## Formal target and its boundary

The generic layer uses the existing matrix-adic compatible-sequence carrier
with its induced topology. A norm ball and one quotient-kernel condition
form a zero-neighborhood basis. For compact sets K and L, simultaneous
approximation to both sets at a sufficiently small stable tolerance and a
sufficiently deep fixed residue level places the common point in any open
neighborhood of their intersection.

For either original named source, the adapter consumes its own authentic
prefix tiles and literal prefix-witness theorem. For a fixed finite carrier
C with a supplied actual StrictSystem, and an open neighborhood U of the
represented cut-pair intersections, it proves the intended quantifier order:

    for every open U covering the represented overlap,
    there exists N such that for every n >= N, every T in C,
    and every pair of actual balanced-cut marks in the 12*n inflations,
    the original common Parikh cut point lies in U.

The carrier-specific union is indexed by the actual `CutPair C` relation.
`strict_cut_labels` authenticates each actual cut's represented labels. The
all-distinct-letter union remains available as a separate interface. The
finite-open-cover form selects the finite subcover J before selecting N.
The following letters, complete marks, source identity, common integer
prefix vector and original product carrier remain explicit.

The source inventory contains **23 explicit named theorems and eight
explicit definitions**:

| Module | Theorems | Definitions |
| --- | ---: | ---: |
| `CompactNeighborhood` | 8 | 2 |
| `NamedCutNeighborhood` | 12 | 3 |
| `CompactNeighborhoodControls` | 3 | 3 |
| Total | 23 | 8 |

The source proof-bank check reports 126 governed claims, 2,693 named Lean
proofs and 411 source openings. These are source inventory totals, not
compiled audit totals. All governed claim statuses remain unchanged.

## What each retained record establishes

| Material | Evidence and scope |
| --- | --- |
| `development/generic-01.log`, `generic-02.log` | Both generic-module development attempts, including the initial errors |
| `development/named-01.log`, `named-02.log`, `named-03.log` | Named-adapter attempts, including the existential-syntax error and the later carrier-specific refinement |
| `development/controls-01.log`, `controls-02.log` | Both formal-control development attempts, including the initial unavailable identifier |
| `development/controls-axioms.log` and `.lean` | Three control statements and their printed development axiom dependencies |
| `development/bootstrap.log` | Fourteen successful baseline development compilations, with exit records; reused project/dependency artifacts were involved |
| `development/attempts.json` | Interpretation of preserved diagnostics and the limits of silent logs |
| `checks/governance.log` | Observed successful terminology, claims, coverage, promotion, numerics and consistency audit message |
| `checks/ledger.log` | Observed message that 32 generated surfaces are current |
| `checks/proof-bank-check.log`, `proof-bank-generation.log` | Generated-source inventory totals |
| `review/initial-ci-and-semantic.json` | Historical CI observations, initial semantic source review, environment inventory and development bootstrap provenance |
| `review/final-source-scope-addendum.json` | Read-only semantic inspection of the final carrier-specific adapter at the code commit |
| `gate/process-start-snapshot.json` (attempt 01) | Historical gate-start identity and source hashes, copied before completion |
| `gate/isolated-in-progress-snapshot.log` (attempt 01) | A historical partial log snapshot, retained separately from the complete terminal log |
| `history/attempt-01.tar.gz` | Exact interrupted-attempt preservation; terminal outcome unknown, no acceptance |
| `history/aggregate-diagnostic/` | Retained-workspace import, exit zero without `-o`; diagnostic only |
| `history/attempt-02/` | Complete terminal exit1 and cache disk-space failure; no acceptance |
| `history/integration-provenance.json` | Exact copy digests and retained snapshot metadata |
| `history/cache-cleanup.json` | Root-owned removal of the abandoned generated first workspace after archive verification |
| `gate/attempt-03-process-start-snapshot.json` | Genuine nonterminal start receipt for the third attempt, with separate capture provenance |
| `gate/attempt-03-runner.py` | Exact heartbeat runner; unchanged checker command and raw child log |
| `next-count-plan.md` | The next finite integer-cut counting target and the separate analytic obligations |
| `next-count-interface-review.md` | Reviewed proposed, uncompiled interfaces for factor-start cardinality, actual marks, empty/erasing cases and exact `CutPair` labels |

Several later development logs are empty. They are preserved as observed;
empty output alone is not a successful process-exit receipt. Narrow local
compilation with reused artifacts does not replace the repository's full
isolated source build. The only development bootstrap exit results asserted
here are the 14 explicit zero exits recorded in its log and review receipt.

The original semantic review predates the carrier-specific addition. Its
source hash and observation times remain intact. The final-source addendum
checks the added `carrierOverlap` definition and its compactness, eventual
containment and finite-cover theorems against the committed final source.
That inspection found no scope defect and makes no compiler claim.

## Independent formal controls

The three new counterexample theorems retain the substantive hypotheses:

1. Closed, disjoint real-plane sets—the axis and a hyperbola—admit
   arbitrarily close witnesses. Closedness alone cannot replace compactness.
2. Compact singleton sets can have arbitrarily close nonzero approximants
   outside their exact intersection. The target must be a neighborhood;
   arbitrary containment cannot replace openness.
3. A moving spike converges pointwise for each fixed natural index while
   failing uniform convergence over the infinite family. A fixed finite
   source carrier is essential to the uniform threshold.

The development axiom output for these three controls lists only `propext`,
`Classical.choice` and `Quot.sound`. The complete isolated compiled audit passed; its terminal process receipt,
complete log and independent declaration inspection are archived in gate/. The existing depth-q versus depth-(q+1) residue control belongs to
the earlier cut-prefix increment; it is not a new numerical replay here.
These controls are abstract interface counterexamples, not counterexamples
to the standing Pisot conjecture.

## Execution history

The first isolated attempt lost its root-owned session handle near 18:36 UTC
after its log reached 9021/9023. Its original receipt has no terminal exit
and no completed audit. The cause of the session loss remains unknown. Its
log, receipt, runner and attributed observation are preserved separately
under `history/attempt-01.tar.gz`; earlier snapshots remain in `gate/`.

A retained-workspace import of `PscVerif.lean`, with no output artifact
requested, exited zero in about 59 seconds. Its result grants no formal
acceptance credit and records no aggregate `.olean`; the complete records
are under `history/aggregate-diagnostic/`.

The fresh second attempt ended at 2026-11-12T18:43:28.732049+00:00 with
exit code 1 after 136.322 seconds. Official dependency-cache extraction
reported `No space left on device`. Its receipt records unchanged HEAD,
tree and source bytes. `history/attempt-02/` retains the complete failure
receipt, compressed raw output and runner. No mathematical failure or
acceptance is inferred from this provisioning failure. No second-attempt
start receipt was reconstructed after its process ended.

After preserving those records, the root removed only the abandoned
generated first workspace; `history/cache-cleanup.json` records the scope
and archive verification. A fresh third unchanged checker began at
2026-11-12T18:46:08.507683+00:00. Its genuine running receipt was captured
at 18:46:31.191315 UTC. It binds the same code, tree and source hashes and
uses separate heartbeat output, raw log and process receipt.

The third attempt must supply its own real terminal zero exit, unchanged
sources and matching completed compiled inspection. No earlier attempt or
supplemental diagnostic can replace those requirements.

## Replaying the required gate

At the exact code revision, use the unchanged repository verifier:

```bash
python tools/make_proof_bank.py --check
./tools/setup_lean.sh
./tools/check_lean.sh
```

The verifier prepares fresh sources, checks dependency pins, uses the fixed
upstream source-hash Mathlib cache, compiles the complete project, and audits
every local compiled declaration. It does not credit locally cached project
or dependency compilation artifacts. The expected standard axiom allowance
is `propext`, `Classical.choice`, `Quot.sound`.

In the recorded workspace the pinned toolchain is Lean 4.34.0-rc2, commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`. The recorded gate invocation
uses the workspace-backed temporary directory:

```bash
ELAN_HOME=/workspace/scratch/84c835820757/toolchains/elan \
PATH=/workspace/scratch/84c835820757/toolchains/elan/bin:$PATH \
TMPDIR=/workspace/scratch/f96c28a561ad/lean-isolation-tmp \
./tools/check_lean.sh
```

The root-owned third invocation completed successfully with unchanged HEAD, tree
and recorded sources. Finalization launched no compiler, test or second gate.
The terminal records and exact byte hashes are listed in gate/README.md and
receipt.json.

## Hosted status and historical observations

No hosted success is asserted for code commit `6915e8d5`. This staging task
made no remote writes and did not poll CI. A separate read-only observation
of draft PR #558's initial source-mirror head
`630415d2a90dac8e8e1de6625bed13edcc9a5523` at 2026-11-12 18:46:37 UTC
returned all 78 check runs: 77 queued and one cancelled evidence-policy
check, with a newer evidence-policy run queued. No check had succeeded at
that observation. The exact snapshot is preserved in
`review/hosted-checks-20261112T184637Z.json`. It is preliminary history,
not acceptance or a guarantee of current status. The final publication head
needs a separate hosted observation. All local acceptance guards remain
bound to the original code revision `6915e8d5` and its exact tree.

The review notes also contain a historical observation of the preceding
PR #557 head `c5c38db3` at
2026-11-12 17:19:51 UTC: 98 queued checks and one cancelled policy check,
with no successful substantive gate at that observation. That snapshot is
neither a current status report nor evidence of execution at the new code
revision. Independent human review remains pending as separate validation
debt.

## Remaining mathematics

This increment proves neither exact overlap membership nor positive
product-Haar measure. It does not supply a lattice count, normalization,
covolume, strict-cut density bound or general PSC conclusion. An arbitrary
measurable or half-open cylinder cover must first be proved to contain an
open neighborhood before the new transfer can consume it.

The [next-count plan](next-count-plan.md) and its
[interface review](next-count-interface-review.md) describe proposed,
uncompiled proof interfaces. The review tightens occurrence-indexed
factor-start cardinality, empty and erasing cases, and exact `CutPair`
labels. A whole-word power-scaling adapter remains to be proved.

The next plan recommends counting the **original integer Parikh cut
vectors**, using the complete balanced-pair factorization and positive
physical lengths. It keeps those cardinalities separate from the internal
image set `cutPoints`: injectivity/cardinality preservation of `ambientStar`
is not proved by this increment. Anchored reference ordinals may repeat and
must not replace the original cut count.

Fixed-origin regular-cylinder lattice asymptotics, all-depth original-carrier
normalization, the chart's actual covolume, regular outer-cover measure
control and positive-overlap assembly remain separate obligations. The plan
adds no new theorem code or accepted premise.
