# Finite integer cut count: local evidence

**The complete local isolated source build and compiled axiom audit passed.**
The accepted source revision is 31f8046291f2428e839d95e8890c8342858ec210, tree e38c3f65efb79fa72860d8ef222e96695847a551. The root-owned process
ended at 2026-11-12T21:08:49.179037+00:00 with real exit zero and unchanged HEAD,
tree and recorded source bytes. This is local acceptance, with no hosted
success or independent human-review claim. The archived literature audit
remains postimplementation; a passing gate does not change its chronology.

## Completed acceptance records

| Record | Actual result |
| --- | --- |
| gate/process-terminal.json | Unchanged ./tools/check_lean.sh exited zero with stable sources |
| gate/isolated-lean.log.gz | 6646 compiled constants; 4865 theorem constants |
| gate/compiled-audit-inspection.json | All 12 explicit proofs (nine public, three private helpers) and three definitions matched |
| gate/compiled-new-declarations.log.gz | 18 new-module owned constants; 15 theorem constants |
| gate/inspect-count-audit.py | Exact inspector source that produced the successful record |
| artifact-manifest.json and SHA256SUMS | Complete byte inventory with canonical packet-relative paths and no hash cycle |

Compressed logs retain the complete original bytes, including empty final tab
fields. The genuine start receipt and prepared-inspector snapshot remain
historical records. The actual terminal records establish this acceptance.

## Exact source and review chronology

- Code: `31f8046291f2428e839d95e8890c8342858ec210`
- Tree: `e38c3f65efb79fa72860d8ef222e96695847a551`
- Actual parent: `38d93a8f25df7579a688ffc3cd7cfa8c36cfa754`
- PR: #560, `research/c4-finite-cut-count` in the initial snapshot

The implementation already existed when this verification work began.
The archived literature review is explicitly a **postimplementation
contract/literature audit**, with GO for unchanged verification. It is not
a pre-code gate. Earlier proposed count plans are not retroactively
relabelled as a fresh targeted pre-code review. The original report at this
code revision is retained separately from the later review.

`source-manifest.json` binds 134 committed source/configuration
records, including every one of the 130 start-receipt
hashes, to the exact code revision. The recorded working bytes matched the
Git objects. `source-inventory.json` is the root's source-only inventory,
not a compilation result.

## Finite contract

The generic module counts original integer Parikh vectors at proper
reduction-factor starts. Nonempty top factors make ordinary prefix lengths
strictly increase, giving injectivity and exact cardinality of the finite
image. Complete balanced reduction supplies full top and bottom marks at
those same vectors. A uniform upper bound on factor physical length gives
the finite count inequality by additivity; positive letter weights place
the vectors in the original half-open physical strip.

The named module uses actual power-`12*n` words, exact whole-word physical
scaling and strict-carrier closure. For a fixed finite strict carrier and a
fixed open neighborhood of its represented `CutPair` overlap, one threshold
captures the images of every counted original integer vector, uniformly
over all sources in the carrier and all later generations. The ambient
image is used for membership only; its cardinality is not substituted for
the original integer count. The carrier bound `L` remains an explicit input.

## Source inventory and controls

| Module | Public theorems | Private proof helpers | Definitions |
| --- | ---: | ---: | ---: |
| `StrictCutCount` | 7 | 2 | 2 |
| `NamedCutCount` | 2 | 1 | 1 |
| Total | 9 | 3 | 3 |

There are **12 explicit named proofs: nine public theorems and three private
helpers**, plus three definitions. Source proof-bank totals are 126 claims,
2,705 named Lean proofs and 411 source openings. These are source counts,
separate from the eventual global and module-owned compiled inventories.

The existing public controls cover repeated factor labels and an empty
factor list. The repeated-label sample exercises the generic nonempty-top
injection and is not claimed to be a balanced reduction. The interface and
literature reviews explain empty, erasing, zero-length, nonpositive-weight
and terminal-endpoint boundaries. Other discussed counterexamples are
contract analysis, not newly compiled control declarations.

## Retained records and their scope

| Record | Scope |
| --- | --- |
| `gate/process-start-snapshot.json` | Genuine nonterminal start receipt; copied while running |
| `gate/start-snapshot-provenance.json` | Capture time, exact receipt bytes and root-reported session identity |
| `gate/runner.py` | Exact guarded runner; unchanged checker, separate 20-second heartbeats and raw child log |
| `gate/inspector-prepared.py` | Prepared inspector source; its presence makes no audit-pass claim |
| `review/initial-pr-snapshot.json` | Original PR body and initial hosted observation; focused-compile statements remain attributed assertions |
| `review/semantic-interface-audit.md` | Read-only semantic review at the code revision |
| `review/postimplementation-literature-audit.md` | Post-code six-source contract/literature audit with chronology qualification |
| `review/original-report-at-code.md` | Exact committed report before later documentation clarification |
| `review/environment.json` | Toolchain/resource inventory and development-versus-isolated-gate plan |
| `source-manifest.json`, `source-inventory.json` | Committed-source identities and explicit declaration inventory |

The initial snapshot returned 76 queued checks and no hosted success. It
contains no explicit retrieval timestamp and is not a current-status
report. The prior focused compilation used retained artifacts and appears
only as an assertion in the original PR body; it does not replace the full
isolated gate. The complete isolated compiled audit passed. Its actual terminal process,
complete raw log and independently inspected declaration records are in gate/.

## Recorded source and governance checks

The exact `checks/` logs and process receipts record three successful checks
at the subject revision: all six governance checks, all 32 generated ledger
surfaces, and the 126/2705/411 proof-bank source inventory. These are
read-only consistency checks and do not establish the isolated Lean gate's
terminal result or compiled declaration inventory. They were run by the
root and copied here without rerunning them.

## Required gate and finalization

From the exact checkout, the required command remains:

```bash
ELAN_HOME=/workspace/scratch/84c835820757/toolchains/elan \
PATH=/workspace/scratch/84c835820757/toolchains/elan/bin:$PATH \
TMPDIR=/workspace/scratch/f96c28a561ad/count-isolation-tmp \
./tools/check_lean.sh
```

The unchanged checker prepares fresh source/configuration only, verifies
the pinned Lean/Lake release and freshly provisioned dependencies, uses the
fixed upstream Mathlib source-hash cache, compiles the full project and
audits local declarations. Locally retained compiled artifacts do not enter
acceptance. Allowed standard axioms are `propext`, `Classical.choice` and
`Quot.sound`.

The root-owned invocation completed with real exit zero and unchanged HEAD,
tree and recorded sources. The terminal records and exact byte hashes are
listed in gate/README.md and receipt.json. Finalization ran no compiler or test.

Full raw output and extracted declaration lines are archived as deterministic
gzip streams preserving all original bytes and trailing empty tab fields. `SHA256SUMS` pins every other packet file exactly once
with `./` paths. The artifact manifest excludes itself and `SHA256SUMS`;
artifact bytes, manifest and checksum generation therefore have no cycle.
The start snapshot remains a historical nonterminal receipt after any
eventual finalization.

## Remaining boundaries

No integer lattice upper count, lattice occupancy finiteness, all-depth
cylinder normalization, actual chart covolume, regular outer-cover measure
assembly or positive Haar measure is established here. A separately
exported positive carrier maximum and a divergence adapter are not part of
these public contracts. No M1, C4, overlap-positivity or PSC status is
promoted. Independent human review remains separate validation debt.

## Proposed following increment

`future/cell-packing-literature-review.md` is a preimplementation research
design review for a later anisotropic fundamental-cell packing argument.
It is separate from this increment's postimplementation contract audit.
The future note contains a proposed argument and explicit hypotheses; it
adds no Lean declaration, compiled acceptance or current positivity claim.
Its attributed correction distinguishes a bounded product-order interval's
upper-face ambiguity from coordinatewise half-open cell ownership. The
corrected review is preserved exactly. Current code and source-bound gate
remain unchanged.

The [mathematical route review](future/cell-packing-route-review.md) is
preserved beside the [future literature review](future/cell-packing-literature-review.md).
Both concern a proposed, uncompiled following step; neither extends the
current finite-count theorem or supplies a current positivity claim.
