# BH finiteness bridge and A1′ tail-family evidence

## Scope and current acceptance

This packet accompanies the next source increment after PR #573. All five
new modules passed ordinary pinned local compilation, and both independent
exact-type audits passed. The source-isolated hosted gate and the unchanged
whole-library gate retain their own acceptance boundary; their final receipts
belong to the exact published commit recorded by each workflow.

| Local audit | Modules | Owned declarations | Theorems | Exact endpoints | Rejected controls |
| --- | ---: | ---: | ---: | ---: | ---: |
| BH finiteness and occurrence ancestry | 3 | 45 | 40 | 11 | 22 |
| A1′ literal coincidences and actual incidence arithmetic | 2 | 249 | 189 | 15 | 30 |
| Total | 5 | 294 | 229 | 26 | 52 |

The complete declarations of each new module, including generated helpers,
use only the established standard axiom allowlist. These are compiled results
at the stated conditional and family scopes, not a universal conjecture proof.

The public BH endpoint derives finite actual `ChildNC` reachability from a
finite packet set covering the actual seed overlaps, complete `InteriorStep`
closure, positive exact length scaling and a literal integral-zero hit from
every packet. It assumes neither a finite word carrier nor a factor bound.

The A1′ source covers two infinite `Z=3` boundary layers (including stated
arbitrary-middle variants) and the three `Z=4` run patterns. Its coincidence
endpoints concern actual iterated words and equal-Parikh prefixes. Shared
prefix and suffix functions give simultaneous coincidence for all three
letters at common depth seven for the two `Z=3` layers and depth four for
the `Z=4` patterns. The Pisot arithmetic is bound to the actual incidence
of the two `Z=3` layers. These results do not promote universal A1′, BH, C4
or PSC.

Derivation and primary-source screens:

- [BH bridge](../../docs/bh-finite-reachability-stop-go-2026-11-14.md)
- [A1′ tail reduction and ordered witnesses](../../docs/p1a-minimal-z3-tail-stop-go-2026-11-14.md)

## Accepted parent source

The full isolated parent build passed at commit
`6bf0b9704501eb763cbb4323c3fd1f939d6f11c8`, tree
`16856ab6885b091b971fdd30c9a800014073970c`:

- Run `43630544688`, job `132555946132`, attempt 1:
  <https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43630544688/job/132555946132>.
- 9,053 build jobs; compiled audit: 11,937 declarations, 7,819 theorems,
  all 3,822 named proofs in that exact source inventory reached.
- Original artifact `14129340218`, 112,748 bytes, SHA-256
  `ba4aae65ae9a52415fe8a1f740ebd2190ded21cf39346b2192cbf6846fcb5c7b`.
- The original ZIP contains only `c4-overlap-lean-audit.log`. Provider
  metadata binds its run and source head; the retained job-log excerpt binds
  checkout and terminal audit output. No nonexistent archive `source.txt`
  is claimed.
- The unchanged `make_proof_bank.check_audit` was replayed against
  `git show 6bf0b970:proof/proof-bank.json`. The parent inventory SHA-256 is
  `faaf07670393313033938dbf919c570aeb9bce5f64f296def82dc83c8a167d3a`.

The parent artifact was redownloaded after the executor reset and its exact
digest and audit were checked again. This acceptance belongs to the parent,
not to the new source. See `parent-573/` for original bytes, metadata and
the independently replayed counts.

## Development history

The old execution workspace disappeared during dependency compilation.
`local-history/` explicitly reconstructs known outcomes from returned tool
messages. It does not claim to contain original lost receipt files. In
particular, one unchanged `OccurrenceNewborn` build returned exit 0, the next
`OccurrenceAddress` session lost its terminal outcome, and the earlier
matrix-only arithmetic attempt returned exit 1 before its source correction.
No new BH source had been elaborated in that former workspace.

The restored checkout starts from the exact published parent. New source
files were reconstructed from recorded edits. The pinned setup completed
successfully and cloned the unchanged manifest revisions. The shared
dependency build passed 2,196 jobs. Subsequent local development logs and
terminal receipts are in `development/`. Failed elaborations, cached
development passes, final ordinary compilations and independent endpoint
audits retain separate receipts; none substitutes for the source-isolated
hosted acceptance gate.

The rejected local Mojo calibration was not retried. Automatic approval
review rejected that environment because it might transmit a locally stored
identifier in compiler telemetry. Exact finite arithmetic used to discover
positive addresses is described in the A1′ note; it is not a proof receipt.
Lean checks of literal word factorizations supply the acceptance criterion.

Two original failed witness logs and the timestamped parent job excerpt
contain significant retained whitespace. They are stored as deterministic
`.gz` files, with exact original and stored hashes in
`lossless-log-transport.json`. Decompression was checked byte for byte.
Original terminal receipts and the historical index keep their original
log paths; the transport manifest maps those names to the lossless stored
files. No compiler diagnostic was trimmed or rewritten to pass a source
whitespace check.

## Replay

```sh
./tools/setup_lean.sh
export PATH="$HOME/.elan/bin:$PATH"
./tools/check_bh_a1_progress.sh
./tools/check_lean.sh
```

The focused gate copies source and configuration only, checks pinned
dependencies, disables caller Lake caches/configuration, obtains the fixed
upstream Mathlib source-hash cache, and compiles the new module dependency
closure. Its two audits compare independent literal endpoint types, verify
module ownership, inspect every declaration owned by the five new modules,
and reject wrong-type and missing-declaration controls. The only permitted
axioms are `propext`, `Classical.choice` and `Quot.sound`.

The unchanged full proof-bank gate remains a separate whole-library check.
The hosted focused workflow records both commit and tree before compilation,
rechecks the source afterwards, and retains the terminal log even on failure.

## Boundaries retained by the controls

The `021/120` control is a genuine irreducible balanced pair with physically
aligned middle tiles and nonzero integral displacement. It refutes dropping
the integral-zero target without an additional independence argument.
The `j=3` arithmetic control has a unit-circle root, preventing removal of the
first-two-layer guard. Existing identity and non-Pisot productivity controls
continue to separate finiteness, coincidence productivity and the universal
Pisot problem. All 126 governed claim statuses remain unchanged.
