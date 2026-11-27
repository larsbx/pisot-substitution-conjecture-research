# Integration of canonical-measure uniqueness with current main

## Status and revisions

**Status:** the literal-family uniqueness and spectral-transport proof is
repository-proved at the source-bound scope of the
[proof note](c4-family-canonical-measure-2026-11-23.md); independent human
review remains pending. The requester authorized opening a pull request
against `main` and merging it on 23 November 2026.

The approved local review commit is
`f88d89d9e5e3ae68a2125f8ecc7e1138016e536f`, based on PR #653 head
`ce52d46bc4706fd2c15ddd3bb345f6e2067f49cd`. Current main was fetched at
`b479faf1677e891d658ba24fd2aa654ddc5948ce`, incorporating the zero-fibre
anchor proof and corrected origin-cycle census from #652. Publication
through the connected GitHub API preserves the exact trees of the local
proof and acceptance checkpoints. The API assigns publication commit IDs;
the pull-request record binds those IDs to the checked local tree hashes.

The new pull request includes the symbolic-spectrum dependency from #653
and the canonical-measure follow-up. No theorem source from either the
approved follow-up or current main requires a conflict resolution. The
three canonical modules and their audit remain byte-identical to the
approved local source. The original symbolic endpoint remains unchanged.

## Integration changes

The merge combines the root Lean imports, both append-only note histories,
and all family-gate obligations. Generated proof-bank files are regenerated
from the combined source inventory. In particular, the gate preserves
main's `C4ParameterFamilyOriginCycle` build and its fourteen distinct
standard-axiom checks, alongside the original symbolic audit and the new
canonical audit.

The origin-cycle test on main supplied its `require_contract` argument as
adjacent quoted literals. The governance scanner recognizes a single
literal argument, so the split spelling made the successful native test's
receipt appear undeclared. Joining the literals preserves the exact
runtime contract bytes, assertions and native behavior. No vendored
scanner or mathematical kernel is changed. Existing roadmap surfaces are
updated to describe the proved symbolic endpoint and probability equality
at their actual scope.

## Verification boundary

The [initial acceptance packet](../evidence/c4-canonical-measure-2026-11-23/README.md)
is preserved as historical evidence for its recorded source commit. Its
87-module, 12-fixture acceptance is not represented as acceptance of this
new integration. The combined gate additionally checks the origin-cycle
audit inherited from main.

Hosted acceptance must bind the new pull request's exact head and tree.
The family workflow checks out that head explicitly, builds an isolated
source copy, checks dependency pins, runs all retained audits and uploads
the source identity with its terminal log. The origin-cycle audit is read
from `evidence/c4-zero-fibre-anchor-proof-2026-11-22/OriginCycleAxioms.lean`;
that input must be included when recording the integrated gate's source
digests. Full-repository checks and the separate Physical Mass workflow
retain their own outcomes.

Replay from the repository root:

```sh
python3 tools/make_proof_bank.py --check
tools/check_c4_parameter_family.sh
PYTHONPATH=tools python3 -m claim_governance.cli --root .
python3 -m pytest tests/test_proof_bank.py tests/test_recorded_data_integrity.py
python3 tools/check_markdown_source.py
git diff --check
```

## Scope retained

For every `k >= 2`, every invariant Borel probability on the actual literal
two-sided legal shift equals `wordMeasure`; explicit equality transports
the original complex L2 closed eigenvector-span theorem. A separate
frequency-defined canonical measure, general primitive-substitution unique
ergodicity, physical variable-roof disintegration and a `k = 1` extension
are not introduced. The universal PSC, BH, residual A1-prime and general
C4 claims retain their separate obligations.
