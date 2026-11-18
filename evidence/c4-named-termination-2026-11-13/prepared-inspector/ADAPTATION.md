# Prepared hosted termination evidence inspector

This directory contains a source-only successor of the retained hosted
strict-exclusion inspector. **It does not contain a successful hosted artifact
inspection or mathematical acceptance receipt.** Its Python tests calibrate
the nine-proof evidence contract and refusal paths. They do not run Lean.

## Candidate and predecessor

The current static metadata binds the clean candidate commit
`6021f042056d3cb0f9717d2488144339721c2071`, tree
`3355716258114a4f5353b10233fa1fa79bb34bbd`. It explicitly disclaims compilation,
hosted acceptance, and independent human review. The inspector compares the
metadata's revision, tree, path set, source hashes, toolchain, and declarations
against the exact clean checkout supplied at inspection time.

The predecessor is the retained
`termination-hosted-inspector-review/inspect-hosted-named-exclusion-audit.py`.
Its SHA-256 and the exact successor, test, and metadata hashes are recorded in
`preparation-tests-receipt.json`. `inspector-change.diff` contains the complete
adaptation for review.

## Contract changes

| Contract | Prepared successor |
| --- | --- |
| Concrete semantic proofs | Nine: all earlier seven, plus `seed_terminates` and `reachable_terminates` |
| Termination fixture results | Requires `seed_and_reachable_termination_fixtures == [0, 1]` |
| Replay source manifest | Exactly the candidate producer's 25 paths, including both Words modules, both Data modules, and the finite-productivity/forward-carrier chain |
| Static source metadata | Exactly 35 unique paths: all 26 predecessor paths plus the nine added proof sources |
| Explicit module inventory | Exactly five source-path/module identities |
| Explicit declarations | Exactly 41 identities: 37 theorems and four definitions |
| Full-log fixture acknowledgements | Requires each new geometry, exclusion, and termination marker once, after the global audit acknowledgement |
| Wrong-type controls | Retains both old checks and independently requires each new endpoint's flag, exact isolated audit source, and its own intended type-mismatch diagnostic |
| Compiled objects | Explicitly requires nonempty retained `lean/Source0.olean`, `lean/Source1.olean`, and the wrong-type fixture's `Source0.olean`; records generated object digests |

The declaration inventory retains the previous 12 declarations and adds nine
from `FiniteProductivity`, six from `NamedFiniteProductivity`, and 14 from
`NamedForwardCarrier` (12 theorems and two definitions). There is no fixed
compiled-library declaration count. The complete named-proof expectation is
derived from the exact candidate proof bank; this candidate contains 3,597
named proofs. The compiled counts and global acknowledgement must come from
the retained hosted log and the candidate's unchanged proof-bank parser.

The metadata helpers exposed for preparation and review are
`EXPECTED_DECLARATIONS`, `EXPECTED_MODULE_PATHS`, `REQUIRED_METADATA_PATHS`,
`metadata_source_records`, and `declaration_inventory`. Missing, duplicate,
extra, privately renamed, misowned, or wrong-kind required declarations refuse
inspection. Missing `module` fields also refuse; the initial metadata draft's
omission was corrected before the recorded test run.

An isolated endpoint log cannot earn credit for a different endpoint's error
or for a combined log containing both termination endpoints. The existing
unresolved-name rejection remains in force. The tests also require the prior
control source files and logs, so adding the two endpoints does not replace
the earlier obligations.

## Preserved acceptance gates

The predecessor's raw GitHub run/job/attempt checks, successful critical-step
requirements, exact clean revision/tree binding, file manifest and stability
checks, complete compiled proof-bank parsing, original graph/address oracle
binding, all 32 native mutation controls, exact eight-test oracle transcript
recognition, and genuine final replay-summary equality remain in place.

The AST comparison in the test receipt confirms that all 13 pre-existing
helper functions/classes are unchanged. Only `inspect` and `main` are adapted;
no predecessor function is removed. Added helpers separate the extended
contracts for focused refusal testing. The successor imports only exact
verified candidate tooling. It neither imports artifact code nor calls the
candidate replay's process-launching function.

## Test evidence

`tests.log` and `preparation-tests-receipt.json` retain a terminal exit-zero
run of 21 focused Python tests, with numerous individual mutation subcases.
The inspector, test source, and corrected candidate metadata remained
byte-identical across that run. Tests cover:

- Rejection of the old seven-proof protocol even when new result flags are added.
- Omission of each semantic proof and incomplete/wrong termination fixture lists.
- Omission of each of the 35 metadata paths and each of the 41 required static or compiled declarations.
- Exact agreement with the candidate's 25-path replay source list and its 37 relevant named proofs.
- Missing, duplicate, private, misowned, wrong-kind, and missing-module metadata.
- Independent endpoint control flags, exact sources, missing/swapped/unrelated/combined diagnostics, and unresolved-name failures.
- Retention of the earlier controls and refusal of nonterminal, failed, wrong-head, wrong-attempt, or unsuccessful-step hosted metadata.

Synthetic audit rows, diagnostic strings, and nonempty object placeholders
exercise parser/presence conditions only. No complete synthetic hosted
artifact is accepted by these tests. They do not authenticate Lean object
contents or establish a theorem.

Run the tests with:

```sh
python3 test_prepared_inspector.py
```

The defaults use the prepared clean checkout and metadata paths. To relocate
them, set `PSC_INSPECTOR_CANDIDATE_ROOT` and `PSC_INSPECTOR_SOURCE_METADATA`.

## Eventual hosted inspection

Only after the relevant run and job complete successfully, invoke the script
with the extracted artifact root, raw REST run/jobs JSON, this exact source
metadata, and the clean candidate checkout. Supply full expected commit/tree
and the exact run ID explicitly. The command interface remains the same as
the predecessor; output schemas are now
`c4-hosted-concrete-termination-inspection-v1` and its refusal counterpart.

The supplied raw run/jobs metadata and extracted-content manifest do not by
themselves bind a GitHub artifact ID or its downloaded ZIP digest. The
inspector preserves that explicit limitation in `artifact_identity`; retain
the raw GitHub artifact metadata, requested artifact ID, archive digest, and
download/extraction provenance separately. Do not infer this missing transport
binding from the inspector's content checks.

Successful future inspection would concern strict-system exclusion for
arbitrary finite carriers of the two named literal substitutions, and the
existing coincidence-termination predicate for all six ordered swap seeds
and their actual terminal-child descendants. It would not cover arbitrary
unlisted starting blocks, prove that every possible path terminates, or
establish general C4 or PSC.
