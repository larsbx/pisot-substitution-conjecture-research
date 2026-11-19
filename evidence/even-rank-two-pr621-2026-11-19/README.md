# Even rank-two investigation: integration with PR #621

Research base: `c0231e0fd64d9eee7f7bb798042d9966276e4cd6`.
Previously verified local checkpoint: `dc4f2723cd4f8313a20b387ca7c9fbcb6f2401c6`.
Integrated main: `017969364269c116aaa5873bfcba6c9f1b1ba7e5`.
PR #621 head: `d50ca9dacb9beb2b6b6a90b35c8c14482597bb25`.

Main advanced during review preparation. This packet records the affected
build, compiled axiom audit and repository checks after integrating #621's
target topology. The [earlier packet](../even-rank-two-2026-11-19/README.md)
is preserved unchanged at the previously verified checkpoint; its finite
controls remain applicable because their source and dependencies did not
change in #621. Neither packet claims hosted candidate acceptance.

## Accepted formal scope

The three focused targets build successfully. Their complete local import
closure contains **21 modules and 483 source-named proofs**, including the
same **49 new named proofs**. The compiled audit checks **1,106 declarations**,
including **804 theorem declarations** with generated helpers. It accepts
only `propext`, `Classical.choice` and `Quot.sound`. All 35 source bindings
and source-to-audit coverage verify.

The focused build recompiled the changed `PeriodicPartnerHull` and
`PeriodicPartnerRealization` modules and `PeriodicPartnerEvenSolenoid`.
The family and seam targets retained valid, unchanged source-matched
artifacts. All three targets completed in the 2,206-job dependency graph.
The unchanged canonical core extraction is verified against both inspected
main revisions. The full legacy sector aggregate and root Lean library
were not rebuilt; the focused closure does not include
`PeriodicPartnerRealizationModels` or purport to replay all of #621.

## Records

| Record | Scope |
| --- | --- |
| `revision-context.json` | Exact revisions and scope of this integrated replay. |
| `integration-checks.log` | Both baseline strict-system sources are identical; finite executable sources are unchanged; the 397-line canonical extraction verifies. |
| `lean-build.log` | Successful focused build after integrating #621. |
| `audit-run.log` | Exact audit command and successful exit. |
| `lean-audit.log.gz` | Lossless compiled declaration/axiom receipts; empty final TSV fields are preserved. |
| `audit-verification.log` | Exact source bindings, complete module and named-proof coverage, and accepted axiom dependencies. |
| `audit-expected.json` | Source-derived inventory of the 21 modules, 483 named proofs and 49 new named proofs. |
| `source-bindings.json` | SHA-256 bindings for the current focused sources, executable controls, audit, verifiers and toolchain pins. |
| `verify-audit.py` | Administrative source/audit coverage verifier. |
| `repository-checks.log` | Generated inventories, ledger, governance, Markdown/source and proof-bank test receipts. |

The earlier packet supplies unchanged finite replay: 16 even family
parameters and 48 pairs, the odd-parameter and failed-template controls,
the 96 short-image specimens and all 288 pair witnesses, and the six
original-range shape counts. Its source bindings match this packet.
Lean, mathlib and Mojo pins also remain unchanged.

## Topology and mathematical boundary

PR #621 establishes compact Hausdorff topology of the target, a shift
homeomorphism and joint target-flow continuity. The new halving theorem
uses the same algebraic solenoid. It does not prove continuity from the
ordinary tiling hull, continuity of desubstitution, normalized BBK/MEF
identification, recognizability, finite fibres or BDS periodicization.

The new unbounded word and literal strict-system theorem is independent
of those geometric hypotheses. Uniform Pisot membership, integral graph
decomposition and cohomological interpretations remain written arguments.
The arbitrary even-determinant rank-two obstruction, C4 and PSC remain open.

## Replay

From the repository root, with the pinned runtimes on PATH:

```sh
(cd proof/PscVerif && LEAN_NUM_THREADS=2 lake --no-cache build PscVerif.EvenCompanionFamily PscVerif.EvenSeamCycles PscVerif.PeriodicPartnerEvenSolenoid)
(cd proof/PscVerif && lake --no-cache env lean EvenRankTwoAudit.lean > /tmp/psc-even-rank-two-pr621-audit.log)
python3 evidence/even-rank-two-pr621-2026-11-19/verify-audit.py --audit-log /tmp/psc-even-rank-two-pr621-audit.log
python3 evidence/even-rank-two-2026-11-19/verify-core-extraction.py
python3 tools/make_proof_bank.py --check
python3 tools/make_ledger.py --check
PYTHONPATH=tools python3 -m claim_governance.cli --root .
python3 -m pytest tests/test_markdown_links.py tests/test_check_markdown_source.py tests/test_proof_bank.py tests/test_recorded_data_integrity.py
sha256sum -c evidence/even-rank-two-pr621-2026-11-19/SHA256SUMS
```

Keep later replay logs outside this immutable packet. The final review
manifest records the exact candidate and the separate recorded-data-integrity
receipt without changing the files whose checksums are being tested.
