# Even rank-two investigation: local evidence

Base revision: `c0231e0fd64d9eee7f7bb798042d9966276e4cd6`.
Date: 2026-11-19. This packet belongs to the local proposed change; it is not
hosted acceptance and makes no claim about a later remote branch.

## Accepted scope

The three final target modules build successfully. Their complete local
import closure has **21 modules and 474 source-named proofs**, including
**49 new named proofs**. The compiled audit checks **1,088 declarations**,
of which **787 are theorem declarations** after including generated helpers.
Only `propext`, `Classical.choice` and `Quot.sound` occur as axioms.
The source-to-audit coverage and all 35 bound files verify.

The proposal proves a uniform literal family exclusion and nilpotent-solenoid
halving, checks the finite ternary seam coefficients, and classifies the
original eventual-range shapes of the existing finite controls. Uniform
PIP membership and graph/cohomology interpretations are written arguments.
The general even-determinant exclusion, universal C4 and PSC remain open.

## Accepted records

| Record | Scope |
| --- | --- |
| `baseline.json` | Exact inspected main, PR head/merge revisions, and the observed queued baseline workflows; no candidate hosted checks. |
| `pin-verification.log` | Lean release and every installed Lake dependency agree with the pinned source revisions. |
| `strict-core-build.log` | Byte-preservation bindings and successful compilation of the canonical strict-system core. |
| `core-extraction-check.log` | Both moved blocks and all remaining original bytes verify against the exact Git baseline. |
| `lean-final-build.log` | Successful final family, seam and solenoid target build: 2,206 dependency jobs. |
| `lean-audit.log.gz` | Every declaration and axiom receipt in the compiled focused closure, losslessly gzip-compressed to retain empty final TSV fields. |
| `audit-verification.log` | Complete source/module/proof coverage, 35 source bindings, and all 49 new named proofs verify. |
| `repository-checks-final.log` | Final generated-inventory, ledger, governance, Markdown/source and proof-bank test receipts. |
| `source-bindings.json` | SHA-256 bindings for the focused local closure, audit entry point, toolchain pins, executable changes, extraction verifiers and retained StrictSystem source. |
| `audit-expected.json` | Source-derived list of the 21 modules, 474 named proofs and 49 new named proofs. |
| `verify-audit.py` | Administrative verifier for source hashes, compiled receipts and complete source-to-audit coverage. |
| `verify-core-extraction.py` | Administrative check of the canonical extraction against the immutable baseline. |
| `baseline-residue.log` | Replay of the existing #619 control before the shape extension: 96 specimens and 288 letter pairs. |
| `mojo-family.log` | Canonical Mojo family replay: 16 even parameters, 48 pairs, odd-parameter and bounded-refusal controls. |
| `python-family.log` | Initial independent Python family and original-shape replay. |
| `python-family-final.log` | Same replay after clarifying the oracle docstring's optional corpus imports. |
| `residue-shapes.log` | Extended canonical #619 replay, preserving all old witnesses and adding the six original-graph shape counts. |

The family Python arithmetic/word check imports no PSC implementation. Its
optional shape census reuses the existing independent Python corpus and
Anderson–Putnam legal-language enumerator. Both remain independent of the
canonical Mojo implementation. The standing corpus exhausts the three-letter
PIP substitutions with nonempty image lengths at most three.

## Canonical core extraction

`StrictSystemCore.lean` contains the original 299-line definition/cut-pair
block and 98-line witness-helper block without changing their declarations
or proof bodies. There are no private declarations in these blocks. The
remaining `StrictSystem.lean` is byte-for-byte unchanged after replacing its
`Descendants` import with `StrictSystemCore`. Public names are preserved;
there is no duplicate or alternative definition of a strict system.

This isolates the literal theorem from the original module's unrelated sector
and spectral imports. The core compiled in 21 seconds; the family bridge then
compiled in 3.5 seconds. The focused audit uses the actual canonical core.
The full legacy sector aggregate and repository-root Lean library were **not**
rebuilt. Their unchanged remaining source is bound and mechanically compared,
not described as newly compiled. Hosted checks remain a separate requirement
before merge.

## Historical incomplete attempts

These records are retained but do not count as final acceptance:

- `lean-build.log`: an aggregate replay before extraction, with completed
  dependencies but no final completion receipt.
- `lean-sequential-build.log`: the sequential diagnostic replay; `Basic`
  completed, while the later attempt was stopped before extraction.
- `lean-resource-monitor.log`: observations from that diagnostic replay.
- `source-bindings-pre-extraction.json` and `audit-expected-pre-extraction.json`:
  the original larger source snapshot and planned closure (47 modules and
  1,523 named proofs), superseded by the canonical extraction.
- `repository-checks.log`: the first final-check attempt; generation,
  ledger and governance passed, but pytest did not produce a completion
  receipt before the execution sessions became unavailable.

No recorded proof failure is silently turned into a success. The final
compiled acceptance is solely `lean-final-build.log`, `lean-audit.log.gz`,
`audit-verification.log`, the extraction checks and the later completed
repository/integrity receipts.

## Toolchains and build provenance

- Lean `4.34.0-rc2`; Lake `5.0.0-src+6a10ac8`.
- Pinned mathlib revision `4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`.
- Mojo `1.1.0.dev2026090805 (34562fa1)`.
- The current and reused installed Pixi lockfiles have identical SHA-256:
  `1515f7300f49ad6b5e263a9bc02a8ec041123ce455b28fd24c440022824b2ff8`.

The new checkout started without compiled local project modules. Pinned
upstream artifacts were reused from installed local runtimes; local modules
were compiled from this checkout. Interrupted attempts retained completed
source-matched artifacts. The final target build uses `--no-cache` and
`LEAN_NUM_THREADS=2`. This is a local source-bound focused replay, not the
repository's isolated hosted periodic-partner gate or a full-root build.

The Mojo commands use an installed Pixi environment and explicitly change
into this checkout's `kernel` before invoking Mojo. Imports therefore come
from the proposed source. The equivalent portable commands follow.

## Replay

From the repository root:

```sh
python3 oracles/python/even_companion_family.py --corpus-shapes
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_even_companion_family.mojo)
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_even_stack_residue.mojo)
(cd proof/PscVerif && LEAN_NUM_THREADS=2 lake --no-cache build PscVerif.EvenCompanionFamily PscVerif.EvenSeamCycles PscVerif.PeriodicPartnerEvenSolenoid)
(cd proof/PscVerif && lake --no-cache env lean EvenRankTwoAudit.lean > /tmp/psc-even-rank-two-audit.log)
python3 evidence/even-rank-two-2026-11-19/verify-audit.py --audit-log /tmp/psc-even-rank-two-audit.log
python3 evidence/even-rank-two-2026-11-19/verify-core-extraction.py
python3 tools/make_proof_bank.py --check
python3 tools/make_ledger.py --check
PYTHONPATH=tools python3 -m claim_governance.cli --root .
python3 -m pytest tests/test_markdown_links.py tests/test_check_markdown_source.py tests/test_proof_bank.py tests/test_recorded_data_integrity.py
sha256sum -c evidence/even-rank-two-2026-11-19/SHA256SUMS
```

Keep new replay logs outside this immutable recorded packet. Generated helper
theorems are audited but are not counted among the 49 new named proofs.

## Verification boundary

The formal statements use the actual repository literal words, strict systems
and realization solenoid. The elementary integral-cycle decomposition,
geometric winding interpretation, stack/covering theorems, eigenfunction
saturation, and uniform Pisot-root argument remain written or published inputs.
No new hosted acceptance or arbitrary nilpotent-cubic exclusion is asserted.
