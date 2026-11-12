# Original archived C4 payload import: evidence boundary

This packet preserves development checks and failed attempts for the
[concrete payload import](../../docs/c4-archived-payload-import-2026-11-12.md).
It starts from merged #550, revision
`06dac7ea4e83a6b5a2c7c36bfe84cfec75da3903`. Historical packets and their
checksums are unchanged.

## Acceptance rule

The authoritative concrete acceptance is the successful **Original C4
archived payload Lean import** workflow on the exact reviewed commit and
tree. Its artifact is named `original-c4-payload-<head-sha>`. The PR records
the accepted revision and run IDs. A different revision, an unfinished run,
one fixture, generic compilation or native agreement is not interchangeable
with that acceptance.

The artifact retains:

- Exact commit/tree and original archive checksum.
- Canonical locked-Mojo native test log, full original payload, independent
  oracle tests and mutation receipt.
- The complete isolated Lean source build and compiled project axiom audit.
- Complete generated `Source0.lean` and `Source1.lean`, kernel compilation
  logs, fresh imported-module audits and all generated declarations' axiom
  sets.
- Typed checks of the actual `valid`, `accepted`, `typed_accepted`,
  `domain_iff`, `roots_null` and `ancestors_null` declarations.
- Lean's complete emitted payload, independent raw/decoded/search-tree
  replay and direct comparison with both original and #550 addressed graph
  digests.
- The compiled right-name/wrong-proof-type negative control.

The proof scope remains the original named rooted inverse domains and their
product-Haar nullity. The probability additive Haar assumptions remain
explicit. No all-strict-packet identification, positive root measure, C4 or
general PSC conclusion is recorded.

## Development results retained here

[development/receipt.json](development/receipt.json) binds all relevant
source hashes, pins and the native payload digest. The native tests replay
all 14,233 states and 69,679 positional slots and observe nine field and
eighteen semantic refusals. The eight independent Python tests use the
actual native output. The production oracle records 32 refusals, sixteen
per fixture; its ordinary and `python -O` receipts are byte-identical.

[development/lean-modules.json](development/lean-modules.json) records the
five new modules' successful local source compilation, with per-module
source and recursive source-closure hashes. These development builds used
the pinned compiler, genuine local project dependencies and the upstream
source-hash Mathlib cache. They do not replace the fresh isolated full-source
build or compiled axiom audit.

The local full Pixi installation could not download an unrelated
conda-forge package. For iteration, the exact Mojo and mojo-compiler package
digests from the unchanged lockfile were verified and extracted. A normal
prefix relocation repaired their scratch configuration. The hosted workflow
uses the complete locked Pixi environment, so this development fallback is
not substituted for hosted native acceptance.

## Preserved failures

[failures/attempts.json](failures/attempts.json) indexes the failed local
attempts and compressed logs. They remain failures:

- The full upstream cache omitted five source modules, including a deprecated
  `BigOperators` wrapper. The pinned sources were built before retrying the
  unchanged local project dependencies.
- Digit round-trip scripts required explicit branch inequalities after
  simplification; their statements and full-mark enumeration did not change.
- The core adapter required a closed denominator arithmetic goal,
  parentheses around a dependent `Fin` bound and explicit equality
  transport. The accepted file has no diagnostic admissions.
- Small controls needed explicit bounded indices and parenthesized record
  fields. The accepted twenty controls compiled with no diagnostics.
- The IO emitter initially used a reserved token as a local variable;
  renaming it repaired parsing.
- The first generated source opened two `Table` names and failed before
  concrete acceptance. Its full generated source and diagnostics are
  preserved as `failures/Source0.lean.gz` and
  `failures/Source0.compile.log.gz`. Fully qualified table constructors
  repair the exporter without changing the graph or packed payload.
- Initial scratch Mojo configuration failures are preserved separately
  from proof failures and do not count as mathematical tests.

`SHA256SUMS` contains every packet file other than itself, using explicit
`./` packet-relative paths. No historical manifest convention is changed.
