# Canonical packet inspection and controls

See [the complete report](../../docs/c4-overlap-canonical-packet-audit-2026-11-06.md)
for hypotheses, exact-revision scope, reconstruction commands and four remaining
geometric/measure bindings.

- `provenance.json`: independently inspected revision/run/artifact identity.
- `inspection.json`: all source/log/auditor/hash checks and fresh full Python
  reconstruction, including measured runtime. No fresh local Lean run.
- `hosted-packet-receipt.json`, `hosted-oracle-receipt.json`: retained hosted
  receipts at `40e5ecf3`, not a claim about this follow-up revision.
- `hosted-generic-audit.log.gz`: complete hosted generic build/axiom audit log.
- `Source0.lean.gz`, `Source0.log.gz`, `Audit0.lean.txt`: complete representative
  generated proof source, independent expected-type auditor and its full
  declaration/axiom/packet log. `payload-manifest.json` pins uncompressed bytes.
- `wrong-proof-type-control.json`: the real Lean fixture compiles but its
  independent expected-type audit refuses it.
- `mutation-tests.txt`: eleven local tests, including genuine source-0 packet
  mutation controls and the existing synthetic audit-protocol controls.
- `class-oracle-tests.txt`: independent class-oracle regressions.

The artifact ZIP's SHA-256 matches GitHub's recorded digest. Full compiled
modules and all-source logs remain in the linked hosted artifact; no compiled
`.olean` is vendored into the repository. Recreate them through the canonical
pinned importer/kernel gate. Standard compiler/source provenance is still a
trust input. No general theorem is promoted and no PR is merged.
