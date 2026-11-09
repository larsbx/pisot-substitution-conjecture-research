# Lean packet binding validation

This directory records development of the concrete-data replay gate, separately
from the generic inference evidence at `../c4-overlap-lean-2026-11-05/`.
No theorem status or proof-ledger dependency is changed. Draft PR #500 remains
unmerged by this work.

## Completed finite pilot

`source0-pilot.json` records kernel acceptance of source 0, including the typed
certificate proof and an audit of every generated logical declaration: 2,564
declarations / 1,539 theorem declarations, only standard axioms. Lean's complete
emitted packet is byte-for-byte equal to the independent Python reconstruction:
15,824 vertices, 78,333 occurrence edges, canonical packet SHA-256
`721f0bcbca2f91d1a7e1613751f446defa7ad85b0316bfe391faeb401d85ccef`.
This is one source, not the 18-source class. The full generated source is
reproducible from the Mojo exporter; its SHA-256 is recorded in the receipt.
`source0-axioms.log.gz` retains every generated declaration's transitive axiom
set and the completion counts. The packet itself is reproducible from the
already committed native class receipt and independent oracle.

The pilot used the development Lean cache and the generic module immediately
before addition of the `false_layout_refused` control. The exact generic source
is retained in `source0-generic-module.lean.gz`; computational definitions and
soundness proofs are identical to the final source. This pilot is separate from
the isolated generic acceptance gate and from exact-head hosted full-class
acceptance. It does not infer geometric coverage or Haar scaling.

## Final local scope

| Source | Prefix cycle | States | Occurrence edges | Kernel / typed / axiom checks | Full packet parity |
|---|---:|---:|---:|---|---|
| 0 | 2 | 15,824 | 78,333 | Passed | Exact |
| 12 | 3 | 15,891 | 78,288 | Passed | Exact |

Both pilots were re-audited with independent expected-type checks and direct
`Packet.emit packet` emission after the harness hardening. Source 12's original
complete single-source replay was followed by that independent re-audit; the
emitted packet was unchanged. Its compiled model came from a hard-linked
snapshot of the freshly cloned, pinned and compiled isolated project, sharing
read-only compiler/cache pages to avoid the earlier paging problem. Source 0's
earlier generic source variant is retained as described above.

`source12-pilot.json` records its period-three source, source/data hashes, axiom
counts and full oracle equality. The two `source*-axioms.log.gz` files retain
every generated declaration; `source*-independent-audit.lean.txt` retain the
actual independent type assertions and emission entry points. Each generated
module audited 2,564 declarations / 1,539 theorem declarations. The source data
and full packets are deterministically reproducible from the canonical exporter.

The clean full-project build and original exhaustive audit passed: **531
declarations, 275 theorem declarations, all 106 named proofs**, with only the
three standard axioms. `generic-validation.json` and the compressed original
log record this. The original auditor's scan materialized all Mathlib constants
and was slow. `ProofBankAudit.lean` now visits each PscVerif module's owned
logical constants directly. Replaying the replacement auditor against the same
freshly compiled project reached **exactly the same 531 complete declaration
rows**, including names, module ownership, proof/definition kinds and axiom
sets. `owned-module-audit.log.gz` preserves that independent replay. Library
sources were unchanged between these audits; the full isolated compilation was
not repeated for the audit enumeration change.

All-18 concrete Lean acceptance is **pending**, including sources 13, 15 and 16
of period three. These pilots do not stand in for the complete class. The new
exact-head hosted workflow requires all 18 after the isolated full-project gate.
No full-class Lean receipt or mathematical promotion is issued locally.

## Replay

See [the binding document](../../docs/c4-overlap-lean-packet-binding-2026-11-05.md)
for the complete isolated command and source/refinement boundaries. A budgeted
development replay after provisioning the pinned project is:

```sh
python tools/replay_overlap_lean_packets.py \
  --exporter /tmp/c4-overlap-lean-export --project proof/PscVerif --root . \
  --output /tmp/c4-source0-pilot --source 0
```

Each output directory must be fresh. The default command omits `--source` and
requires all 18 sources before issuing a class receipt. The hosted workflow
always runs that complete gate, after the clean full-project source/axiom audit.
Generated sources, fresh `.olean` files, all audit/packet logs and parity receipts
are retained in the workflow artifact. An incomplete run issues no class receipt.

## Runtime provenance and controls

Lean 4.34.0-rc2 and Mathlib `4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09` are
the existing project pins. The local Work host requires the documented
`host-proc-path.c` adapter from the preceding evidence directory; hosted CI does
not use it. Source SHA-256:
`97246ffaa7eaa0ba843adfd189227c324092ad4de9651052fed8959fe440250b`.
Only the current executable path is adapted, without changing Lean binaries.
The compiler and official Mathlib cache remain trust inputs.

The native exporter and regression compiled under pinned Mojo
`1.1.0.dev2026090805 (34562fa1)` using the minimal compiler package whose SHA-256
is `0d71889abb0887e2fa8a556c1081af4026034cdf98d27ad05b57cb096d7ad4f6`.
The local package's runtime configuration was relocated to its installation
prefix; compiler/modules were unchanged. Hosted CI instead uses locked Pixi.
The test passed both fixed decimal encodings and all three overflow/refusal
controls, reaching its contract receipt. `protocol-tests.txt` records five
passing provenance-parser tests; synthetic logs are not proof evidence.
`wrong-proof-type-control.json` and `wrong-proof-type-audit.txt` record a stronger
calibration: a valid Lean module with `accepted : True` and an unrelated emitter
compiles, then fails the independent expected-type checks. The auditor now
emits the checked packet directly, instead of invoking a generated emitter.
This corrects a harness-level binding weakness found during this work.

Earlier complete-array and monolithic kernel attempts were interrupted or
exhausted the 8 GiB host memory budget. They did not produce an acceptance or
rejection verdict about the mathematical certificates. Separate concurrent
Mathlib workspaces also caused paging and led to interrupted attempts. The new
gate uses bounded row proofs and sequential source compilation; timeouts fail
without a class verdict. No native-evaluation axiom is accepted.

## Hosted evidence inspected

At source head `b19f2e09c1c41edf1250a05743e3dfdcf67e6fc0`, PR #496's focused
common-attractor run [42011456718](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42011456718)
and all-18 graph run [42011456546](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42011456546)
completed successfully. The common-attractor job `127191253305` passed native
compilation/regression, native packet execution and independent full packet
parity. Other repository checks included failures; no all-CI-green assertion
is made. PR #496 had already been merged independently at
`ea870c846f6575e51aaa78ef4659e533da636b0a`.

The preceding generic Lean head `73aea7d7fc482cad28562235f017f38f4c70a904`
passed exact-head [Lean run 42074047016](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42074047016)
with 355 declarations, 201 theorem declarations and all 88 named proofs. That
run does not validate the new packet layer. New exact-head results must be read
at the new revision, without reusing this older success as its acceptance.
