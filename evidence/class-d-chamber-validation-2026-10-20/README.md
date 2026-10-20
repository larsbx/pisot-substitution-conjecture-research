# Class-D chamber validation continuation

This packet records a successful uninterrupted native serial aggregate,
reconciliation of two historical line pins, and reuse of the hash-verified
manuscript reconstruction from PR #290. The research derivation and scope are
in [the validation note](../../docs/class-d-chamber-validation-2026-10-20.md).

## Native aggregate result

The original driver returned **exit0** after 3564 seconds, from `2026-10-20T00:56:31Z`
to `2026-10-20T01:55:55Z`, and emitted this native receipt:

```text
CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED wedges= 6 explicit_lines= 6 boundary_lines= 73 finite_prefix_pip= 952 max_symbolic_vertices= 164
```

All six cores, 73 returned strip obligations (69 distinct affine lines), and
six explicit interfaces match the previous component campaign exactly.
The 952 finite-prefix PIP checks are obligations, not a count of distinct
parameter points. `check-aggregate.py` verifies the log and exit status;
it does not create a mathematical receipt.

The native `max_symbolic_vertices=164` field accumulates only wedge cores
and explicit interfaces. The largest line graph observed in the complete
log has 465 vertices. The field is not presented as a bound on all strip
or concrete graphs.

## Provenance

- Base: PR #293 at `e17aef51f6773a97d04201d73b77a4354651b5bb`.
- Compiler/runtime: the exact lock-matched Mojo
  `1.1.0.dev2026090805 (34562fa1)` archives, with hashes in `run-context.json`.
- Full Pixi environment installation: failed, preserved in `pixi-install.log`.
- `aggregate-binaries.sha256` and comparison exit0 establish that the repaired
  historical pin tables produce a byte-identical aggregate binary.
- Manuscript original/block/corrected hashes and reconstruction origin are
  preserved in `manuscript-reconstruction.json`.
- `preclip-pins.log` replays the parent of the clipping change with the same
  pinned compiler. The unchanged merged-#289 replay is preserved in the prior
  continuation packet's `pinned-baseline-pins.log`.
- `symbolic-line-regression.log` preserves the complete test, including the
  finite transition vertex-set checks and final contract declarations.
- CI snapshots record queued jobs, which have no steps or logs yet.

Raw `.exit` files are shell process exit codes. A timeout or interrupted run
is not a mathematical refusal. The old interrupted aggregate in the previous
packet is retained unchanged. Only the native driver can produce its aggregate
certificate marker; this packet's metadata scripts never synthesize one.

## Completed validation

The complete symbolic-line regression passes under the pinned runtime and
reaches every final contract, including all five old-to-new transition checks.
The focused Python suite exits0 (34 passed, one skipped). The provenance suite
passes, including manuscript integrity and claim governance. CI remains queued
at the recorded check; local execution does not assign it a success.

The broader integrity/governance run reports 189 passed and one missing
conditional-claim registration. Its raw failure is preserved. The focused
ledger/governance replay after reusing PR #290's existing registration passes
(73 passed, one optional TLC mutation test skipped). The two universal premises
remain open; the assembly is conditional.

## Replay

Bootstrap the runtime with
`../class-d-chamber-continuation-2026-10-19/bootstrap-pinned-mojo.py`, then run
`TLA_TOOLS=/path/to/tla2tools.jar PSC_PINNED_MOJO_ROOT=/path/to/runtime bash evidence/class-d-chamber-validation-2026-10-20/replay.sh`
from the repository root. A complete repository Pixi/CI replay remains the
integration gate. The supplied minimal runtime is not labelled a successful
full Pixi installation.

## Boundaries

No plus-family claim is promoted here. PR #290 now separately records a
complete local minus residual certificate and minus-branch assembly; its
receipt and source/evidence hashes were inspected, not rerun in this session.
Universal boundary hitting and the general PSC remain open targets.
The separate manuscript repair and regression reconciliation supply no missing
mathematical premise. Historical raw logs and failed pins remain in earlier
packets and git history.
