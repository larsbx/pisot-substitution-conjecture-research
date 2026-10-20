# Two-obstruction length-moment execution evidence

Base: `main@54c67739f0a502216fbfb1bff5260b0841511cb9`.
Derivation and exact scope:
[`docs/two-obstruction-moment-interface-2026-10-20.md`](../../docs/two-obstruction-moment-interface-2026-10-20.md).

The final native Mojo test returns **exit 0** and reaches its contract receipt.
It checks all three aligned pairs of the stated PIP specimen (witness depths
3,2,1), a genuine nonzero-offset swap occurrence (depth 3), exact drift and
short-window controls, singular-map refusal, malformed addresses and budgets,
and return periods through 64. No universal hit or family theorem is claimed.

## Runtime boundary

Execution uses **Mojo 1.1.0 (8189361e)**, the available runtime. This is **not**
the locked nightly `1.1.0.dev2026090805 (34562fa1)` and **not** a full Pixi or
GitHub Actions receipt. Reusing the prior lock-hash bootstrap failed with
HTTP 403 before provisioning the compiler; `bootstrap.log` and `.exit`
retain that failure. The dedicated workflow requests the locked replay.

## Separate class-D CI observation

Original run [39292497570](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/39292497570)
is now completed/failure at its pre-repair head `30dc38d`. The lattice test
passes and the aggregate exits 1 on the exact low-1 sign-reader exception
archived in the earlier execution packet. `original-chamber-ci.log` preserves
the raw job log; `original-ci-reconciliation.json` records the full exception
string match against the committed `low-1.log` and complete-driver log.
This is the already repaired reader obstruction, not new carrier evidence.
PR #293 head `53a4021` run 39356406683 is still queued in the API snapshot.
Neither result changes the independent local plus aggregate receipt.

The supplied shell replay was itself executed successfully against the
available runtime. Its raw output, timestamps and return codes are the
`script-*` files. `run-context.json` records the binary digest and 312 source
and lock/manifest hashes. All mathematical arithmetic uses exact vendored
unbounded rationals; no floating threshold is introduced.

## Replay

From the repository root, with Pixi available:

```sh
bash evidence/two-obstruction-moments-2026-10-20/replay.sh /tmp/new-length-moment-replay
```

The output directory must not exist. For an explicitly labelled diagnostic
runtime, set `PSC_MOJO_RUNTIME_ROOT` to the directory containing `bin/mojo`
and `lib/mojo`. This override must not be described as a locked replay unless
its compiler/runtime provenance actually matches the lock.

## Preserved failures and governance

- `initial-build.log`: initial API misuse (`Q` equality/printing and missing
  search budgets), corrected before the successful builds.
- `build.*` and `replay.*`: first passing implementation.
- `final-*` and `script-*`: final source with direct word-inflation checks.
- `focused-tests.log`: host Python initially lacks pytest. The retry uses
  existing installed pytest packages; focused Markdown/ledger regressions
  pass with one optional test skipped (`focused-tests-retry.log`).
- `provenance.log` and `governance.log`: vendoring, generated claim ledger,
  catalogue, Markdown and hit-evidence checks pass. Proof-bank freshness,
  manuscript integrity and two governance findings fail. These same three
  gates fail on untouched `54c6773`, as recorded in `baseline-gates.json`.
  The governance findings are the inherited imported-bridge label and
  `test_symbolic_line_empty_blocks.mojo` declaration. Pending PR #293 owns
  their repairs; this focused contribution neither waives nor duplicates
  that integration work. No green whole-repository gate is claimed.

`SHA256SUMS` checks this packet’s integrity; hashes are provenance, not a proof.
Both universal questions and general PSC remain open.
