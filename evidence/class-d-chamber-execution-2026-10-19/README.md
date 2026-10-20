# Chamber execution evidence — 2026-10-19

Base commit: `85fafd3383a2837785199ad7f66e913c0e86c2a7`.
The pinned toolchain could not be provisioned. All local arithmetic runs use
`Mojo 1.1.0 (8189361e)`; they are not a pinned compiler receipt.
No whole-quadrant success receipt is synthesized from partial outputs.

## Replay

From a checkout of this contribution:

```bash
cd kernel
pixi install --locked
pixi run --locked mojo --version
pixi run --locked mojo run -I . tests/test_class_d_plus_positive_b_chambers.mojo
pixi run --locked mojo run -I . tests/test_class_d_chamber_sign.mojo
pixi run --locked mojo run -I . tests/test_symbolic_line_empty_blocks.mojo
pixi run --locked mojo run -I . tests/test_symbolic_line.mojo
pixi run --locked mojo run -I . class_d_plus_positive_b_chambers.mojo
```

To inspect every component independently, build once and invoke `low K`
for K=0..4, `high`, and `line J` for J=1..6. Each low/high call includes
all boundary lines returned by a successful core. A core refusal produces
no boundary-strip threshold and cannot be assigned a fictitious strip list.

```bash
pixi run --locked mojo build -I . class_d_plus_positive_b_chambers.mojo -o /tmp/plus-chambers
/tmp/plus-chambers low 1
/tmp/plus-chambers high
/tmp/plus-chambers line 6
```

For a boundary line with coefficients `[AP,BP,AQ,BQ,AR,BR]` in
`low-boundary-plan.json`, replay the existing exact line driver:

```bash
pixi run --locked mojo run -I . symbolic_line_certificate.mojo norm D AP BP AQ BQ AR BR
```

Replace the six uppercase coefficient placeholders by the exact listed
integers. The plan binds each distinct affine line to every wedge/axis/offset
it covers; deduplication merges only identical six-coefficient tuples.
The 66 low-wedge strip obligations have 62 distinct tuples.

## Source and execution variants

`source-variants.json.gz` contains the exact modified source text for six
stages, relative to the common base checkout. `source-digests.json` binds
those bytes. Other imported sources and vendored pins come from the base.
The stages are:

- `baseline`: unmodified merged driver and engine; the aggregate refuses.
- `components`: only component CLI/progress output added; same decisions.
- `query-context`: only additional query context around the original refusal.
- `coefficient-fallback`: a same-sign coefficient fallback after reader refusal.
- `shifted-fallback`: also checks coefficients in beta-2 after proving chi(2)<0.
- `guarded-fallback`: final source; additionally propagates every error other than the specific undecided-quadrant-sign refusal. The final sign regression uses this version; earlier component receipts retain their own version labels.

To replay a historical stage, use a separate checkout of the base and restore
that stage's two files from the archive. Never overwrite a current checkout
with uncommitted work. The tests added by this contribution exercise the
final implementation. The separate `repaired-build.log` records an unused
intermediate build (shortcut before the existing readers); no execution
receipt is credited to that unused binary.

`complete-driver-mojo-1.1.0.log` is the unmodified aggregate output, exit 1.
It reaches the low-1 refusal only after low-0 and all its strips succeed.
`low-1-query-context.log` records the actual geometric query as well as the
auxiliary polynomial. The first component sweep used a 360-second per-call
budget; timeout 124 is not a mathematical refusal. The later component
sweep allowed 1200 seconds. Independent boundary-line replays use 1200
seconds per line. The initial boundary batch was launched before its binary
finished building, returned 127, and receives no mathematical credit; its
separate launch-error record is preserved. Only the subsequent built-binary
runs count.

The local compiler wrapper was invoked with
`PYTHONPATH=/tmp/psc-mojo-toolchain /tmp/psc-mojo-toolchain/bin/mojo`.
Those paths describe this execution environment, not a dependency to install
or a substitute for the repository's locked environment.

## Evidence boundary

Read `run-context.json` for the final outcomes and `SHA256SUMS` for the
packet digests. Source/compiler errors, timeouts, mathematical refusals,
core success, line success and whole-quadrant certification are different
states. A component success includes the finite prefix and the exact graph
cross-checks performed by `certify`; a printed core success excludes its
boundary strips. No general #139, minus carrier closure or PSC conclusion
is attached to these local partial receipts.

## Final result and archive index

All six wedge cores and all six explicit lines pass locally. Of the 69
distinct returned boundary lines, 67 pass (71/73 strip obligations).
Low-1 v=13 and v=14 remain unresolved. Their first runs time out; isolated
retries lose the execution session with no saved verdict. The original
whole-quadrant success marker is absent. Required pinned replay is absent.

`boundary-line-runs.json.gz` losslessly stores the independent line logs and
metadata, including the failed/incomplete attempts. Paths beginning with
`boundary-lines-final/` or `boundary-retries/` in `run-context.json` name
members of that archive's `files` map. The `sha256` map binds each member's
UTF-8 bytes. `boundary-launch-errors.json.gz` separately preserves the first
batch's exit-127 build-order errors, which receive no mathematical credit.
All other log paths are ordinary files in this packet.

The final `guarded-fallback` source was validated by
`sign-regression-occurrence.log`, including reconstruction of both observed
occurrence endpoint queries. The long component receipts retain their
recorded earlier source-variant identities; they are not relabelled as
final-head execution.
