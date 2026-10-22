# Class-D chamber continuation: pinned-runtime execution

Continuation of PR #293 at `2af1b9630331e75ebbf1ce23db2e3b1da9d9525e`.
The source changes preserve #289's six wedges, six explicit lines, exact
occurrence relation, caps and fail-closed aggregate gate. No family theorem,
universal boundary-hitting theorem or general PSC claim is promoted here.

## Completed result

All twelve component invocations return zero from the same binary:
**six wedge cores, 73/73 boundary-strip obligations (69 distinct lines), and
six explicit lines**. `coverage-reconciliation.json` matches all 66 low
obligations to the canonical prior plan and all seven high lines to their
exact formulas. Every line call includes its finite prefix and cross-checks.

The separate serial aggregate was manually interrupted as duplicate work;
`aggregate-interruption.json` records the observed exit 130. It supplies no
aggregate success marker. The component computation is complete; full Pixi/CI
integration remains outstanding and no theorem status is promoted.

## Runtime provenance

`toolchain-context.log` records **Mojo 1.1.0.dev2026090805 (34562fa1)**,
archive hashes, the unchanged `pixi.lock` and vendoring hashes, host Python,
and linked runtime libraries. Both compiler and `mojo-python` archives match
the exact SHA-256 entries in `kernel/pixi.lock`. The standard library and
three Modular runtime libraries come from that compiler archive.

Full `pixi install --locked` fails on the conda-forge dbus package through
the available proxy. These are **lock-matched minimal Mojo compiler/runtime
executions**, not receipts from a successfully installed full Modular/Pixi
environment. The direct compiler package depends only on the matching
`mojo-python` package and Python >=3.10; host Python 3.12 satisfies that
requirement. No lock was edited, re-solved, or substituted.

To recreate the minimal environment (Python 3.12 and `zstandard` required):

```bash
python evidence/class-d-chamber-continuation-2026-10-19/bootstrap-pinned-mojo.py /tmp/psc-fresh-runtime
PSC_PINNED_MOJO_ROOT=/tmp/psc-fresh-runtime bash evidence/class-d-chamber-continuation-2026-10-19/replay.sh
```

To reproduce individual calls after building the chamber driver, invoke
`plus-chambers low K` for K=0..4, `plus-chambers high`, and
`plus-chambers line J` for J=1..6. Wedge calls include every returned strip.
The component campaign used a 2400-second limit per low1..4/high call,
1800 seconds for the independent low0 replay, and 600 seconds per explicit
line. The separate serial attempt had a 7200-second ceiling but was manually
interrupted; its recorded status is not a timeout or a mathematical refusal.

Run `summarize.py` followed by `reconcile-coverage.py` to check the archived
log mapping. Neither script emits the native aggregate success marker.

The full locked CI replay remains the preferred integration gate. The
`ci-*.json` snapshots record the original and #293 Actions runs as queued,
without logs or successful certificate receipts.

## Mathematical obstruction versus execution cost

The earlier packet preserves the actual low-1 and high auxiliary sign-reader
refusals and their sufficient exact coefficient arguments. The first is a
strictly negative actual query despite a changing auxiliary polynomial;
the second factors as `(beta-2)((u+2)beta+2)>0`, after `chi(2)<0` proves
`beta>2`. Neither warrants a new chamber wall or a carrier enlargement.

The two previously unresolved strips instead stall in concrete finite-prefix
graphs, after their symbolic tails have certified. The interval sweep removes
only pairs of child occurrences whose open intervals provably cannot meet;
it preserves the former ordered child list, multiplicity, endpoint strictness
and exact field predicates. See the derivation in
[`docs/p1b-class-d-chamber-execution-2026-10-19.md`](../../docs/p1b-class-d-chamber-execution-2026-10-19.md).

## Evidence index

- `run-context.json` and `source-snapshot.json.gz`: source/compiler/binary
  identity. `baseline/kernel/psc/overlap_seed_patch.mojo` is the original
  nested loop; other kernel sources are the continuation's final source.
- `pinned-component-*.log` and matching `.exit`: whole wedge calls, including
  all returned strips, and the six explicit lines, all from the same binary.
- `component-results.json`: a log index made by `summarize.py`, not a
  mathematical certificate and not an aggregate success marker.
- `pinned-complete-chambers.log`: the separate serial aggregate attempt.
  Only the actual driver may emit `CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED`.
- `pinned-low-1-v13-sweep.log`, `pinned-low-1-v14-sweep.log`: both formerly
  unresolved calls complete, with thresholds 53/56, 164 symbolic vertices,
  finite-prefix counts 53/56, and exact graph agreement at 53/58 and 56/61.
- `child-sweep-test.log`: ordered differential agreement on 1,096 reachable
  states in four plus/minus/long-run specimens, plus equal-endpoint and
  invalid-parent controls. `test_overlap_seed_patch.log`: all 16 existing tests.
- `sweep-benchmark.mojo` and `.log`: executed source snapshot and log for
  the canonical `kernel/overlap_child_sweep_bench.mojo`; the former production nested loop versus
  the new sweep on a noncoincident swap-seed state at the v=14 line's n=30
  member; both full ordered child lists must agree. Earlier coincident and
  reference-loop measurements retain their separate source/log labels.
- `test_symbolic_line.log`: full suite fails at the inherited 21/18 threshold
  pin. `symbolic-line-suffix.log`: previously hidden 6/4 norm-line pin failure.
  `pinned-baseline-pins.log`: untouched #289 reproduces both. The separate
  `norm-property-only.log` records the last test, which was otherwise hidden.
- `provenance.log`: generated/governance/vendoring checks, with unchanged
  manuscript-integrity failure. `python-tests.log`: targeted regression suite.
- `low-1-v13.log` (unpinned, original enumeration) and
  `pinned-low-1-v13-baseline.log` (pinned compiler, tracing, original
  enumeration) both finish with exit0 and the same q0=53/164-vertex verdict.
  `low-1-v14-trace.log` is an unpinned 300-second timeout during its finite
  prefix, with no mathematical refusal or complete receipt.
- Initial build/installation failures retain their own names and receive no
  successful-certificate credit.

## Logical separation

Plus component execution does not establish the minus quadrant. The current
minus premise in PR #290 is **CycleSum-**, not the refuted RC- premise;
conditional target realness and the productive exceptional exits remain
separate ingredients. Universal #139/#84 and general PSC stay open.

Historical results in the previous evidence packet retain their original
unpinned compiler and source-variant labels. This packet does not relabel
those runs. A passing component includes the finite-prefix and graph-agreement
checks actually executed inside `certify`; a core receipt excludes its strips.
