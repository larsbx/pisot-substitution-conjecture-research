# Eight upper plus-Class-A cycle exits: exact-source acceptance

## Result and scope

For all integers `n>=7`, `d=2n+12-J`, and `(J,H)` equal to
`(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(4,1)`, the new literal paths
start at `yy(H,3H,-6H)` and reach typed `yy(0,0,0)`. They have depths
`3,3,5,7,3,5,2,2`. Actual track reversal gives the negative orientations.
Every original word index, child type, full integral offset and both
nested original prefix tracks are retained, with `M^m*w=P-Q` at the endpoint.

The [complete proof](../../docs/class-a-plus-upper-cycle-exits-2026-11-15.md)
contains all intermediate vectors, strict inequalities and explicit prefix
formulas. The [pre-code gate](../../docs/bh-class-a-plus-upper-cycles-stop-go-2026-11-15.md)
records the primary-source review. Recurrence classification, arbitrary-source
upper entry, small `n` and universal BH/PSC remain separate obligations.

## Fresh accepted evidence

| Layer | Observed result | Binding |
| --- | --- | --- |
| Canonical bounded Mojo | 160 paths, 600 edges, max depth 7; 23 exact-reason refusal controls | `native-final.json`, `native-final.log` |
| Independent literal replay of native output | All 160 paths, complete types/offsets/strictness and both original prefixes | `native-independent-replay.json` |
| Separate independent exact oracle | 1,008 paths, 3,780 edges, eight corruptions and two resource refusals | `independent-replay/summary.json` |
| Symbolic integer-polynomial verification | 16 directed all-n paths, 60 edges, 120 original occurrences; 17 corruptions rejected | `symbolic.json` |
| Targeted Python tests | 119 passed, no failures or skips | `pytest-result.json`, `pytest.log`, `pytest.xml` |
| Fresh isolated Lean | 20 local modules compiled from fresh sources; 167 declarations, 114 theorem declarations, eight exact endpoints and 24 controls | `lean-fresh/receipt.json`, unedited `attempt-3.log` |

The final native run has 751 source/pin inputs unchanged before and after,
including a re-enumerated path set. Its log SHA-256 is
`08a7ebc8d790bccb814e5bcdc2b7d141b7815f97c690fc7d4af080cfbdcb0708`.
The independent oracle shares no native implementation or arithmetic code.
Its 1,008-path transcript SHA-256 is
`e843be77ee0d174c79ea6aeb02b5de6e6b235b9fb683653dd68c17b570bc488b`.
The symbolic checker uses an independently specified eight-row table over Z[n].
The native parser is tested against the actual native transcript as a required
successful baseline; it also tests every source/target field, all six prefix
coordinates, receipt completeness, alternate line separators and resource caps.

The native fixture grid is `n=7,8,9,10,11,12,16,31,64,127`, all eight cases,
both orientations. The separate arbitrary-integer replay uses
`n=7..65,127,255,1024,4096`. Large prefix coordinates there are not native
machine-integer acceptance. A native control checks the genuine prefix overflow
at `n=4096,J=1,H=4`, after verifying all small offsets and original indices.
The canonical constructor's step cap defaults to seven; overflow and exhausted
caps refuse without a verdict. The independent oracle caps literal occurrences
at 50,000 and root refinements at 256; exhaustion refuses.

The fresh Lean gate binds 128 local source/pin files, with snapshot digest
`5be0479a196dd3fcc45799ecd0c15268ff431b5509ee86a4bef4f3906a192193`.
It clones pinned dependency sources, requests 25 explicit upstream cache roots
(2,165 upstream artifacts), then compiles all 20 local library dependencies
and runs the fresh standalone audit. It reuses no local project `.olean` files.
The axiom closure allows only `propext`, `Classical.choice`, and `Quot.sound`.
The strict-prefix theorem explicitly requires positive lengths, positive beta,
and exact literal substitution scaling. It does not prove the family-specific
Perron identification or the proposed recurrence/source-entry theorem.

## Reconstruction and preserved failures

The earlier workspace became unavailable and was replaced. Its raw local logs,
unfinished manifest and uncommitted native files did not survive. Earlier chat
counts are not relabelled as files in this packet. The two new Lean sources,
symbolic source/tests and independent exact source were recovered from recorded
edits and verified against their surviving SHA-256 digests. The Mojo module,
receipt adapter and acceptance tooling were reconstructed and freshly executed.

The renewed native attempts are preserved with source bindings:

1. Attempt 1 failed to find `std` because the direct compiler invocation omitted
   its required `MODULAR_HOME`; it produced no mathematical receipt.
2. Attempt 2 set the runtime environment and exposed the reserved Mojo word
   `case` used as a loop variable. The failed driver and unchanged module are
   preserved in `failed-native-sources/`, authenticated against the receipts.
3. Attempt 3 corrected the spelling and passed. The final run also uses the
   hardened runner that detects added or removed source files; its output is
   identical to the preceding successful run.

Fresh Lean attempt 1 failed before launch because `/usr/bin/time` was absent.
Attempt 2 refused the 4.9 GiB default temporary filesystem before dependency
downloads. Attempt 3 used an empty workspace temporary directory with adequate
space and passed without a Lean source change. See `lean-fresh/README.md`.

Review also found that text-mode reads normalized carriage returns and that
`splitlines()` accepted non-LF separators. Both actual CLI readers now decode
raw bytes; rejection tests preserve raw framing. The parser used by the fresh
kernel gate is archived separately from later parser revalidation on the same
unaltered audit bytes. No later Lean compilation is invented.

## Direct integration onto main

`imported-source-provenance.json` pins the exact prerequisite sources from
#581 `9f0138d` and the generic prefix helper from #582 `3091554`. Only five
missing Lean modules are required on main; this does not merge the 304-file
#579 stack. Historical imported review notes retain their original context;
the manifest gives canonical commit-specific source URLs.

See the [stack compatibility review](../../docs/class-a-plus-upper-stack-compatibility-2026-11-15.md).
The original zero-defect helper differs from the later #580 extension, so
future stack reconciliation must review that known source difference.

## Replay

Install the locked native environment with `pixi install --locked` in `kernel/`.
Install Python test dependencies `pytest==8.4.2` and `sympy==1.14.0`.
Use a new output prefix/directory so historical evidence is preserved:

```sh
python tools/run_class_a_plus_upper_native.py --output-prefix /tmp/upper-native
python oracles/python/class_a_plus_upper_cycles.py --native /tmp/upper-native.log
python oracles/python/class_a_plus_upper_independent.py --output-dir /tmp/upper-independent
python oracles/python/class_a_plus_upper_symbolic.py
PSC_UPPER_NATIVE=/tmp/upper-native.log python -m pytest -o addopts='' -q   tests/test_class_a_plus_upper_cycles.py   tests/test_class_a_plus_upper_symbolic.py   tests/test_class_a_plus_upper_audit.py
./tools/setup_lean.sh --toolchain-only
./tools/check_class_a_plus_upper_cycles.sh
```

For the isolated Lean gate, select `TMPDIR` on a filesystem with at least
12 GiB free. The gate creates and removes only its own empty temporary
workspace. Default `tools/setup_lean.sh` behavior is unchanged; its new
`--toolchain-only` option lets this scoped gate retrieve its own fresh
upstream import closure without first downloading the complete Mathlib cache.

The dedicated hosted workflow checks the producing head and retains raw
native/oracle and isolated-Lean artifacts. The existing whole-library Lean
workflow remains a separate check. Hosted and post-merge outcomes must be
read at their producing revision; this local packet does not predict them.
