# Minus-Class-A constant entry: exact-source evidence

Date: November 14, 2026. Parent source:
`34ff471c24960729527ae5f090e96c7c16ae4584` (draft PR #578).

## Mathematical result and source scope

For the literal substitution

```text
x -> x y^(n+d) x, c -> c y^n x, y -> x y^(n-1) c,
d>=5, n>=d+1,
```

the [written theorem](../../docs/class-a-minus-constant-entry-2026-11-14.md)
constructs an actual composable path to typed coincidence from **every
strict integral overlap**. One-level word densities force central `y/y`
entry, a positive nearest recurrence has a constant tail, and three
original RUN edges lower every admissible nonzero constant height.
Nested original prefixes give the full identity `M^m w=P-Q`.

This includes the former residual strip `d+1<=n<5d`, with no upper bound
on `n`. Section 7.2 of the proof authenticates the separate low-gap and
seam-line contracts. Together with #578, those sources cover the entire
minus-Class-A canonical swap-seed domain `n>=1,1<=d<=2n-1` mathematically.
The inherited certificates keep their original source and acceptance
scopes; they are not all-strict theorems or new executions of this head.
`inherited-kernel-source-comparison.json` verifies that all 757 inherited
native source/pin files are byte-identical to the parent.

## Acceptance results

| Layer | Observed result and boundary |
| --- | --- |
| Canonical central and constant paths | Passed: 27 members, 945 central paths, 156 signed constant paths, 10,606 checked edges, maximum depth 37. |
| Canonical entry fixtures | Passed: 567 paths, 1,295 checked edges, maximum depth 5; 270 homogeneous density inequalities and eight refusal controls. |
| Canonical typed aligned entry | Passed: 162 paths, 462 checked edges, maximum depth 4; mixed-letter zero is nonterminal. |
| Independent complete original-prefix replay | Passed: all 1,830 expected native sources, all 12,363 edges and every composed original-prefix identity; exit zero recorded in `literal-and-differential-run.json`. |
| Unbounded symbolic support | Passed: two exhaustive positive-height chambers, both reversals, four directed paths, 12 edges and 24 genuine RUN occurrences; exact cubic, recurrence and density identities; eight mutation controls. |
| Targeted Python tests | Passed: 39 cases, no skips; exact XML and stdout retained. |
| Recorded-data integrity | Passed: 164 cases; final packet digests and exact file-set bindings verified again after adding this receipt. |
| Cached Lean development | Passed: 75 owned declarations, including 68 theorem declarations; seven independently specified endpoint types and 21 rejection controls. |
| Fresh source-isolated Lean | **Not passed.** Attempt 1 exited 1 at the fixed upstream Mathlib cache, before local theorem compilation: all 8,890 downloads returned HTTP 403. |
| Exact-head hosted and whole-library acceptance | Pending. The configured workflows must be assessed at their producing commit. Parent or cached receipts are not substitutes. |
| Independent human review | Pending. |

The maximum finite depth 37 is a regression result, not a uniform depth
bound for all parameters or all strict integral sources.

### Original occurrence evidence

`central-native.log` and `entry-native.log` contain the complete original
ordered indices, typed intermediate states and all three integral offset
coordinates. `paths-native.log` is their exact concatenation. The source
fixtures are explicitly declared in both the native tests and independent
oracle: `d` is 5, 7 or 11, and `n` includes both sides of the height
thresholds and values through `24d`. All admissible signed constant
heights in those fixtures, through height 12, are included.

The independent oracle scans all legal RUN gaps, rebuilds selected
incidence and prefix counts from literal words, compares every ordered
native path, and reconstructs proper prefixes in the original depth-`m`
images. It checks `M^m w=P-Q`, original ordinals, terminal letters and
the requested stopping policy. It requires the exact complete source
set, exact counters and exact contract receipts. Missing sources,
duplicate records, altered full vectors, fabricated prefixes or partial
logs cannot be credited as complete.

`literal-and-differential.json.gz` is a lossless archive of the complete
independent replay output, including all 1,830 original-prefix certificates.
Its uncompressed stdout digest is recorded in
`literal-and-differential-run.json`; `summary.json` provides the short
machine-readable result and the explicit acceptance boundaries.

### Formal subset and trust inputs

The seven exact endpoints are `forward_integer_bound`,
`bounded_two_sided_classification`, `periodic_cycle_classification`,
`eventual_constant_tail`, `constant_nearest_iff`, `three_run_decrement`
and `constant_composable_path`. The eventual-tail theorem derives boundedness
and periodicity. The signed constant path derives strictness backwards
from typed zero under explicit positive-length scaling, and assumes
neither a supplied hit nor an interior source.

The cached development audit inspects every owned declaration and its
transitive axioms, allowing only `propext`, `Classical.choice` and
`Quot.sound`. Its source hashes are:

| Input | SHA-256 |
| --- | --- |
| `ClassAMinusConstantRecurrence.lean` | `748b13de20f335033940b3cdddf2d648d10365c23080301b66dfd8db8a498e04` |
| `ClassAMinusConstantRecurrenceAudit.lean` | `6e90eee52630956763ce1bca0525ecc0fd20b02b956ac09a5007863e8c930ecc` |

The full family theorem still uses written Perron identification,
half-unit exclusion, one-level center counting, central recurrence
specialization and nested-prefix assembly. These interfaces are not
silently included in the formal endpoint audit. The generated proof
inventory is not a whole-library compilation receipt.

## Fresh-source refusal and preserved development records

`lean-isolated-attempt1.json` records the exact command, timestamps,
exit code, elapsed time, input hashes before and after, and raw log
digest. The run began at `23:00:34.563431 UTC` and ended at
`23:03:59.388635 UTC`. It copied and bound 127 source/configuration
files, verified the explicit Lean 4.34.0-rc2 / Lake 5.0.0 release and
freshly cloned pinned dependencies, and built the upstream cache tool.
It then failed downloading the fixed upstream cache with
`CONNECT tunnel failed, response 403`. No new local theorem was
compiled in that isolated workspace.

The exact raw log is retained losslessly as
`lean-isolated-attempt1.log.gz`; its uncompressed SHA-256 is
`4c9fcfd37998ed17da16ac70625ea389378b57a5b9e997ed3bf6325ab956c30f`.
`lean-source-bindings-attempt1.json` retains the 127 copied source
bindings and their snapshot digest
`3a3fd14176f3b45d512e81251b5114fbdb429a83ca0417d8f41e48d036f3f165`.
These are source-copy receipts, not compilation acceptance. The gate
continues to refuse local compiled artifacts and uses an empty temporary
cache; its policy was not relaxed to turn this refusal into a pass.

The initial native entry compilation used the wrong new-Mojo `List`
constructor spelling. Its compiler diagnostic is retained in
`entry-compile-refusal-attempt1.stderr`; the corrected literal-list run
passed at the final source.

The initial central emission lost its session during a workspace
interruption and stopped without completion receipts after 1,074 path
rows. Its exact partial stdout/stderr are retained in the two
`central-emission-interrupted-attempt1.*.gz` files and are not accepted
as a complete transcript. The replacement run completed with exit zero,
all 1,101 rows and exact final receipts, with unchanged source hashes;
`central-native-run.json` records its command and timing. The initial
successful no-emit run is retained as an accurately labelled combined
tool capture, without invented stream boundaries or timestamps.

## Controls and replay

Native controls reject foreign words, field coefficients and prefix
caches even at an empty zero-source path; invalid parameters/heights;
noncentral inputs; altered ordinals and offsets; negative or exhausted
caps; and checked-integer overflow. The tests explicitly verify that
nonzero constant states are nearest-selector fixed points before using
their different, productive exits. Independent controls additionally
reject nonintegral helper inputs, wrong prefix certificates, premature
or continued terminal paths, incomplete receipts and symbolic mutations.

From the repository root:

```bash
python -m pytest -o addopts='' -q tests/test_class_a_minus_constant_entry.py tests/test_class_a_minus_constant_symbolic.py
python oracles/python/class_a_minus_constant_symbolic.py
python oracles/python/class_a_minus_constant_entry.py --native-log evidence/class-a-minus-constant-entry-2026-11-14/paths-native.log
./tools/check_class_a_minus_constant_entry.sh
python tools/make_proof_bank.py --check
sha256sum -c evidence/class-a-minus-constant-entry-2026-11-14/SHA256SUMS
```

For fresh canonical output, run from `kernel/`:

```bash
pixi run --locked mojo run -I . tests/test_class_a_minus_constant_entry.mojo --emit
pixi run --locked mojo run -I . tests/test_class_a_minus_entry_search.mojo --emit
```

`source-inputs.sha256` binds the producing source files and explicit
inherited dependencies. `SHA256SUMS` binds every file in this evidence
packet, including this README. Historical packets are preserved. No
governed claim status is promoted, and universal BH, plus-Class-A,
arbitrary-ternary A1-prime, C4, spectral conclusions and arbitrary
alphabets remain outside this result.
