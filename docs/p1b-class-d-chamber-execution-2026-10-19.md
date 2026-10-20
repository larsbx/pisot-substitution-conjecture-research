# Class-D positive-b chamber execution — 2026-10-19

Status: **complete native aggregate replay with the lock-matched Mojo compiler/runtime**; no family theorem promotion.
The October 20 native aggregate returns exit0 after all six cores, all 73
returned strip obligations (69 distinct lines), all six explicit lines and
952 finite-prefix PIP checks. See the [latest validation and scope note](class-d-chamber-validation-2026-10-20.md).
Earlier partial, interrupted and failed-validation runs below remain historical.
Base: `85fafd3383a2837785199ad7f66e913c0e86c2a7` (merged PR #289).
The dedicated original run is [39292497570](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/39292497570).
Execution receipts, source variants and replay instructions are in
[`evidence/class-d-chamber-execution-2026-10-19/`](../evidence/class-d-chamber-execution-2026-10-19/).

## Work shown

### Assumptions and hypotheses

The exact lattice cover in §12 of
[`p1b-class-d-positive-b-wedge-2026-10-19.md`](p1b-class-d-positive-b-wedge-2026-10-19.md)
is unchanged: five low wedges, six lines, one high wedge. Local `(u,v)`
coordinates refer to those wedge parameterizations, not the original `(a,b)`.
All children still require exact occurrence ranges and open overlap margins.
A successful wedge core is only one shifted orthant: every omitted boundary
strip and every finite PIP prefix must also certify.

The symbolic-line literature gate in
[`p1b-catch-up-free-ppvc-2026-10-07.md`](p1b-catch-up-free-ppvc-2026-10-07.md)
continues to govern the existing overlap-graph contract. This contribution
repairs its sign reader and execution reporting; it proposes no new
universal invariant or imported theorem. The determinant-two, realization,
and general-PSC boundaries of that gate remain intact.

The pinned compiler is `1.1.0.dev2026090805` under `kernel/pixi.lock`.
`pixi install --locked` failed through the package proxy (first observed:
OpenVINO TensorFlow frontend; recorded replay: NumPy). All local Mojo
results below use **Mojo 1.1.0 (8189361e)** and are explicitly **not pinned
replay receipts**. The pinned environment was neither silently replaced nor
relocked.

### Derivation / reduction

The unmodified complete driver finishes low wedge 0, including all its
boundary lines, then refuses in low wedge 1 at source `(c,x,-e_y)`.
The first refused segment pair is top RUN / bottom LAST; the query is
the upper margin at the smallest legal difference `m=-(q-1)`.
Its actual oriented Perron query is

```text
h(beta) = -4 -(5+2u+2v) beta -(3u+4v) beta^2.
```

This is strictly negative for every `u,v>=0` and `beta>0`; the constant term
is already negative. The refusal is in an auxiliary Sturm–Tarski polynomial,
not in the geometric inequality. Its exact degree-13 specializations have
leading coefficients

```text
P(n,n):   -16602626880,
P(4n,n):  144310901145600.
```

Both positive integer rays enter every shifted orthant. Consequently no
larger corner can make this auxiliary polynomial one-signed. The verbatim
expanded polynomial is retained in `low-1-query-context.log`.

A separate high-wedge refusal at source `(c,x,e_c-e_y)` occurs at top
FIRST / bottom RUN, the upper margin at `m=0`. It asks for

```text
h(beta) = (u+2) beta^2 -2(u+1) beta -4
        = (beta-2) ((u+2) beta+2).
```

The existing PIP contract certifies `chi(2)<0` for a monic characteristic
polynomial whose Perron root is its largest real root; hence `beta>2` and
this query is positive. That sign rejects the whole occurrence block
because every legal difference is `m>=0`. Its refused auxiliary polynomial has leading term
`2304 n^6` on `(u,v)=(n,n)` and `-4 n^9` on `(n,n^2)`, so moving the
quadrant corner cannot settle that auxiliary sign either. Again, neither
an escaped child nor a changing geometric margin is exhibited by this refusal.

The repair is a sufficient, exact fallback after both existing sign readers
refuse specifically on an undecided quadrant sign. Other arithmetic or
invariant errors propagate. It checks all nonzero coefficients of the actual query for the same
strict sign on the already certified parameter region. If necessary, and
only after independently certifying `chi(2)<0` on that region, it applies
the same check to the exact Horner translation `h(z+2)` with `z=beta-2>0`.
Zero polynomials return zero; mixed or undecided coefficient signs remain
undecided. No sample decides a uniform sign. Successful historical reader
paths are unchanged; no cap, fitted bound, PIP screen or child relation is
weakened.

These two obstructions require a sign-reader correction. They do **not**
justify another chamber, a carrier enlargement, or discarding a real
child. More demanding conditional realness/closure arguments remain
possible later obligations, and must be based on a subsequent exact refusal.

### Evidence and replay

The original aggregate has exit code 1 and emits no whole-quadrant receipt.
The lattice calibration passed. Independent component entry points expose
later components even when the aggregate stops at the first refusal. A
component receipt never substitutes for
`CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED`.

All six explicit interface lines completed with the coefficient fallback
(first repair source variant):

| Line `c=5a+j` | Tail threshold `a>=q0` | Symbolic vertices | Finite PIP prefix members |
| --- | ---: | ---: | ---: |
| j=1 | 12 | 164 | 12 |
| j=2 | 12 | 164 | 12 |
| j=3 | 12 | 164 | 12 |
| j=4 | 12 | 164 | 12 |
| j=5 | 12 | 164 | 12 |
| j=6 | 13 | 164 | 13 |

Each successful `certify` call also checks offset-zero reachability,
determinant magnitude two, its finite prefix, and exact graph agreement
at the two declared cross-check parameters. This is the scope of these
local receipts, not canonical execution with the locked toolchain.

Wedge and final regression outcomes are recorded in the accompanying
execution manifest and the final status table below.

### Negative controls

`kernel/tests/test_class_d_chamber_sign.mojo` checks the low query and its
negative, exact concrete Perron signs at five parameter points, zero,
mixed signs, a changing parameter coefficient, and a coefficient vanishing
on a boundary. It checks the shifted high query and rejects the same
shortcut when `chi(2)>0` or `chi(2)=0`. A polynomial such as `beta-3`
remains undecided from the bound `beta>2` alone. The full existing
symbolic-line regression is also replayed. The original refused logs are
preserved rather than overwritten by repaired runs.

### Non-claims / remaining gaps

| Obligation | Evidence boundary |
| --- | --- |
| Exact plus integer cover | PR #289 formulas preserved; local lattice regression passes |
| Plus positive-b closure | Requires all six cores, all returned strips and six explicit lines; local partial receipts do not promote it |
| Minus selected lower-rank state | Separate PR #287 algebraic result |
| Minus conditional target realness | Separate PR #288 implication; not carrier closure |
| Minus positive-b closure | Separate PR #290 at 3b16b54 now records a uniform seed-carrier proof on a>=2,b>=1, complete a=0,1 strips, and a native minus-residual aggregate. Its full Pixi/CI integration remains pending; no minus proof is imported into this plus contribution |
| Universal #139 / #84 | Open; a class-D contribution is not universal hitting |
| General PSC / G1 | Open; no quantifier or spectral import is enlarged |

Independent human review remains final validation; its absence does not
block this research contribution. Missing pinned execution is a distinct
unfulfilled requirement, not a human-review issue.

## Validation and inherited failures

The new coefficient/shifted-sign regression and the empty-block regression
pass under the available compiler. The independent targeted Python suite
exits successfully. Governance passes after adding the missing empty-block
contract and replacing the proof ladder's unrecognized imported-bridge label
with the existing `[IMPORTED theorem]` vocabulary. The regenerated inventory
still has 102 governed claims; no status or dependency is promoted.

The full symbolic-line regression stops at `test_a_class_d_line_is_certified`:
its pinned `q0=18` differs from the computed `q0=21`. A detached checkout of
untouched base `85fafd3`, with the same compiler, independently gives
`q0=21`, 97 symbolic vertices, 20 finite PIP members and one non-PIP member.
Thus this pin mismatch predates the coefficient fallbacks. The pin is not
weakened to hide it; the full regression is recorded as failed. Its later
test bodies and end-of-file contract declarations receive no execution credit.
The unchanged manuscript source also fails its integrity guard at line 1357.
Those inherited failures and missing pinned replay remain integration debt.

The separately emitted Mojo `wedge_edges` list matches every entry of the
boundary plan: 66 obligations and 62 distinct coefficient tuples. Python
only orchestrates/reconciles exact line replays; it supplies no closure or
Perron-sign decision.

## Reconciliation with concurrent work

Main advanced to `c0c5f9d10f3025d8fab8df07e4a300b1b173a70a` during this run
(PR #292, two documentation files). This branch incorporates it; no executed
kernel dependency changed from the recorded `85fafd3` base.

The earlier PR #290 diagnosis said **RC-** was refuted by productive
U/Ubar/V/Vbar cycles. Its later correction at `00c0cb8` distinguishes
formal cycles from seed reachability: the checked 56-specimen seed grid has
no escaped recurrent labels. Unrestricted carrier inclusion fails, but that
is not an observed counterexample to the seed-qualified premise.
The current sufficient premise is **CycleSum-**, the bound |wx+wc+wy|<=1
on genuine seed-reachable cycles. The guarded 1,971-state superset and
exceptional exits in that separate branch reduce minus BH to this open
premise, using #287 algebraic descent and #288 conditional target realness.
Finite SCC calibration does not prove CycleSum-.
Open PR #291 separately implements the row-12 integer squeeze. This
contribution complements that work with actual chamber execution and does
not duplicate its squeeze implementation or the minus SCC investigation.

## Historical local execution result (before continuation)

| Component | Certified core `(u0,v0)` | Vertices | Completed boundary lines / required |
| --- | --- | ---: | ---: |
| Low 0 | (1,7) | 164 | 8 / 8 |
| Low 1 | (7,15) | 164 | 20 / 22 |
| Low 2 | (1,7) | 164 | 8 / 8 |
| Low 3 | (3,7) | 164 | 10 / 10 |
| Low 4 | (3,15) | 164 | 18 / 18 |
| High | (7,0) | 164 | 7 / 7 |

All six explicit interface lines also pass. The returned cores leave 73
boundary-strip obligations, representing 69 distinct affine lines. **67 of
those 69 distinct lines completed**; equivalently, 71 of 73 strip obligations
are discharged locally. Duplicate lines are credited only after their exact
six-coefficient tuples agree with canonical `wedge_edges` output.

At that checkpoint the two unresolved lines were low wedge 1 with `v=13` and `v=14`:

```bash
cd kernel
pixi run --locked mojo run -I . symbolic_line_certificate.mojo norm D 4 69 4 68 3 53
pixi run --locked mojo run -I . symbolic_line_certificate.mojo norm D 4 74 4 73 3 57
```

Each first attempt exhausted a 1200-second wall-clock budget during the
concurrent line sweep. No mathematical refusal was emitted. An isolated
retry with a declared 1800-second budget subsequently lost its execution
session (`Unknown process id 77030`), with no saved exit result or receipt.
That loss is recorded as incomplete execution, **not** as a further timeout,
mathematical refusal or successful certificate. Neither line is credited.

The high aggregate also reached its 1200-second budget, but its completed
log contains the successful core and first six strips. Its last strip
`(p,q,r)=(n+59,n+58,n+50)` subsequently completed independently (q0=1),
so all seven high strips are credited. Similarly, independent line replays
complete low wedges 2, 3 and 4 despite earlier per-wedge timeouts. Partial
runs are not globally credited; individual completed calls are identified.

**No whole-quadrant receipt was emitted.** No final-head pinned execution or
family theorem is claimed. The original CI run remained queued on recheck.
The next execution obligations at that checkpoint were the two lines above
followed by the locked full driver; the existing line-pin and manuscript integrity
failures must also remain visible for integration. No new chamber wall,
conditional geometric exception, or escaped carrier child was found after
the two sign-reader repairs in the completed work.

## Continuation: finite-prefix execution cost

The traced v=14 boundary call completes its symbolic tail with 164 vertices
and q0=56 before spending its remaining budget in exact finite-prefix graphs.
The existing concrete child routine enumerates every pair of image tiles.
The continuation preserves the existing overlap contract and replaces only
that enumeration by a monotone interval sweep. This is an implementation
optimization of the already reviewed contract, not a new universal invariant
or a new theorem-facing diagnostic; the literature gate cited above applies.

For positive tile lengths, both image partitions have strictly increasing
endpoints. A bottom tile ending at or before the current top start cannot
intersect this or any later top tile. A bottom tile starting at or after the
current top end cannot intersect this top tile, nor can any later bottom tile.
Keep a monotone first-bottom index, enumerate the surviving interval, and use
the original exact interior predicate before appending. This preserves top-major
occurrence order, duplicates, strict endpoint exclusion and exact field arithmetic.
Work changes from O(m*n) candidate pairs to O(m+n+K), where K is the number
of intersecting occurrence pairs. A differential regression compares the full
ordered output against the former nested loops, including equal endpoints and
non-overlap rejection. No cap or proof obligation is relaxed.

### Two formerly unresolved strips now complete

The continuation obtained the exact lock-matched compiler/runtime packages
by their lockfile URLs and verified both SHA-256 hashes before use. The
compiler is Mojo 1.1.0.dev2026090805 (34562fa1). Full `pixi install --locked`
still failed on a dbus dependency; this is a minimal compiler/runtime replay,
not a claim that the whole Modular/Pixi environment installed.

| Low-1 strip | Tail threshold | Symbolic vertices | Finite PIP members | Cross-check parameters | Result |
| --- | ---: | ---: | ---: | --- | --- |
| v=13 | 53 | 164 | 53 | 53,58 | pass |
| v=14 | 56 | 164 | 56 | 56,61 | pass |

The runs return zero in 189.6 and 210.4 seconds respectively, using the
interval-sweep implementation and exact sign-reader repairs. Neither has
a non-PIP or inadmissible finite-prefix member. Their earlier timeouts were
execution-cost gaps; no additional chamber, conditional realness exception,
or carrier extension was needed for these two calls. The 1,096-state
ordered differential test and all 16 seed-overlap regressions pass under
the same pinned compiler/runtime. The complete same-source campaign is
recorded separately below; earlier receipts retain their source identities.

### Continuation validation boundary

The full symbolic-line regression fails with q0=21 versus the historical
class-D pin18 under the pinned compiler. Executing the previously hidden
suffix reveals the norm-line threshold6 versus pin4. The unchanged merged
#289 checkout (`85fafd3`) reproduces both outcomes under this same compiler:
`BASELINE_CLASS_D_PIN 21 97 20 1` and `BASELINE_NORM_PIN 6 105 6 0`.
Neither mismatch was introduced by the interval sweep or tracing. Both pins
remain unchanged, and neither failed full test receives a success receipt.
The remaining norm-product test passes when invoked separately.

Provenance passes the generated ledger, refreshed proof bank, vendoring,
claim governance, Markdown integrity and historical evidence checks, but
continues to reject the unchanged manuscript's unmatched end at line1357.
The four targeted Python files complete (32 passed, one skipped).
The dedicated CI workflow now includes the ordered-sweep and existing
seed-overlap regressions before attempting the complete certificate.

## Complete same-source component result

All twelve component invocations return zero using the same
`psc-continuation-chambers` binary and Mojo 1.1.0.dev2026090805 (34562fa1):

| Component | Certified core | Vertices | Returned strips certified |
| --- | --- | ---: | ---: |
| Low0 | (1,7) | 164 | 8/8 |
| Low1 | (7,15) | 164 | 22/22 |
| Low2 | (1,7) | 164 | 8/8 |
| Low3 | (3,7) | 164 | 10/10 |
| Low4 | (3,15) | 164 | 18/18 |
| High | (7,0) | 164 | 7/7 |

All six explicit lines also return zero: j=1..5 have threshold 12 and j=6
has threshold 13, each with 164 symbolic vertices and every finite-prefix
member PIP and hitting. These are uniform tail certificates plus their
complete finite prefixes, not a finite parameter grid.

The 66 low-strip obligations match the previously emitted canonical
`wedge_edges` plan, including wedge/axis/value provenance; the seven high
strips match `[1,11+8k,1,10+8k,1,8+7k]`, k=0..6. Altogether this is
73 obligations and 69 distinct affine lines. Source hashes, binary hashes,
all logs and exit codes, and the reconciliation are in
[`evidence/class-d-chamber-continuation-2026-10-19/`](../evidence/class-d-chamber-continuation-2026-10-19/).

The separate serial aggregate was manually interrupted as duplicate work
(exit 130); it is not a failed mathematical certificate and does not receive
a successful aggregate receipt. No
`CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED` marker is synthesized from the
component logs. The source's original fail-closed aggregate gate remains
unchanged and the dedicated full-Pixi CI replay is still required for
integration. The local component computation is complete; full environment/CI
validation and the inherited pin/manuscript failures remain separate debts.

The exact sweep benchmark on a noncoincident swap seed at the v=14 line's
n=30 member produces the same ordered list of 390 children. The former
production loop takes 1.967 seconds and the sweep 0.0150 seconds in that run
(about 131x); no general timing guarantee is inferred from one specimen.
The declared candidate-pair complexity changes from O(m*n) to O(m+n+K).

No additional exact mathematical obstruction arose after the two sign-reader
repairs. The established lattice cover and all existing caps/checks are
preserved; no carrier extension is introduced. The separate minus-side contribution has since advanced to the native
residual certificate recorded in PR #290 at 3b16b54; see the October 20
validation note for the inspected receipt and scope. Universal boundary
hitting and general PSC remain open. No governed plus-family status is promoted.

## October 20 native aggregate and validation completion

The uninterrupted serial driver now emits its own
`CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED` receipt and returns exit0.
All six cores, 73 strips (69 distinct lines), six interfaces and 952 finite-prefix
PIP obligations reconcile exactly with the earlier same-binary component
campaign. The old interrupted serial run is retained and not relabelled.

The full pinned symbolic-line regression now passes after tracing and
reconciling PR #288's two inherited sufficient-threshold changes. Exact
transition checks and complete finite prefixes preserve coverage. The
hash-verified manuscript reconstruction and existing conditional completion
record are reused from PR #290; manuscript/provenance checks, focused
governance regressions and all 16 TLA+ models pass. No universal premise is
supplied by that registration.

Full Pixi installation still fails at a dependency download and the dedicated
CI runs remain queued at the recorded recheck. PR #293 stays draft with no
governed plus-family promotion. PR #290 now separately records its complete
minus residual certificate and minus-branch assembly at 3b16b54; its source and
evidence hashes were inspected, not rerun here. Universal #139/#84 and general
PSC remain open. See the [validation note](class-d-chamber-validation-2026-10-20.md)
and [new evidence packet](../evidence/class-d-chamber-validation-2026-10-20/).
