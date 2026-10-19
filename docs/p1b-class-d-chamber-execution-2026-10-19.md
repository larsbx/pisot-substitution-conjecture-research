# Class-D positive-b chamber execution — 2026-10-19

Status: execution audit and sign-reader repair; **no family theorem promotion**.
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
| Minus positive-b closure | Uniform recurrent-carrier inclusion RC- is the current sufficient target in separate PR #290; conditional all-child closure is stronger. Its a>=2 transport domain does not silently cover a=0,1 |
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

Issue #139's newer comment and open PR #290 narrow the minus sufficient
obligation to uniform **recurrent-carrier inclusion RC-**, together with
#287 algebraic descent and #288 conditional target realness. Full child
closure is a stronger sufficient route, not a necessary premise of that
new reduction. The finite SCC calibration in #290 is not a uniform proof.
Open PR #291 separately implements the row-12 integer squeeze. This
contribution complements that work with actual chamber execution and does
not duplicate its squeeze implementation or the minus SCC investigation.

## Final local execution result

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

The two unresolved lines are low wedge 1 with `v=13` and `v=14`:

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
The next execution obligations are precisely the two lines above followed
by the locked full driver; the existing line-pin and manuscript integrity
failures must also remain visible for integration. No new chamber wall,
conditional geometric exception, or escaped carrier child was found after
the two sign-reader repairs in the completed work.
