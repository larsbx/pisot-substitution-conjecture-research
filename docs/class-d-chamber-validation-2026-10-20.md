# Plus-chamber aggregate and inherited validation — 2026-10-20

This continuation replays the existing exact certificate and repairs two
inherited regression pins. It changes no chamber, carrier, sign rule, occurrence
relation, arithmetic cap or claim status. Execution evidence lives in
[`evidence/class-d-chamber-validation-2026-10-20/`](../evidence/class-d-chamber-validation-2026-10-20/).

The native serial aggregate now returns **exit0**, after 3564 seconds,
and emits `CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED`: six wedges, all
73 returned strips (69 distinct affine lines), six explicit interface lines,
and 952 finite-prefix PIP obligations. This is the driver's own receipt,
not a synthesis of component logs. No additional mathematical obstruction
appears after the previously justified reader and enumeration repairs.
The lattice cover, caps and fail-closed gate remain unchanged. Full Pixi/CI
integration is still pending, so no governed plus-family status is promoted.

## Work shown

### Assumptions and hypotheses

The five low unimodular wedges, six interface lines and high unimodular wedge
of PR #289 retain exactly their original parameterizations. The certificate
uses the exact reader corrections and ordered interval sweep in PR #293.
Every core, returned strip and explicit line must finish; component receipts
cannot manufacture the native aggregate receipt. The existing symbolic-line
literature gate continues to govern this regression repair. No new universal
invariant or theorem is proposed.

### Derivation / reduction

`Eventual.threshold` bounds every sign query visited by the algorithm; it is
not a minimal mathematical onset for the eventual graph. PR #288's
`7a74edabb9d96a346bde39f13a6104aa9d0607ce` changed the order of occurrence
endpoint tests: clip an empty block before attempting an affine fit. The added
endpoint queries may enlarge the sufficient tail threshold, even when the
same family is completely certified by checking a longer finite prefix.

The commit changes only that block in `psc/symbolic_line.mojo`. Exact pinned
Mojo replay of its parent `7408537` reproduces both historical pins. Untouched
merged PR #289 (`85fafd3`), already replayed in the previous packet, reproduces
the two later thresholds. Thus the changed pins precede the coefficient
fallbacks and interval sweep.

| Class-D line `(p,q,r)` | Mode | Before clipping | With clipping | Symbolic vertices | Finite PIP / non-PIP / outside |
| --- | --- | ---: | ---: | ---: | --- |
| `(n+1,n,n+3)` | Sturm | 18 | 21 | 97 | 20 / 1 / 0 |
| `(3n+14,3n+15,4n+17)` | norm | 4 | 6 | 105 | 6 / 0 / 0 |

The repaired regression invokes complete `certify`, including every finite
PIP member, determinant checks, symbolic offset-zero reachability and the
usual exact graph cross-checks at `q0` and `q0+5`. It additionally compares
complete exact vertex sets at the old-to-new transition: `n=18,19,20` and
`n=4,5`. These comparisons do not replace tail sign certificates or assert
an unperformed edgewise graph comparison. The all-PIP-member boundary-hitting
conclusion is unchanged; only the sufficient tail/finite-prefix division moves.
Historical tables and earlier failed logs remain available and are annotated,
not silently rewritten. Other historical pin rows are not blanket recertified.

### Evidence and replay

Use the previous packet's hash-verifying bootstrap to install the two
lock-matched Mojo compiler/runtime archives. The compiler is
`1.1.0.dev2026090805 (34562fa1)`. `replay.sh` in the new packet runs the aggregate,
the complete symbolic-line regression and the integrity/provenance checks.
A fresh full `pixi install --locked` failed on
`pydantic-extra-types-2.11.1-pyhcf101f3_0.conda` with a proxy tunnel error.
The exact compiler/runtime replay is not a successful full Pixi installation.

The serial aggregate was built from PR #293 head `e17aef5`. A second build after the pin-table-only change produces a byte-identical
binary (SHA-256 `72d3a54dd2a956302a149317d582d780353008e4dd36dc7575490d8e857fb138`);
the comparison and both hashes are preserved. The pin tables are not queried by this driver.
Raw start/finish times, exit statuses and source hashes accompany the logs.
CI status snapshots distinguish a queued job from an executed certificate.

The complete pinned symbolic-line regression returns exit0 and reaches every
final contract declaration, including all five historical-transition checks.
The provenance suite returns exit0, including generated surfaces, vendoring,
manuscript/Markdown integrity, evidence provenance and claim governance.
The focused Python policy/agreement run returns exit0 (34 passed, one skipped).

### Negative controls

The complete symbolic-line regression retains its rejected non-PIP line,
determinant-zero line, changed-sign quadrant, malformed CLI and mismatched-pin
controls. The prior chamber packet retains negative sign-reader, exact
endpoint and cap/refusal controls. No timeout, undecided predicate or missing
receipt is assigned mathematical success.

### Non-claims / remaining gaps

The plus result is limited to the established class-D positive-b parameter
domain and its stated overlap-graph contract. Dedicated full-environment CI
remains a separate integration gate. No independent human review is claimed.
The minus contribution remains separate. Universal boundary hitting
(#139/#84) and the general PSC remain open obligations.

At the initial inspection, PR #290 at `00c0cb8` still used open seed-qualified
CycleSum-. Its correction distinguished formal productive cycles from seed
reachability: the 56-specimen complete seed grid had no escaped recurrent
labels. Shared parameters and real interiority alone permit formal cycles
with unbounded sums, so they do not replace a seed argument.

**Concurrent update:** PR #290 has since advanced to
`3b16b5447aa9b3ecdecfdabb5033a381580f230e`. It now records a uniform seed-carrier
proof supplying CycleSum- on `a>=2,b>=1`, exact certificates for the omitted
`a=0,1` strips, and a native aggregate for the entire minus residual. Its
assembly with the existing `r>=q-1` theorem covers the PIP minus branch.
This session inspected the aggregate call sequence, its committed exit0
receipt, and all 335 source hashes and 16 evidence hashes in that packet.
It did not independently execute the minus proof or import it into the plus
binary. The cross-reference is pinned in `minus-cross-reference.json`.
Full Pixi/CI remains pending on that separate contribution; neither its
scoped result nor this plus replay supplies a universal premise.

## Reused manuscript and governance repair

The manuscript reconstruction from PR #290 commit
`5e9391d43c10f7fcf969db0e16fecb6108a84927` is reused byte for byte. The original
564,173-byte file contains three identical 183,857-byte tail blocks. Two
were injected after `A1` and before a surviving dollar sign. Restoring `$'`
at exactly those two locations retains the third copy and produces the
196,463-byte source already reconstructed in PR #290. Original, block and
corrected SHA-256 hashes are asserted before writing. The current source
matches that commit exactly; the archived PDF is unchanged. This repairs
syntax and duplicate injection, not the manuscript's proof content or review.

The one-line malformed-string repair in `test_show_your_work_policy.py` is
also reused from that commit, so the policy regression can collect and check
the actual workflow argument fragment. Both repairs are recorded with their
origin; no minus proof code or conditional theorem is imported into this branch.

The broader integrity/governance test run additionally exposed a missing
ledger record for the already-written two-obstruction completion criterion
(189 passed, one failed). Reuse only that registration from the same PR #290
commit: two open universal premises and their existing conditional assembly.
The source is `tools/make_ledger.py`; all ledger surfaces are regenerated.
No minus-family result is copied, and no scoped plus result is substituted for
either universal premise. The adapted regression asserts that either premise
alone is insufficient, the unconditional/import-only models establish neither,
and the already-established class-D lines/wedges do not establish them.
The new two-premise TLA+ scenario is generated and included in the model gate.
The failed broader log is retained; the focused repaired ledger/governance
suite returns exit0 (73 passed, one optional TLC mutation test skipped).

All 16 TLA+ models return their expected outcomes, including the generated
two-obstruction scenario. The TLA tool archive hash is recorded; no dependency
model is credited by inspecting its source alone.

## Correction, 2026-10-30 (fit-first line engine)

The receipt above records the accepted execution and stays the accepted
receipt. After the fit-first change to `psc/symbolic_line.mojo` (§4b
correction of 2026-10-30 in
[p1b-boundary-hitting-progress-2026-10-08.md](p1b-boundary-hitting-progress-2026-10-08.md)),
the same driver emits `CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED wedges= 6
explicit_lines= 6 boundary_lines= 51 finite_prefix_pip= 287
max_symbolic_vertices= 164`. The lower wedge floors return fewer strips and
fewer prefix obligations; the cover and its six cores are unchanged. A local
native run took 3981 seconds. The hosted exact-revision receipt is
`evidence/class-d-closure-rebind-2026-10-30/`.
