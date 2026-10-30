# Class C residual diagonal cover, \(j=2,3,4,5\) (2026-10-29)

**Research status:** exact finite countercontrols verified independently;
all eight scoped parameter-uniform boundary-hitting certificates passed the
hosted native Mojo CI matrix in run `40950276676` (trusted symbolic engine;
independent mathematical review still pending). No PDS/G1/global PSC conclusion. Builds on Theorem T_C (merged
PR #384) and the independently proved PIP criterion P_C (merged PR #397).
No modification of the trusted symbolic cone engine.

## 1. Parameterization and the exact domain

For \(d\ge 6\), \(\varepsilon\in\{+1,-1\}\), and integer \(j\ge 1\), set

    c_eps = 0 (plus), 4 (minus);
    n = 4d + c_eps - j;
    sigma(x) = x y^(n+d) x;
    sigma(c) = c y^n x;
    sigma(y) = c y^(n-d+eps) c.

Theorem P_C gives the exact PIP conditions

    plus: 2d >= j - 5;
    minus: 2d >= j - 3.

Thus every \(d\ge 6\) is PIP for both signs and each \(j=2,3,4,5\).
This conclusion is **algebraic**, not inferred from the finite graph data.
The bounded native cover rechecks PIP on each symbolic piece as a
fail-closed guard, independently of this argument.

## 2. Reproduced, independently exact finite structure

The separate standard-library rational-interval oracle from PR #397,
using all ordered occurrence pairs (not Mojo's optimized sliding window),
reconstructed **complete typed label sets** for d=6,7,8 in both signs:

| j | plus vertices (d=6,7,8) | minus vertices (d=6,7,8) | interpretation |
| --- | --- | --- | --- |
| 2 | 204,204,204 | 222,222,222 | stable full typed rows over 3 sampled gaps |
| 3 | 228,228,228 | 238,238,238 | stable full typed rows over 3 sampled gaps |
| 4 | 180,180,180 | 212,212,212 | stable full typed rows over 3 sampled gaps |
| 5 | 196,196,196 | 226,226,226 | stable full typed rows over 3 sampled gaps |
| 6 | **270,278,278** | **260,254,252** | exact counterexample to one label set for all d>=6 |
| 7 | **286,268,276** | **262,256,250** | another exact nonfrozen line |

All 36 finite exact graphs are complete under the 20,000-state cap
and every vertex reaches offset zero. Complete normalized typed rows,
not just counts, agree across the three gaps for j=2..5 in each sign.
The independent oracle is the same committed exact-arithmetic code as
PR #397; it is a useful algorithmic cross-check, not a wholly independent
implementation of the swap-seed graph's mathematical definition.

**Verified obstruction N_C.** There is no single label set (nor a single
cardinality) for the entire (j=6) diagonal, for *either sign*: for plus,
(d=6) gives 270 labels and (d=7) gives 278; for minus these two
give 260 and 254. Both members are PIP by P_C and BH holds in these
particular finite graphs. The same warning applies to (j=7).
This is a genuine finite counterexample to a *frozen-label claim*,
not a counterexample to BH. In particular, the proposed cover must
not assume constant labels across its finite prefix or across parameter
cells.

The complete rows for each finite sample are SHA256-pinned by the
standalone oracle output in
`evidence/class-c-residual-diagonal-cover-2026-10-29/finite_controls.py`.
The first four j rows are finite observations only, not proofs of
constant labels for unbounded d. The exact source reference is
`evidence/class-c-residual-domain-2026-10-29/exact_oracle.py`.

## 3. Scoped conditional BH theorem / proof obligations

**Candidate B_C(2..5).** For each (\varepsilon=\pm1) and
(j\in\{2,3,4,5\}), the complete canonical swap-seed
overlap graph of the class-C substitution at (n=4d+c_\varepsilon-j)
has an offset-zero descendant from every vertex for every integer \(d\ge 6\).

The code `kernel/class_c_residual_diagonal_cover.mojo` **attempts** to
certify each of eight candidate statements as follows.

1. For each threshold (D=6,7,\ldots,16), construct the affine
   symbolic diagonal `Piece(eps,c_eps-j,D,0,DIAGONAL)`.
   PIP, strict signs and run-index bounds must certify for the whole
   region (d\ge D), not at samples.
2. Require every symbolic vertex to reach an identically-zero offset
   on this parameter region. This implies BH for each member through
   Lemma S' **if** the trusted symbolic engine and its assumptions
   are correct. This does not require symbolic offsets to be constants.
3. Compare **all vertex keys** at both (d=D+1) and (d=D+2) against
   the ordinary exact Mojo kernel. These are independent sanity checks,
   not the quantified proof step.
4. On success, exhaustively run the fail-closed capped exact kernel at
   *every* integer gap (6\le d<D). Its `c_block` helper rejects
   a non-PIP input, graph cap or a vertex without an offset-zero
   descendant. Each such finite exceptional member is a separate
   finite BH certificate.
5. If a sign or affine fit is undecided, try a larger D. Any other
   failure aborts; in particular, **no certifying D** means
   `NO_CERTIFICATE`, not "BH false".

The finite prefix and the symbolic tail are disjoint and cover
all \(d\ge 6\), so a successful certificate is a uniform BH result.
There is deliberately no `rows(g)` / constant-offset requirement.
The cover prints `BH_CERTIFIED` only at the end after every guard.

The eight native jobs completed successfully in workflow run `40950276676`.
They constitute repository-level, computer-assisted BH certificates under
Lemma S' and the trusted symbolic cone implementation, not an independently
reviewed proof of the symbolic engine itself. Failing a future replay would
suspend acceptance; never infer a BH counterexample from an inconclusive sign.

## 4. Replay and next region

    python3 evidence/class-c-residual-diagonal-cover-2026-10-29/finite_controls.py
    cd kernel
    pixi run --locked mojo run -I . class_c_residual_diagonal_cover.mojo 1 2
    pixi run --locked mojo run -I . class_c_residual_diagonal_cover.mojo -1 2
    # analogously for j=3,4,5

Authoritative workflow:
`.github/workflows/class-c-residual-domain.yml` (the `native-j2-j5-cover`
matrix and `finite-diagonal-controls` job). The originally added duplicate
`.github/workflows/class-c-residual-diagonal-cover.yml` was malformed YAML
because its unquoted `steps[].name` contained a colon followed by a space;
GitHub created failed runs with **zero jobs**. It was removed instead of
maintaining a second, more expensive set of identical proof jobs.
The Python exact samples were independently reproduced locally;
new native Mojo executions were **not** performed locally because
the Mojo toolchain is unavailable in the execution environment.
No claim_governance or completion-ledger assertion is advanced
before hosted acceptance.

**Next after acceptance:** parameter-stratify j>=6, not by assuming
globally fixed offsets. The exact j=6 countercontrols force at least
one finite exception or separate cell per sign, while the finite
profile suggests an eventually stable symbolic tail. Such stability
is a *candidate to certify* on d>=7 (plus) and d>=8 (minus),
not an established uniform fact.

## Work shown

### Assumptions and hypotheses

The only unconditional spectral premise is the proved exact class-C PIP
criterion P_C in #397; its integer threshold is checked independently from
the overlap graph. A complete finite seed-reachable graph is required for
the bounded witnesses. No global constant label set or pure-discrete-spectrum
hypothesis is assumed.

### Derivation / reduction

Parameterize each diagonal by (n = 4d + c_\varepsilon - j).
For each sign and (j=2,3,4,5), the proposed symbolic tail is an affine
one-parameter family. A successful symbolic closure, together with
every-vertex zero reachability, proves BH for all integer gaps in the certified
tail by Lemma S'. Every omitted gap is checked independently by the capped
exact graph kernel. Thus a completed run would cover every gap (d\ge6).
The finite j=6 controls show that the stronger frozen-label claim
cannot extend to all small gaps.

### Evidence and replay

The earlier hosted Class-C residual workflow run
`40950276676` completed successfully, including eight
`native-j2-j5-cover` jobs and the independent finite controls. The
original PR #398 also had a failed generic PSC research check; that check
must not be mistaken for a failed mathematical certificate.
Reproduce with
`python3 evidence/class-c-residual-diagonal-cover-2026-10-29/finite_controls.py`
and, from `kernel/`,
`pixi run --locked mojo run -I . class_c_residual_diagonal_cover.mojo 1 2`
(and similarly for the other seven cases).

### Negative controls

At j=6 the plus graph has 270 vertices at d=6 and 278 at d=7;
the minus graph has 260 and 254 respectively. Those exact complete
graphs are incompatible with a universal frozen-label assertion,
though each finite graph passes BH. Sign-reader refusals and graph caps
must never be classified as proof of BH failure.

### Non-claims / remaining gaps

The certificate outputs establish only scoped BH under Lemma S' and
the existing trusted `psc.symbolic_cone` implementation. They do not
independently verify the symbolic engine, imply PDS or discharge global
PSC. Subsequent merged Theorem T_C2 (#399) covers the larger band
(3d\le n) below the onset, so the remaining class-C BH investigation
should prioritize the lower cone rather than duplicate its work.
Independent mathematical review is still pending.
