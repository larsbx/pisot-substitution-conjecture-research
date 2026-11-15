# Actual balanced cuts approach the original prefix tiles

Baseline: `main@9a1357ed5dae3b4502d29c34396d0e9403ccca75`.
The [pre-code source gate](c4-cut-prefix-embedding-literature-2026-11-12.md)
is the preceding commit. This increment formalizes the literal embedding
and uniform approximation step in Section 4 of the
[written compact counting bridge](c4-nonunit-madic-counting-bridge-2026-11-04.md).

**Local formal acceptance:** the complete isolated source build and compiled
axiom audit passed at code revision
`73a0b6a95539beb1b6712afec0f8412571b41cd3`, tree
`8233701f593a8ba680356a88c2c6fc8e4cf01df5`. All 2,670 source-named
proofs were reached, including the 37 new theorems. The audit inspected
6,589 compiled declarations and found only `propext`, `Classical.choice`,
and `Quot.sound`. The [local evidence archive](../evidence/c4-cut-prefix-embedding-2026-11-12/README.md)
preserves the complete log, exact source bindings, all native witnesses,
independent inspections, and earlier failed or interrupted attempts.

Hosted candidate CI has not run. Local native replay passed with the exact
lock-matched Mojo compiler; complete local locked-environment provisioning
failed on a network dependency download and is not claimed successful.
The later evidence-only commit does not claim a fresh build or hosted run
of itself. Independent human review remains pending and does not block
continued research. No governed claim status changes.

## Result

Let `s` be either `1/021/001` or `1/012/001`, with its own authenticated
infinite period-two word `w`, original stable chart `piZ`, and original
matrix-adic factor `H(s)`. Fix a finite source word `u`.

For **every** `n` and **every actual marked position** of `s^(12n)(u)`,
the proof constructs an ordinal `j` of `w` selecting the same following
letter. Write `x` for the Parikh vector before the finite marked position
and `y` for the Parikh vector before position `j` of `w`. Then `y*` is an
actual prefix point of the corresponding tile, and

\[
 \|\pi_Z(x)-\pi_Z(y)\|
 \le (7/8)^n C_{s,u},\qquad
 [x]_q=[y]_q\quad(0\le q\le12n).
\]

The finite constant `C_{s,u}` depends only on the original source word and
its fixed reference positions. It is not selected anew at each depth.
The uniform consequence has the quantifier order

\[
 \forall\varepsilon>0\ \forall q\ \exists N\ \forall n\ge N\
 \forall\text{ actual marks}\ \exists\text{ same-letter prefix witness}.
\]

The stable error is below `epsilon` and the original depth-`q` residue is
equal. Thus both the real and finite-place coordinates are controlled.

For two marks at a balanced cut, their prefix Parikh vectors are exactly
equal. Applying the theorem to both tracks gives two authentic tile
witnesses approaching that **same cut point**. If the source is a member
of a supplied `StrictSystem`, the existing literal cut theorem supplies a
represented cut pair and proves that the two following letters differ.

## Derivation and hypotheses

### Literal embedding before projection

Decode the full marked position into a source mark at parent ordinal `i`
and a local mark `P a S` in `s^k(d)`. Choose a proved occurrence of `d` in
the same reference word, after prefix `Y_d`. The actual prefixes are

\[
 X=s^k(u_{<i})P,\qquad Y=s^k(Y_d)P.
\]

The local prefix cancels, giving the exact integer identity

\[
 p(X)-p(Y)=M^k\bigl(p(u_{<i})-p(Y_d)\bigr).
\]

`CutPrefixEmbedding.mark_decomposition` reconstructs the complete parent
and local marks, including suffixes and repeated positions. It does not
assume nonerasure for a position that actually exists.
`embeddedIndex`, `embedded_letter`, and `embedded_prefix` bind the new
point to a real ordinal and the entire prefix of the declared word.
`prefix_error` proves the identity above. The generic statement explicitly
requires the reference occurrences and the fixed-prefix identity.

Projection gives `x* - y* = A^k z*` in the **original** product space.
`prefix_residue_eq_of_le` proves equality at every `q<=k` by image-lattice
membership and the genuine quotient reduction maps. The completion is not
replaced by one for `M^k`.

### Fixed finite error bound

The source bound is a finite sum over the uninflated parent positions and
the three fixed reference choices:

\[
 C_{s,u}=\sum_{i<|u|}\sum_{a<3}
 \left\|\pi_Z\bigl(p(u_{<i})-p(w_{<j_a})\bigr)\right\|.
\]

Every actual correction is one term of this sum. The generic
`correction_norm_le` proves that inequality. The existing authenticated
block-twelve contraction iterates to `(7/8)^n`; the generic `norm_pow_le`
supplies this step without expanding the concrete real chart in tactics.
The ordinary geometric-sequence limit proves uniform decay.

`NamedCutProximity` discharges the reference-occurrence and fixed-word
premises for both named sources. The reference ordinals are `(0,2,1)` for
the first word and `(0,1,2)` for the second. The same incidence matrix is
not used to identify their different literal words. Powers `12n` are
genuine fixed-word powers and include the zero-depth case.

### Balanced and strict cuts

`balanced_cut_approximation` requires equality of the two **actual**
prefix Parikh vectors and returns both witnesses around the common vector.
It needs no assumption that the finite source words themselves occur in
the infinite reference word. `strict_cut_labels` separately applies the
existing `StrictSystem.cut_follow` and `cutPair_ne` theorems to actual
strict-carrier membership.

The witness ordinal can be reused by different original parent positions
with the same letter and local digit. Future density counts must count the
original common cut vectors; no injectivity of the reference witnesses is
claimed.

The witnesses belong to their respective tiles. The cut is not asserted
to belong to either tile, or to their intersection, at a finite depth.

## Independent executable replay

The canonical Mojo implementation constructs complete literal witnesses
for the original two substitutions at powers `0,2,4,6`. Its declared
source words are `012`, `2010`, and `120`; the paired controls inflate
`01/10`. It retains full parent/local positions, prefixes and suffixes,
following letters, source and reference prefix vectors, signed corrections,
and every explicit integer residue witness. A cap is a refusal, never a
geometric exclusion.

The independently written Python oracle expands complete words, locates
parents with separately computed block boundaries, recounts literal prefix
slices, and uses unbounded integer incidence action. It compares the
entire packet recursively, including all records, order, field inventories,
types and declared scope. No digest-only or summary-only comparison is
credited.

The complete local packet contains 3,220 marked witnesses, 21,028 residue
witnesses and 272 balanced cuts, of which 51 have distinct following
letters. These are finite replay counts, not the quantifier domain of the
Lean convergence theorem. The paired examples are not claimed to be a
strict system.

## Controls

The 15 Lean controls retain the actual distinct named words and failure of
their one-step fixed-word identities. They prove a nonzero signed reference
correction and show that its reversal changes the stable error. In the
genuine inverse limit for multiplication by two on `Z`, `star(2^k)` agrees
with zero through depth `k` but differs at depth `k+1`, for every `k`.
A separate exact counterexample shows that growing corrections can cancel
every contraction step and keep the error equal to one.

Native and independent oracle mutations refuse changed source/reference
identities, wrong parent or local marks, reversed correction, altered
prefix vectors, missing or corrupted residue witnesses and invalid paired
cuts. The complete oracle additionally rejects dropped, duplicated or
reordered records and ambiguous JSON. Native mutation baselines are built
and verified before entering rejection-catching blocks, so a failed
positive fixture cannot earn refusal credit.

## Replay and acceptance gates

From the repository root:

```sh
python tools/make_proof_bank.py --check
./tools/setup_lean.sh
./tools/check_lean.sh
```

From `kernel/`, using the repository's locked environment:

```sh
pixi run --locked mojo run -I . tests/test_c4_cut_prefix_embedding.mojo
pixi run --locked mojo run -I . c4_cut_prefix_embedding.mojo > /tmp/cut-prefix-packet.json
```

Then, from the repository root:

```sh
python -O oracles/python/c4_cut_prefix_embedding.py --native /tmp/cut-prefix-packet.json --controls
C4_CUT_PREFIX_NATIVE=/tmp/cut-prefix-packet.json python -m pytest --assert=plain -o addopts='' -q tests/test_c4_cut_prefix_embedding_oracle.py
```

The focused `C4 actual cut-prefix embedding` workflow binds the exact
head/tree, provisions the locked native environment and retains the full
packet and receipts. The existing `C4 overlap Lean verification` workflow
performs the complete isolated source build and compiled axiom audit.
The unchanged independent named-chart and prefix-window Quint workflows
remain selected by the proof changes. Local development caches are not
substituted for the isolated-source acceptance gate.

## Recorded local checks

The full isolated build and compiled audit passed with the worktree clean
at the code revision above. Independent inspection matched all 37 explicit
theorems and seven source definitions to their compiled records, including
the complete `strict_cut_labels` specialization. The three new modules own
52 compiled constants, including generated helpers.

The full native packet and optimized-mode oracle agree record by record;
eight Python tests passed with native comparison enabled and zero skips.
Native tests rejected 19 mutations. The oracle exercised 18 refusals and
one finite-residue sanity control. At the same code head/tree, the existing
named-chart Quint suite passed 22 tests and rejected 10 mutations, and the
prefix-window suite passed 19 tests and rejected nine mutations. These
bounded checks retain their own finite scope.

## Remaining machine-checked counting obligation

This closes the literal and uniform-proximity step of the written M1
argument at the stated scope. The next analytic assembly still needs:

1. Compactness to turn simultaneous approximation of both tiles into
   eventual containment in each suitable open cover of their intersection.
2. A fixed-origin regular-cylinder lattice count with the correct product
   normalization and covolume.
3. The literal strict-cut density lower bound and the limit/outer-cover
   argument deriving positive product-Haar measure.

The [compact-cover follow-on plan](../evidence/c4-cut-prefix-embedding-2026-11-12/compact-followon-plan.md)
states the next exact target and identifies the pinned Mathlib route. It
uses compact tiles and a product neighborhood basis; a separate precompact
bound on the moving cut points is unnecessary for that proposed transfer.
The plan is not an additional implemented Lean theorem.

Those conclusions are not obtained from finite residue agreement,
physical interval length, nonempty compact overlap or the contraction
estimate alone. No new all-packet identification, general PIP constructor,
general C4, A1', BH, G1, PDS or PSC conclusion is asserted. The ordinary
one-step ancestry work remains independent of this embedding theorem.
