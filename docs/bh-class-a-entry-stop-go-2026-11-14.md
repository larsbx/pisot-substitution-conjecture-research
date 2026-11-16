# BH Class-A entry: source gate and selected-escape investigation

Date: November 14, 2026. Baseline: `c9358c2d46d7b306853609e2c5a090328aff92c3`.
This investigation concerns [#452](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/452).
It makes no universal BH, A1′, G1, C4 or PSC claim.

## Pre-code decision

**Proceed with a narrowly stated selected-escape experiment.** The existing
minus-Class-A one-step zero-predecessor set is complete at its stated scope.
The outstanding implication is entry from every cyclic seed descendant.
Investigate whether complete child closure forces an occurrence-valid escape
using the full oriented state and the two affine target defects, or whether
an exact reachable countermodel rejects the proposed progress quantity.
Read-only inspection of existing finite certificates is calibration; it does
not establish parameter-uniform coverage. No new broad census is planned.

For `k,t>=0`, put `n=k+t+3`, `d=k+2t+5`, `A=n+d`, and use the literal words

```text
x -> x y^A x,   c -> c y^n x,   y -> x y^(n-1) c.
```

For a state `(a,b,p,q,r)`, let `delta` be the difference of the indicators
that the first letters of the two source images equal `x`. The nonzero
one-step reverse target is characterized by

```text
p-delta = 0,
p+q+r = 0,
-R_b <= q+(d+1)delta <= R_a,
```

where `R=(A,n,n-1)`. The exact candidate to inspect first is whether a
selected actual edge or a short actual macrostep can decrease the pair of
target defects `(p-delta,p+q+r)` in a well-founded order, preserving tile
types and legal FIRST/RUN/LAST addresses. No decrease under every edge is
required. A valid experiment must retain the original source-to-state and
state-to-exit witnesses when a candidate fails or succeeds.

## Primary-source review

1. Akiyama and Lee, *Algorithm for determining pure pointedness of self-affine
   tilings*, [author preprint](https://arxiv.org/pdf/1003.2898). The overlap
   graph and reachability-to-coincidence construction are prior art. The
   source retains Meyer/actual-overlap hypotheses; its algorithm is not a
   proof that every arbitrary primitive irreducible Pisot substitution has
   a successful escape. A graph-theoretic SCC contradiction may be reused
   only after the actual occurrence relation and relevant source coverage
   are supplied.
2. Akiyama, *Strong coincidence and overlap coincidence*,
   [author preprint](https://arxiv.org/pdf/1509.04471). The converse uses
   strong coincidences for sufficiently many choices of control points.
   A single productive hub or selected seed cannot replace its coverage
   hypotheses. No spectral implication is imported in this experiment.
3. Minervino and Thuswaldner, *The geometry of non-unit Pisot substitutions*,
   Annales de l'Institut Fourier 64 (2014), 1373–1417,
   [publisher PDF](https://www.numdam.org/article/AIF_2014__64_4_1373_0.pdf).
   Prefix automata and Dumont–Thomas addresses retain literal occurrences.
   The representation space includes the finite places. Multiple tiling
   alone does not give pointwise exact finite-level hitting; the degree-one
   tiling criterion retains strong coincidence and geometric property (F).
   This determinant-minus-two chamber is not treated as unimodular.

These sources justify the existing occurrence/graph framework. They provide
no new unconditional Class-A entry theorem. The attempted rank is a research
candidate, not an imported result.

## Existing controls and reuse

The append-only side-notes ledger and the following exact-source notes were
read before the experiment:

- [Uniform reverse target](class-a-uniform-zero-return-2026-11-02.md).
- [Guarded odd-plane transfers](class-a-x-transfer-plane-2026-10-31.md):
  the reachable state `(x,y,1,6,-9)` at `k=t=0` defeats the guard-free
  transfer because its second proposed ordinal is `A+3`.
- [Rectangular cover obstruction](class-a-cover-obstruction-2026-10-21.md):
  strict physical clipping and independent coordinate bounds do not prove
  full child closure.
- [M-adic digit ladder](class-a-madic-digit-ladder-2026-11-02.md): a matching
  lowest digit can fail a later integral carry; successful carry tests for
  supplied addresses do not force the existence of addresses.
- [Literal X-descendant audit](class-a-x-productivity-2026-10-31.md):
  finite complete graphs, selected paths and productive cycles are useful
  controls, while all-parameter coverage remains separate.

PR #574 at `fd23a6681db651762e49c9c959a9aad682fb007f` was inspected before
starting. It supplies a conditional BH-to-finite-reachability bridge and
new A1′ tail witnesses. Neither discharges #452. Its actual carrier,
closure and zero-hit premises must not be assumed as an entry theorem.

## Evidence boundary

At this pre-code checkpoint no new experiment has run and no new progress
rank, source cover, escape theorem or countermodel is asserted. Subsequent
findings must be recorded below with their exact inputs and replay scope.

## Refined candidates before their implementation

The first exact control rejects the two-defect rank without its legal-gap
condition. The positive follow-up is therefore restricted to the entire
**strict zero-defect slice**, `p=delta` and `p+q+r=0`: first reduce all gap
overruns to finitely many endpoint states with their actual LAST/FIRST
addresses, then construct exits from those states. This is a slice theorem;
it does not assert that arbitrary cyclic seed descendants enter the slice.
The formal track also investigates an explicit, clipped, two-step RUN/RUN
preimage of the existing one-step target. Both tracks retain source letters,
proper occurrence ordinals and every integral offset. They use no new census.

## Outcome of the selected investigation

The initial two-defect candidate omitted a real base-case obstruction:
at `k=t=0`, `(y,y,0,-4,4)` is recurrent and X-reachable, has both defects
zero, but has no legal one-step zero address and no target entry within
two actual steps. Its source path, return cycle and productive four-step
exit are retained in the canonical negative regression.

The repair is a new local theorem, rather than a conjectured rank:
**every strict zero-defect source has an actual integral-zero path of
at most ten generations, for all parameters**. The proof reduces the
legal-gap overruns to thirteen explicitly typed endpoint families, then
gives exhaustive parameter cases and original occurrence ordinals for
their exits. Every path has a final full Parikh zero, so literal ancestry
supplies strict geometry. The proof and exact scope are in
[the zero-defect escape note](class-a-zero-defect-escape-2026-11-14.md).

This proves the candidate's zero-rank base case. For a supplied actual
child-closed strict graph, reaching the one-step target is now equivalent
to reaching the entire strict zero-defect slice. Uniform entry from
arbitrary cyclic seed descendants, or a decreasing selected choice from
every source outside the slice, remains unproved. The result supplies
no new source cover or nonunit realized-overlap dictionary.

Written proof, canonical native validation and Lean subfamily proofs
have distinct acceptance scopes. Finite replays check formulas; none is
used to infer an all-parameter or all-descendant statement. Exact source
and runtime receipts are recorded with the implementation, and hosted CI
and independent review are not silently assumed.

The completed local evidence now includes exact native/oracle agreement
on 1,332 original-address paths and 4,145 edges; independent complete
strict-slice replay at fourteen named parameters covers 3,970 states and
6,512 edges. The universal symbolic certificate separately proves
199 endpoint/chamber paths and their genuine reversals (398 directed
paths, 1,096 edges), with every ordinal guard checked coefficientwise.
Its sixteen ordinary chambers and seven strict fifth-endpoint chambers
exhaust the stated parameter domains, and all nine oriented source
LAST/FIRST identities are checked. These results support the local
ten-generation theorem; none establishes seed entry into its source slice.
The native-log gate binds every expected source record and the exact
fixture set, not just aggregate counts: it rejects duplicates and a
truncated log that still contains one valid row for all fourteen members.
