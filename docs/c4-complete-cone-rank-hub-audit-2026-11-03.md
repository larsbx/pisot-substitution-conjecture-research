# C4 complete strict-cone rank/ordered-hub certificate — 2026-11-03

**Status:** uniform elementary exact algebra + **bounded, hypothesis-checked
word-level diagnostic** for *supplied* finite strict child-closed ternary
balanced-pair systems. This is a necessary-condition instrument, **not a
proof of C4, G1, BH, A1′, seed productivity, pure discreteness or PSC.**

**Baseline:** `main@4993a5960fb7570ee0ce3c07b3a2c66316b755ae`,
including merged #455 Proof Bank and merged #460 local
two-generation literal Parikh spanning.

## 1. Prior work and targeted stop/go

The [Parikh intertwiner](c4-parikh-intertwiner.md) already proves
`P_C N_C=M P_C` for a given strict fully closed component and
`rank_Q(P_C)=3` if the ternary incidence characteristic polynomial
is irreducible. The merged
[two-generation literal rank theorem](c4-two-generation-parikh-span-2026-11-02.md)
strengthens this: **from every source** its complete actual
depth-at-most-two offspring masses span `Q³` under the irreducible
incidence hypothesis, independent of the number of states.
The merged [strict birth atlas](c4-strict-birth-atlas-2026-11-02.md)
keeps all real child boundaries and their source digits; [PR #459](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/459)
pins the primitive full-rank reducible four-state
**non-PIP** system with sixteen all-zero ordered hub residuals and
twelve nonsynchronizing newborns.

The imported mathematical ingredient is elementary rational invariant
subspace/dual eigenvector algebra. This note provides an **explicit
integral obstruction certificate** and a *single* fail-closed cross-layer
audit; it does not represent the prior Parikh argument as new or claim
that flatness entails low rank. No fresh population census, synthetic
letter-pair graph, or theorem claim-status promotion is needed.
**Decision: proceed** with a reusable complete actual-word
certificate and preserve the rank-two control before attempting
the much harder strict PIP flatness theorem in [Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).

## 2. Closed-system integer mass and two-generation conformance

Let `sigma` be a nonerasing ternary substitution, `M` its incidence
matrix, and `C={T_0,...,T_{r-1}}` a **nonempty finite complete
strict child-closed** set of irreducible balanced noncoincident word
pairs. Let `P` have column `p(T_i)` and `N` count **every actual
ordered child occurrence** in each parent image, with multiplicity.

Then (by literal concatenation, not an inferred packet quotient),

```text
              P N = M P.                             (1)
```

For every root `i`, its depth-0, depth-1 and depth-2
**complete occurrence cone** has columns `p(T_i)`, all
`p(T_{N-child})` and all granddaughter `p(T_{N²-child})`
with exact ordinal multiplicity. Sums at each depth are

```text
    p(T_i),       M p(T_i),       M² p(T_i).          (2)
```

If `chi_M` is irreducible of degree three over `Q`,
its minimal-polynomial argument forces `det[p,Mp,M²p] != 0`
for every nonzero `p=p(T_i)`. So:

> **Uniform necessary condition (restatement with a finite
> certificate):** Every root in a supplied fully strict closed
> ternary system with irreducible incidence must have a complete
> depth-at-most-two cone whose actual descendant columns have
> **rank three**. This result quantifies over *all source roots*,
> without a bound on `|C|`, and does not assert that such
> a strict PIP system exists.

The new native routine enumerates every root's three-level
*state-ID/occurrence-ordinal paths*, not only their set of
reachable states. It checks (1) directly from actual source
word factorization before searching for integer 3×3 minors.
A failed/over-budget construction raises, never returns a false
negative on a truncated system. It does **not** use its finite
rank computations to infer an unbounded theorem.

## 3. Constructive rank-two invariant-plane obstruction

A precise refinement useful when a *hypothetical* strict system
has global `rank_Q(P)=2`:

> **Integral plane/eigenvalue certificate.** There is a
> nonzero **primitive integer row** `f in Z³`
> and an **integer** `lambda` such that
> `fP=0` and `fM=lambda f`. In particular
> `x-lambda` divides the incidence characteristic
> polynomial over `Z`.

**Proof.** Two rationally independent Parikh columns span the
rational image plane `W=im_Q(P)`. Take their nonzero integer
cross product and divide by the positive gcd of its three
coordinates; choose the sign so its first nonzero coordinate
is positive. The resulting primitive row `f` annihilates
every column of `P`. From (1), `f M P=f P N=0`,
so `fM` lies in the one-dimensional rational annihilator
of `W`; hence `fM=lambda f` for some rational
`lambda`. Because `M,f` are integral and `f`
has coprime entries, Bezout's identity gives
`lambda = lambda · (sum a_i f_i) = sum a_i(fM)_i
in Z`. Thus `lambda` is an integer eigenvalue
and `x-lambda` is a monic integral linear factor.
QED.

This proof is **conditional on rank exactly two and actual full
child closure**; it does not conclude that all phase-flat strict
systems have rank two. If rank is one, the certificate here
does not attempt to select a canonical 2-dimensional
annihilator. Under irreducible `chi_M`, rank two or one
is impossible by the prior rank theorem.

## 4. The exact four-state non-PIP flat-hub calibration

Use the actual closed strict system
`sigma=10/102/211` and states

```text
S0=(102,210)
S1=(11102,21110)
S2=(10210211,21110210)
S3=(10210210210211,21110210210210).
```

Complete ordered child rows:

```text
S0 -> [2]
S1 -> [3]
S2 -> [2,0,0,1,0]
S3 -> [2,0,0,1,0,1,0,1,0].
```

```text
M = [[1,1,0], [1,1,2], [0,1,1]],
P = [[1,1,2,4], [1,3,4,6], [1,1,2,4]],
N = [[0,0,3,5], [0,0,1,3], [1,0,1,1], [0,1,0,0]].
```

Check `P N=M P` by integer multiplication. The
complete depth-at-most-two cone ranks at roots
`S0,S1,S2,S3` are **[2,2,2,2]**, even though each
root's forest retains all repeated child occurrences.
Their total occurrence lengths (root included) are
`[7,11,15,23]`, which matter for the cap guard.

The primitive integral plane normal is exactly
`f=(1,0,-1)`:

```text
f P = (0,0,0,0),      f M = f,      lambda=1.
```

Thus this specimen has a genuine rational invariant
plane and integral eigenvalue one; its characteristic
polynomial factors as
`(x-1)(x²-2x-2)`. It is primitive and nonsingular
but **not irreducible Pisot**.

The existing first-child candidate-good-edge
classifier reports mask `0b011` (edge `{0,1}`
and edge `{0,2}`). For **each** compatible hub,
the *complete actual ordered* residual words are
`[0],[0],[0,0,0,0,0],[0,0,0,0,0,0,0,0,0]`,
so the separate all-child **flat-compatible mask**
is also `0b011`.

**Very important:** either bit is merely *compatible*
with a genuinely eventually coincident good edge.
The mask is not an occurrence-level Barge–Diamond
certificate. This specimen's reducibility prevents any
PIP conclusion. Flat all-child words and a rank-two
integer plane **coexist** here without C4 synchronization.

## 5. Canonical implementation and falsifiable replays

- `kernel/psc/c4_complete_cone_hub_audit.mojo`:
  builds the **literal** `DerivedSystem` from the complete
  supplied word list, checks each column of `P N=M P`,
  enumerates every root's exact depth-two child ordinals,
  builds deterministic integer rank pivots, computes the
  three-bit candidate good-edge mask and tests all actual
  child hub-residual bits for each compatible hub.
  If rank is exactly two, exports the primitive integer
  plane normal and checked integer `lambda`.
- `kernel/tests/test_c4_complete_cone_hub_audit.mojo`:
  pins all four root ranks, both masks, primitive `f`,
  `lambda=1`, source pivot ordinals and strict
  refusal controls.
- `tests/test_c4_complete_cone_hub_audit_oracle.py`:
  independently reconstructs **all literal balanced
  child blocks**, child incidence, every root's
  complete depth-two occurrence forest, the Parikh
  intertwiner, the two flat hub words, and
  `fM=f`, using integer-only standard-library Python.

**Independent local exact replay:** the complete four
source words, child ordinals, integer matrices,
`P N=M P` and all four root cone ranks were
reconstructed in a separate Python calculation
with ranks [2,2,2,2]. This is not a hosted Mojo
receipt; at authoring the new CI runs are pending.

From the repository root:

```sh
cd kernel && mojo run -I . tests/test_c4_complete_cone_hub_audit.mojo
cd .. && python -m pytest -q tests/test_c4_complete_cone_hub_audit_oracle.py
bash tools/verify_all.sh provenance
```

**Fail-closed negatives:** input list omitting S3 must
be rejected by actual child closure; a productive
Tribonacci recurrent source cannot be re-labelled
strict by dropping diagonals; caps 0 and 1 refuse
rather than treating a partial cone as a rank
counterexample; invalid image digits are refused
before an indexed word count. The code does not
touch vendored packages, claim governance or
generated Proof Bank inventories.

## 6. Remaining research target

Issue [#461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461)
asks for an independently justified **strict recurrent
whole-word** mechanism that promotes genuine phase-flat
ordered word constraints to a rank obstruction or directly
to `Sync_±`, preserving the irreducible Pisot premise.
Our exact rank-two certificate shows what the *output*
of a successful flatness-to-annihilator lemma would look
like; it **does not provide that missing lemma**.

The productive genuine-PIP flat-zero depth-two cone
retained in [PR #460](c4-two-generation-parikh-span-2026-11-02.md)
has full rank and determinant +1 before it exits at
depth three. Hence a proposed functional derived from
only a local flat cone would be false. Any proof must
use strict **all-child closure/recurrent continuation**,
not just a finite initial window or the merely
compatible hub mask.

A final review should check native Mojo exact-head CI
before promoting even this scoped implementation to
accepted evidence. Independent human review remains
final validation debt.
