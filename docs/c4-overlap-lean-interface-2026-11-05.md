# Lean verification interface for the C4 overlap certificates

**Scope:** a deductive Lean layer for the inference used by PR #496, with
explicit geometric and certificate-data inputs. This does not claim a complete
Lean proof of the concrete 18-source overlap theorem, general C4, or PSC.
Claim statuses and proof-ledger dependency edges are unchanged.

The implementation is
[`PscVerif.OverlapContraction`](../proof/PscVerif/PscVerif/OverlapContraction.lean),
imported by the root library and reached by the existing full declaration and
axiom audit. There are no new axioms, admitted proofs, native evaluation
axioms, or opaque assumptions declared as global facts. Hypotheses appear as
ordinary theorem arguments.

## What Lean verifies

| Declaration | Deductive content | Inputs still supplied by its caller |
|---|---|---|
| `fixed_of_unique_iterate` | A unique fixed point of `F^m` is fixed by F | The fixed point and uniqueness |
| `invariant_of_contracting_iterate` | A fixed point of a contracting iterate is fixed at every step | A metric space, contraction and fixed-iterate identity |
| `block_fixed_of_period` | A period-q identity gives a period-m identity when q divides m | The actual period identity |
| `period_three_two_step` | `F^3 K=K` and a contracting `F^12` imply `F^2 K=K` | The actual compact-prefix operator and its contraction |
| `zero_of_subinvariant` | Finite weighted-maximum argument forces zero mass | Nonnegative masses, positive weights, complete recurrence and a strict rate gap |
| `Certificate.check_iff` | Boolean integer validation is equivalent to the stated inequalities | A typed occurrence graph and integer weights |
| `Certificate.sound` | Accepted integer inequalities imply zero for any real mass vector satisfying the recurrence | The recurrence and a strict spectral gap |
| `recurrence_of_cover` | Complete occurrence covers and per-piece scaling imply the real mass recurrence | Actual sets, finite measures, complete cover and scaling |
| `null_of_cover` | The cover plus positive subinvariant weights forces null overlaps | The same concrete geometric inputs |
| `Certificate.null_of_cover` | Composes integer validation with the measure-cover theorem | Accepted data and geometric bindings |
| `Certificate.class_rate_null` | Specializes to rate `102/20` and `beta^2>103/20` | A valid imported certificate, complete cover and scaling |
| `no_positive_subset_of_null` | A set inside a finite union of null roots cannot have positive measure | The strict-cut carrier inclusion and its positive lower bound |
| `product_scaling` | `(D/beta)*(1/D)=1/beta` | The fact that the two actual measure factors have these values |
| `common_box_arithmetic` | Checks the exact rational norm and box inequalities in the note | The actual matrix-entry and complete digit enclosures |

The finite comparison is not a floating-point spectral computation. It
chooses a maximum of `v_i/w_i`, propagates the bound through all occurrence
indices, and uses a strictly smaller weight rate than the scale. The natural
certificate checks positive weights and denominator and every integer row
inequality before the real soundness theorem applies.

Each row has its own finite occurrence type `Fin (degree i)`. Two occurrences
with the same target remain two different indices and two terms in the sum.
The checker never replaces an occurrence list by its set of target vertices.
Typed targets exclude out-of-range indices inside the Lean model. A future
external packet decoder must prove that it constructs exactly these rows;
the type alone does not authenticate a packet.

The measure theorem uses finite-union subadditivity, not measure-disjointness.
It first proves the inequality in extended nonnegative reals, then converts
to real values using the explicit finite-measure hypotheses. Thus infinity
cannot silently become zero under `toReal`.

## Counter-calibrations checked in Lean

`six_parallel_edges_refused` rejects the one-vertex, six-occurrence graph at
rate `102/20`: its left integer sum is 120 and its right side is 102.
`zero_weight_refused` rejects a zero weight; `terminal_control_accepted`
accepts a positive-weight terminal row. `equal_rate_does_not_force_zero`
exhibits a valid one-loop certificate with positive mass when the spectral
gap is only equality. `period_alone_does_not_supply_two_step` uses a genuine
three-cycle to show that period three alone does not justify a two-step
equation. The contraction hypothesis is essential.

## Exact remaining bindings

The first layer does not turn the following obligations into axioms or mark
them as discharged:

1. Import all 18 canonical graph packets and weights into typed Lean data,
   preserving state order, occurrence multiplicity, all rows and the complete
   finite source domain. Then establish `Certificate.check = true` by
   kernel-checked computation. The small controls above are not a substitute
   for the 285,786-state packet.
2. Prove the graph-construction refinement: actual paired prefix occurrences
   give the recorded targets; nonintegrality and strict box separation are
   sound empty-piece tests; caps cannot omit an occurrence. A favorable
   matrix detached from the complete geometric cover cannot discharge this.
3. Construct the specified matrix-adic completion, its Haar measure and the
   index-two image; establish the actual product-measure scaling. The scalar
   cancellation lemma is only the last algebraic step.
4. Construct the compact-prefix operator on the complete Hausdorff space;
   prove the displayed block and digit enclosures imply its `F^12`
   contraction and bind the actual prefix sets to it. The period-three
   inference is now formalized after these inputs.
5. Formalize the fixed-origin cylinder/regular-box counting and strict-cut
   approximation proving the positive lower bound `kappa/L_max`, with the
   same measure normalization as the graph theorem. The final contradiction
   is formalized after that positive-measure input.

These are the boundary between the new formal inference and the remaining
written geometry, representation and data-refinement proofs. The existing
native/Python parity receipts do not themselves close that boundary.

## Replay and provenance

From the repository root:

```sh
./tools/setup_lean.sh
./tools/check_lean.sh
```

The required acceptance path compiles source copies in an isolated workspace
using the pinned Lean `4.34.0-rc2` release and Mathlib revision
`4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`. Its declaration audit accepts only
`propext`, `Classical.choice`, and `Quot.sound`, and checks that every inventoried
named proof is reached. The focused `C4 overlap Lean verification` workflow
checks out the exact PR head and retains the audit log as an artifact.

Local validation records are in
[`evidence/c4-overlap-lean-2026-11-05`](../evidence/c4-overlap-lean-2026-11-05/README.md).
Compilation of the generic module is separate from validation of all 18
concrete packets. The latter remains explicitly unimplemented here.

## Prior art and decision

This formalizes an already audited proof interface rather than proposing a
new universal invariant. The existing overlap note's
[literature check](c4-pair-overlap-graph-2026-11-05.md#2-prior-art-and-stopgo)
remains applicable: use direct graph-directed measure containment and retain
the compact-model scope. No Akiyama–Lee tiling/PDS equivalence or alternate
adelic representation theorem is imported.

The pinned Mathlib
[`ContractingWith` development](https://github.com/leanprover-community/mathlib4/blob/4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09/Mathlib/Topology/MetricSpace/Contracting.lean)
already contains fixed-point uniqueness and contracting-iterate results.
The formal layer reuses that theory and standard finite-union measure
inequalities. Its contribution is the explicit occurrence-certificate
interface and its composition with the weighted comparison, not a new Banach
fixed-point theorem. Proceed with the narrow formal layer; require the five
concrete bindings above before describing PR #496 itself as fully Lean verified.
