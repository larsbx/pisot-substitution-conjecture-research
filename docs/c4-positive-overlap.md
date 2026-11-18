# Positive measure from original balanced cuts

## Pre-code decision

Proceed with a conditional quantitative lower bound for the compact union
of represented overlaps in the two named fixtures. The earlier
[cell-packing literature review](../evidence/c4-finite-cut-count-2026-11-12/future/cell-packing-literature-review.md)
examines the geometry of non-unit Pisot substitutions, Haar fundamental
domains and outer regularity. For this consumer, the closest construction
is the original diagonal representation in Minervino and Thuswaldner,
[The geometry of non-unit Pisot substitutions](https://arxiv.org/abs/1402.2002).
Use only the actual chart, carrier and finite packing already formalized
in #561. No tiling or multiplicity theorem from that paper enters the proof.
The pinned Mathlib sources for the
[compact tube lemma](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactness/Compact.html#generalized_tube_lemma)
and [open approximation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Regular.html#Set.exists_isOpen_lt_of_lt)
give the two analytic transfers. They require compactness and continuity
for the tube, and outer regularity for open approximation. A moving cell
width or a bounded strip can absorb a density deficit. A target failing to
contain the overlap cannot be used to capture the cuts.

## Work shown

### Assumptions and hypotheses

Fix either named fixture, a finite actual strict system `C`, and an
additive Haar probability measure on its original matrix-adic carrier.
Write `μ` for the product of stable-coordinate volume and this measure.
For the quantitative theorem, let `L > 0` bound all physical top-factor
lengths in `C`. The qualitative corollary takes the maximum over `C`.
Nonemptiness and the block condition supply a positive maximum.

### Derivation / reduction

The common cell mass is `c > 0`. Given a finite-measure open superset
`O` of `carrierOverlap`, apply the compact tube lemma to the preimage of
`O` under addition and to `carrierOverlap × {0}`. It gives an open
capture set `U` and a zero neighborhood `V` with `U + V ⊆ O`.

Fix a single admissible block depth `12*d` for `V`, with physical
width `W`. For a fixed member `T` of the strict carrier, let `Xₙ` be
its inflated top-word length. The same integer finset `Zₙ = integerStarts f n T`
enters both inequalities. The count gives `Xₙ ≤ L * |Zₙ|`. Capture in
`U` and the physical strip place the translates in the packing rectangle,
giving `c * |Zₙ| ≤ (Xₙ + W) * μ.real O` for every sufficiently large `n`.
There is no cardinality comparison with a projection or a set of labels.

The block condition and positive letter weights give a positive source
length. Since `β > 1`, `Xₙ → ∞`. If `b = μ.real O < a = c/L`,
the inequalities would imply `Xₙ * (a - b) ≤ W * b`. Eventual growth
past `W * b / (a - b)` contradicts that bound at the fixed depth.
Outer regularity then yields `ENNReal.ofReal (c/L) ≤ μ carrierOverlap`.
The measure proof uses the topology induced from the countable product
of finite discrete residue spaces and the actual stable-coordinate
product topology.

### Evidence and replay

From the repository root with the pinned toolchain and Mathlib cache:

```sh
(cd proof/PscVerif && lake build PscVerif.NamedPositiveOverlapControls)
./tools/check_lean.sh
```

The first command builds the two bridge modules and their dependencies.
The second is the isolated acceptance gate for the aggregate and its
compiled declarations.

### Negative controls

`NamedPositiveOverlapControls` encodes the constant-strip and
moving-width counterexamples, failure of the compact tube when the
target omits the overlap, and a null singleton with a positive-measure
open superset. Its dependencies include the exact matrix-adic controls
from #561 for a coarser residue depth (disjointness fails) and a finer
residue depth (coverage fails).

### Non-claims / remaining gaps

The theorem takes a supplied actual strict system. It gives a bound
for the union of its represented overlaps. The cell mass remains
symbolic. No governed claim is promoted.
