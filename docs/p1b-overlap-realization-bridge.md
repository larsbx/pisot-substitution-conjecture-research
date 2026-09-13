# P1-B — balanced-pair to overlap realization bridge

**Status:** theorem-facing program and exact finite diagnostic for the open G1b-2 gate. This note does **not** identify the repository seed-patch overlap graph with the complete overlap graph of the literature, does not prove relative density of simultaneous boundaries, and does not prove G1b-2.

## 1. Why this route is being tested

The affine-ancestry work explains the last retained finite sidewise-abelian collision by a symbolic pump, but its remaining uniform theorem still has two clauses:

1. repeated affine states must be removable without leaving the relevant realizability/context class;
2. loop-free realizable traces must form a uniformly finite family under a fixed discrepancy bound.

The geometric overlap formulation is useful because **realized** tile overlaps are the native objects in which finite-local-complexity/Meyer arguments apply. The literature connection must nevertheless be kept separate from the repository's formal balanced-pair graph.

Literature targets to pin before any ledger promotion:

- Sirvent--Solomyak, *Pure Discrete Spectrum for One-dimensional Substitution Systems of Pisot Type* (2002), for the one-dimensional relation between balanced-pair and overlap algorithms;
- Akiyama--Lee, *Algorithm for determining pure pointedness of self-affine tilings* (2011), for overlap coincidence and pure point spectrum in the stated self-affine/Meyer setting;
- Lee--Solomyak, *Pisot family self-affine tilings, discrete spectrum, and the Meyer property* (2012), for the precise hypotheses under which the Pisot-family condition gives the Meyer property;
- Minervino--Thuswaldner, *The geometry of non-unit Pisot substitutions* (2014), for the non-unimodular representation-space setting.

These are citation targets, not imported theorem nodes in this note.

## 2. Exact geometric coordinate and rational interval layer

Let `M` be the incidence matrix and `beta` its irreducible cubic Pisot Perron root. A positive left Perron eigenvector gives tile lengths

```text
ell^T M = beta ell^T.
```

The canonical Mojo kernel represents every length and displacement exactly in

```text
Z[beta] = {a0 + a1 beta + a2 beta^2 : ai in Z}
```

modulo the monic characteristic polynomial.

### 2.1 Rational interval arithmetic is the first enclosure layer

The Perron root is first enclosed in an exact checked rational interval

```text
beta in [p/q, r/s].
```

The box is obtained from an integer sign-change bracket and a bounded number of exact rational bisections. Every endpoint operation is normalized and checked against fixed-width overflow. If an endpoint or intermediate cannot be represented safely, interval refinement fails closed rather than widening silently or wrapping.

For any cubic-field element

```text
x = a0 + a1 beta + a2 beta^2,
```

the kernel evaluates the **natural rational interval extension** of

```text
a0 + a1 X + a2 X^2
```

over the current beta enclosure. This produces a certified rational interval `I(x)` satisfying

```text
x(beta) in I(x).
```

The sign rule is deliberately strict:

```text
I(x) entirely > 0  =>  x(beta) > 0
I(x) entirely < 0  =>  x(beta) < 0
0 in I(x)           =>  unknown
```

An interval containing zero is never interpreted as equality, failure, or a negative result. This is the key theorem-facing discipline: interval arithmetic supplies positive enclosure certificates only.

### 2.2 Exact algebraic fallback

When the rational enclosure straddles zero, or interval arithmetic itself cannot proceed safely within fixed-width integers, the kernel delegates to the independent specialized Sturm--Tarski signed-remainder query. That fallback uses checked integer arithmetic and no rational refinement.

Thus the order-decision architecture is

```text
checked rational interval enclosure
        |
        +-- strict sign certified --> accept sign
        |
        +-- zero contained / unsafe --> exact Sturm--Tarski fallback
```

The Codex near-Perron counter-calibration

```text
-152138 + 67035 beta
```

is intentionally retained: a modest rational interval remains ambiguous, while the algebraic fallback resolves the sign exactly. This prevents the interval layer from being mistaken for a completeness oracle.

No floating point, inverse incidence matrix, Euclidean stable-space lattice, or unimodularity assumption is used. Arithmetic overflow fails closed and makes a finite run inconclusive.

The current PIP-validation boundary is deliberately restricted to the audited repository census domain: non-erasing three-letter substitutions with every image length at most three. This finite precondition is checked before calling the older fixed-width PIP predicate. Larger incidence matrices are rejected as unsupported rather than risk overflow and false classification.

For an oriented overlap state

```text
(i, j, t),
```

the top tile is `[0, ell_i]` and the bottom tile is `[t, t + ell_j]`. It is an interior overlap exactly when

```text
t < ell_i,
t + ell_j > 0.
```

These two inequalities are now routed through the rational-interval-first sign path above. If the interval box certifies the sign, the box itself is finite evidence; if not, the exact algebraic fallback decides the comparison.

If the selected top and bottom children have geometric prefix translations `p` and `q`, inflation sends the displacement to

```text
t' = beta t + q - p.
```

A tile coincidence is exactly

```text
i = j,
t = 0.
```

All of these predicates are exact in the finite executable kernel.

## 3. Repository seed-patch overlap graph

The first diagnostic starts from the same unordered letter pairs `a < b` used by the repository BPA, but geometrizes the two seed words:

```text
ab
ba
```

with their left boundaries aligned. Every pair of seed tiles with nonempty interior intersection produces an oriented overlap state. The graph then repeatedly applies the exact inflation rule above and retains only child pairs that still overlap.

Coincidence states are terminal for the same finite productivity question used by `B_sigma`: whether every reachable state can reach a tile coincidence.

The construction has a state cap. A capped run is inconclusive, and productivity queries on a capped graph fail closed.

### Scope warning

This seed-patch graph is **not yet the literature overlap graph**. The literature algorithm ranges over the appropriate realized overlap classes/return translations of the tiling. The current graph is a deliberately auditable subset generated from the repository seed patches. Agreement of its productivity verdict with the BPA on a finite corpus is evidence for the dictionary, not proof of it.

## 4. The bridge is path-valued, not vertex-valued

A reduced balanced pair `(u,v)` spans an interval between two simultaneous boundaries of two aligned patches. In general that interval contains several top and bottom tiles. Therefore it should not be identified with one overlap vertex.

The appropriate candidate map is

```text
realizable reduced balanced pair
    -> finite ordered chain of tile-overlap states
```

covering the common geometric interval between its two simultaneous boundaries.

This corrects an overstrong possible interpretation of the cross-program audit: the desired correspondence is not a graph isomorphism between BPA vertices and overlap vertices.

The theorem-facing commutative diagram should instead establish:

1. **realization:** every realizable reduced balanced pair determines such a finite overlap chain;
2. **inflation compatibility:** inflating the balanced pair and refining its overlap chain give the same child geometry;
3. **cut compatibility:** common Parikh-prefix returns are exactly the simultaneous-boundary cuts of that realized chain;
4. **coincidence compatibility:** a balanced-pair coincidence corresponds to a full-tile coincidence in the chain;
5. **finite-type consequence:** under the exact literature hypotheses, the relevant realized overlap classes are finite, and a uniform bound on chain length between simultaneous boundaries yields G1b-2.

Items 1--5 are theorem targets. The executable graph tests only finite instances of the local geometry.

## 5. Relation to the affine pump program

The affine state

```text
(top_current_letter, bottom_current_letter, x_t)
```

records ordered substitution ancestry and exact prefix displacement information. A repeated affine state is a symbolic loop candidate. The overlap chain supplies the missing geometric question: does deleting that ancestry loop preserve the same realizable overlap/context class?

Thus the two approaches are complementary:

```text
affine trace       -> exact symbolic loop candidate
rational intervals -> certified geometric enclosures
overlap geometry   -> realizability / finite geometric type
```

Neither implication is assumed. A future proof should make the compatibility explicit rather than replacing one representation by the other by analogy.

## 6. Immediate executable acceptance criteria

For a controlled PIP specimen, the Mojo diagnostic must:

- construct positive Perron tile lengths exactly;
- construct a checked rational interval enclosing the Perron root;
- implement natural rational interval extension for integer polynomials;
- certify a sign only when the complete rational enclosure excludes zero;
- retain a near-boundary regression where interval arithmetic is intentionally inconclusive and exact algebraic fallback is required;
- fail closed on rational endpoint overflow and interval division across zero;
- enumerate seed-patch overlaps without floating point;
- fail closed on malformed/non-PIP input;
- reject substitutions outside the audited image-length-at-most-three input domain before invoking the legacy fixed-width PIP validator;
- terminate below the state cap or report inconclusive;
- reject productivity queries on capped partial graphs;
- retain exact coincidence reachability;
- compare its finite productivity verdict with the repository BPA without asserting equivalence.

Only after these regressions are pinned should the same comparison be run over the full 4,554-specimen finite corpus.

The canonical Mojo run for the determinant-two calibration produces exactly

```text
initial seed-overlap states: 9
reachable seed-overlap states: 628
nonproductive reachable states: 0
```

These three finite counts are pinned in regression coverage. They apply only to the stated seed-patch construction for this specimen; they do not identify it with the complete realized-overlap graph or establish any uniform bound.

## 7. Theorem boundary

A clean finite corpus would not prove any of the following:

- that the seed-patch graph equals the complete realized-overlap graph;
- that every formal BPA state is globally realizable;
- that simultaneous boundaries are relatively dense in every relevant fibre pair;
- that overlap-chain lengths are uniformly bounded;
- G1b-2 or G1.

The current objective is to turn the realization gap into an exact, falsifiable geometric interface in which rational interval boxes are first-class finite certificates and exact algebraic queries settle only the unresolved boundary cases. G1b-2 remains open.
