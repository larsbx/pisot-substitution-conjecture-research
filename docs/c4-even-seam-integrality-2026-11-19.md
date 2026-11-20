# Integral grouped seam cycles in the ternary range

Research base: `c0231e0fd64d9eee7f7bb798042d9966276e4cd6`.
Integrated main: `017969364269c116aaa5873bfcba6c9f1b1ba7e5` (#621).
This is a finite refinement of the nonzero grouped-square condition in
the [even-stack reduction](c4-even-stack-residue-2026-11-19.md).

## Literature decision

**Proposed intermediate claim.** Let `G` be a finite simple bipartite graph
with at most three vertices on each side. Partition each side into two
groups and map an integral cycle to the sums of its coefficients in the
four grouped cells. If this map is nonzero, its image is the full integral
cycle lattice of the grouped square. Thus there is an integral cycle with
grouped coefficients `(1,-1,-1,1)`.

| Source | Transfer and boundary |
| --- | --- |
| [Barge--Diamond (2008), Theorem 4](https://arxiv.org/pdf/math/0702669) | The eventual-range graph contributes to first cohomology through its cycle group. The present graph calculation does not identify the grouped graph with the stack quotient. |
| [Barge (2015), Proposition 19 and Theorem 22](https://www.numdam.org/item/10.24033/bsmf.2691.pdf) | The stack pullback is rationally injective, while the lower bound of five in degree three requires odd norm. No integral primitivity claim for the stack pullback is inferred from this graph lemma. |
| [Barge--Kellendonk--Schmieding (2012), Corollary 3 and Theorem 5](https://arxiv.org/pdf/1204.1432) | The eigenfunction subgroup has torsion-free cokernel. This statement concerns the maximal equicontinuous factor, not every factor or covering pullback. |
| [Existing winding calculation](c4-rank-two-stack-cycle-exclusion-2026-11-19.md#effect-of-a-factor-identifying-periodic-seam-tilings) | The grouped rational cycle space is at most one-dimensional. The proposed calculation addresses its integral image on the original ternary graph. |

**Decision: proceed with the finite specialization.** Integral circulation
decomposition into oriented simple cycles is standard graph theory, not a
new mechanism. A simple cycle in this graph has four or six edges. For each
of these lengths test every two-group assignment; its square coefficient
must be `0`, `1`, or `-1`. Preserve an eight-edge counterexample on four
vertices per side, where the image is `2 Z`. Formalize the finite coefficient
claims; leave the graph decomposition and the geometric winding application
as separate written steps. Integral surjectivity alone does not contradict
the even-stack residue.

## Work shown

### Assumptions and hypotheses

The finite claims need only Boolean labels on alternating cycle vertices.
Their interpretation as simple cycles of `G` uses simplicity, bipartiteness,
and the three-vertices-per-side bound. They use no substitution, determinant,
Pisot, recognizability, finite-fibre, or stack hypothesis.

### Derivation / reduction

Orient the edges of `G` from the left side to the right side. Its integral
cycle lattice consists of integer edge vectors with zero row and column
sums. For a simple cycle write its alternating edge vector as

```text
+(r_0,c_0) -(r_0,c_1) +(r_1,c_1) -(r_1,c_2) + ...
```

with cyclic indices. Let `a_i,b_i` be the zero-group indicators of `r_i,c_i`.
The coefficient of its grouped `(0,0)` cell is

```text
k = sum_i a_i (b_i - b_(i+1)).
```

All grouped row and column sums are zero, so its four grouped coefficients
are `(k,-k,-k,k)`. If there are two or three vertices on each side of the
cycle, a cyclic Boolean sequence `b_i` has at most one transition from one
to zero and one from zero to one. Thus `k` is the difference of two Boolean
indicators, or zero: `k` belongs to `{-1,0,1}`. The Lean statements check
all sixteen four-cycle and sixty-four six-cycle assignments directly with
kernel reduction.

For completeness, the standard integral cycle decomposition can be applied
without rational denominators. Reverse an edge with negative coefficient
and give it the positive absolute coefficient. The zero divergence
condition allows any positive edge to be extended along positive outgoing
edges until a vertex repeats. Extract a simple directed cycle, subtract
the minimum of its edge weights, and repeat. Each step decreases the total
integer weight. This expresses the original circulation as an integer sum
of oriented simple cycles. A simple bipartite graph with at most three
vertices per side has only four- and six-edge simple cycles. If the
grouped cycle map is nonzero, some summand has `k != 0`, hence `k = 1` or
`k = -1`. Reverse its orientation in the latter case. This proves the
stated integral surjectivity theorem.

**Formal boundary.** Lean proves the finite coefficient statements and
their nonzero consequences. The integral decomposition just given and its
application to an actual eventual-range graph remain written arguments.
No theorem here constructs a stack factor or formalizes its cohomology.

**Consequence for the winding calculation.** Suppose the winding
functional on pullbacks of integral stack classes has the form `alpha k`
on original seam cycles, as in #617. The unit cycle makes `alpha` integral.
This rules out a denominator arising only from the grouped cycle image.
It does not prove that a covering pullback is primitive, or that a fifth
cohomology class exists.

An explicit algebraic control shows why. Let `E` be any torsion-free
abelian group of rational rank three and let `v` be a primitive vector in
`Z^l`. Set

```text
H_Y = H_X = E + Z,          H_original = E + Z^l,
p*(e,n) = (e,2n),           q*(e,n) = (e,nv),
transfer(e,n) = (2e,n),     deck* = identity.
```

Both compositions of transfer and `p*` are multiplication by two, the
deck-odd rational part vanishes, the eigenfunction subgroup `E` has
torsion-free cokernel, and the seam coordinate on the original graph is
primitive. These are compatible algebraic data. They are not realized
tiling spaces and do not supply a counterexample to C4 or PSC; they show
that the listed integral identities alone do not give a contradiction.

### Evidence and replay

The following local command passed with the pinned Lean `4.34.0-rc2`:

```sh
(cd proof/PscVerif && lake --no-cache build PscVerif.EvenSeamCycles)
```

The [Lean module](../proof/PscVerif/PscVerif/EvenSeamCycles.lean) contains
`four_cycle_coefficient`, `six_cycle_coefficient`, their two
`nonzero_is_unit` consequences, `eight_cycle_coefficient_two`, and
`eight_cycle_unit_bound_fails`. It uses kernel `decide`, without
`native_decide`, `sorry`, or added axioms. The aggregate audit and source
manifest are recorded with the parent proposal. No hosted acceptance is
asserted.

### Negative controls

Take four distinct row vertices and four distinct column vertices, the
eight edges `(r_i,c_i)` and `(r_i,c_(i+1))`, and both group sequences
`(0,1,0,1)`. This is a connected simple eight-cycle, with cycle lattice
generated by its alternating edge vector. That vector has grouped
coefficient two, so the image lattice is exactly `2 Z`. Thus the
three-vertices-per-side restriction cannot simply be removed. It is a
graph control, not a substitution counterexample.

### Non-claims / remaining gaps

The new finite bound cannot imply a fifth cohomology class. Passing from
grouped cycles to an obstruction for the actual cubic stack quotient still
requires a geometric or dynamical argument. The existing nilpotent case,
universal C4, and PSC remain open.
