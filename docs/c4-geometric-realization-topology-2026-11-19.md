# Topology of the concrete realization target

## Source decision

The starting revision `c0231e0fd64d9eee7f7bb798042d9966276e4cd6` includes
PR #618's algebraic solenoid realization and PR #620's spectral contraction.
The remaining claims carried forward from the reviewed stable-coordinate patch
are compact Hausdorff topology on that target, continuity of its shift and
flow, and an actual hull witness for loss of the past under projection to
depth zero.

Baker–Barge–Kwapisz §3, equations (3.8), (3.10) and (3.12), describe the
inverse limit of the quotient endomorphism, the shift and the induced flow.
Their return-lattice identification is used at the irreducible boundary.
Barge–Diamond–Swanson §2 distinguish the projected-letter lattice from the
optimal return lattice and use the usual topology of the legal tiling hull.
Barge–Kwapisz §§5–6 describe the unit case in which a torus suffices. The
topology of the inverse-limit target transfers directly. Adjacency,
continuity of desubstitution and the ordinary hull topology are separate
obligations. Proceed with target topology and a literal nonunit test using
the current matrix and flow. [BBK](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf)
[BDS](https://www.impan.pl/shop/en/publication/transaction/download/product/89123)
[BK](https://math.montana.edu/jarek/documents/papers/AJM2006.pdf).

The current Thue–Morse control only detects a kernel in the torus
endomorphism. Its unstable vector is `(1/2, 1/2)` in the current integer
lattice chart. Translating by two, in this normalization, gives the same
depth-zero class and changes depth one. Use a legal periodic seed for a
tiling with a verified origin cut. The test continues to take bijective
inflation for this hull as an input.

## Work shown

### Assumptions and hypotheses

The topology uses the existing integer lattice and its torus quotient for a
finite alphabet. The inverse limit uses the existing incidence endomorphism,
with no determinant restriction. Continuity of the target flow uses the
existing `PisotData` for its direction vector. The concrete hull check takes
bijective inflation as a premise and uses the checked Thue–Morse data.

### Derivation / reduction

Subtract the coordinatewise integer floor to put a representative of every
torus point in the compact unit cube. The lattice is closed, so the quotient
is also Hausdorff. The inverse limit is the closed intersection of the
coordinate compatibility sets in the product of those tori. The shift
applies the continuous induced matrix in every coordinate. Its inverse
deletes coordinate zero, which is continuous in the product topology.
At each level the flow adds the quotient of a continuous linear function of
time, proving joint continuity.

Inflating a growing legal seed and taking the increasing union now produces
a tiling containing that seed and fixed by the chosen power of inflation.
For the Thue–Morse seed `1.0` the power is two. Forward R4 realizes that
tiling to zero. The unit tile after the seed ends at physical position two,
so the translate by two still has a cut at zero. The flow adds `(1, 1)` at
depth zero and `(1/2, 1/2)` at depth one. Only the first vector is integral.

### Evidence and replay

`PeriodicPartnerRealization` contains `torus_compactSpace`,
`solenoid_compactSpace`, `solenoid_t2Space`, `shiftHomeomorph` and
`continuous_flow`. `PeriodicPartnerRealizationModels` contains
`thueMorse_flow_two` and `thueMorse_hull_depth_zero_loses_information`.
These are included in the existing scoped axiom and exact source checks.

```sh
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
```

### Negative controls

The two Thue–Morse tilings both have a cut and the same depth-zero class.
The shifted tiling's depth-one class excludes it from the zero fibre. This
detects loss of the past in the actual realization and shows why forward R4
requires periodicity. The existing Fibonacci first-coordinate injectivity
test exercises the unit case.

### Non-claims / remaining gaps

The new topology is on the target. The source still has the exact-agreement
ultrametric. Continuity on the ordinary tiling hull, correspondence with the
published normalized BBK map, recognizability and finite fibres remain
separate obligations. No strict-system exclusion or governed claim changes.
