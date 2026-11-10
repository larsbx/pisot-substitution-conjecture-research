# Concrete C4 occurrence and newborn extraction

This development advances the concrete bridge in the
[C4 next-obligations note](c4-next-proof-obligations-2026-11-10.md).
Its source is
[`PscVerif/OccurrenceNewborn.lean`](../proof/PscVerif/PscVerif/OccurrenceNewborn.lean),
following the recorded
[literature stop/go](c4-concrete-occurrence-literature-2026-11-10.md).
The finite controls remain the canonical Mojo addressed replay and its
independent Python oracle. General C4 and uniform forced-crossing
productivity remain open.

| Lean result | Exact conclusion | Boundary |
| --- | --- | --- |
| `red_common_factor` | Strictly overlapping selected tile occurrences in `red` have the same factor ordinal and label. | Inputs are already located in the factorization. |
| `physicalLength_eq_iff` | Equal prefix lengths under a nonzero eigenrow of an irreducible rational cubic are exactly Parikh equality. | This derives rational independence; reducible matrices are excluded. |
| `physical_diagonal_newborn` | A supplied one-step physical diagonal has an exact singleton ordinal and interior `SyncPlus` or `SyncMinus` newborn. | Immediate parent is irreducible and noncoincident; substitution is nonerasing. |
| `coincidence_child_newborn` | An actual coincident child is a singleton and gives a newborn. | Uses the complete `red` child relation. |
| `child_path_newborn` | A literal path to coincidence has a reachable noncoincident immediate parent with a synchronized newborn. | Packet paths must still be refined into these literal paths. |

## 1. Literal words and exact factor ordinals

The source reuses `Binomial.subst`, `Equiv1`, `IrreduciblePair`,
`Reduction.red`, and `IsBlock`. It introduces no substitute child relation.

For literal decompositions

\[
U=p_u a s_u,\qquad V=p_v a s_v,
\]

with `Equiv1 p_u p_v` and `Equiv1 U V`,
`red_split_at_diagonal` proves the exact ordered equality

\[
\operatorname{red}(U,V)=
\operatorname{red}(p_u,p_v)\;[(a,a)]\;
\operatorname{red}(s_u,s_v).
\]

`diagonal_factor_ordinal` locates the singleton at ordinal
`length (red p_u p_v)`. This retains a selected occurrence when identical
factor words appear repeatedly. No finite-state, Pisot, irreducibility or
legality hypothesis is required for this word factorization.

## 2. Common-factor geometry

`FactorOccurrence` contains an ordinal, the factor at that ordinal, and an
actual decomposition of one of its tracks into a prefix, one selected
letter and a suffix. Its global physical start is the length of all
preceding factors on that track plus the local prefix length. Its finish
adds the selected letter's length.

`FactorOccurrence.bounds` derives containment in the selected factor's
physical interval. Each factor's balance makes the two track boundaries
coincide. `common_factor_ordinal` then proves that two such occurrences
whose interiors strictly intersect have the same factor ordinal.
`red_common_factor` specializes this to the actual complete zero-return
reduction and returns both ordinal equality and factor equality.

This argument only needs nonnegative tile lengths together with the stated
strict interior intersection; the reduction wrapper uses positive lengths.
It needs no rational-independence premise. A boundary touch is insufficient:
two adjacent factors may share a boundary without having a common interior.

The occurrence inputs are already located in the factorization. The module
does not yet prove lookup/coverage from arbitrary global source addresses,
transport complete digit-address histories or residual vectors through
packet normalization, or establish consistent lifting of abstract paths.
Those are separate refinement obligations.

## 3. Physical alignment gives Parikh alignment

`physicalLength` is the actual prefix Parikh vector evaluated by a real
length row. Let `M` be a rational ternary matrix with irreducible
characteristic polynomial, and let the nonzero row `ell` satisfy
`ell M = beta ell`. `rational_length_injective` proves

\[
\ell w=0,\quad w\in\mathbb Q^3\quad\Longrightarrow\quad w=0.
\]

It applies the existing cyclic-vector theorem to `w,Mw,M²w`: a nonzero
rational vector is cyclic, so an eigenrow annihilating it would annihilate
a basis and be zero. `physicalLength_eq_iff` applies this to the difference
of two literal prefix count vectors. Thus equal physical lengths imply
equal Parikh columns and equal combinatorial prefix lengths. Rational
independence is a consequence of irreducibility, not a new assumption.

The final geometric theorem uses the substitution's own incidence matrix
and a positive left eigenrow. It does not require unimodularity. The local
argument also needs no Pisot modulus restriction; that restriction belongs
to the still-open global productivity argument.

## 4. A singleton gives a synchronized newborn

`InheritedCut s u v k` means that `k` is the inflated length of an actual
balanced prefix of the immediate parent. `NewbornCut` requires an interior
zero return of the one-step image that is not inherited.

For an irreducible parent, `interior_not_inherited` derives that every
interior image cut is noninherited. The parent has only its two endpoint
returns, whose inflated positions are again endpoints. A noncoincident
balanced parent has at least two letters; nonerasure preserves that lower
bound in its image.

`aligned_letter_newborn` now makes a concrete choice:

- if `p_u` is nonempty, choose its length as the cut. It is an interior
  newborn and the selected common letter lies immediately to its right
  (`SyncPlus`);
- if `p_u` is empty, both prefixes are empty. Choose cut one. The image
  length is at least two, so the cut is interior, and the selected common
  letter lies immediately to its left (`SyncMinus`).

`physical_diagonal_newborn` composes physical-to-Parikh alignment, exact
singleton location and this newborn extraction. Its conclusion retains the
immediate parent and the exact singleton ordinal. The side of an earlier
endpoint witness and the side of this newborn are distinct data.

`singleton_child_newborn` reconstructs actual prefix and suffix words from
membership of the singleton in the complete reduction.
`coincidence_child_newborn` derives singleton shape from irreducible
factorization. Finally, `child_path_newborn` finds the first coincident
child along a literal `Descendants.Child` path and returns its reachable
noncoincident parent, its `IsBlock` proof, and the synchronized newborn.
If a supplied component is child-closed, existing path-membership theorems
keep that returned parent inside the component.

## 5. Remaining composition and acceptance boundary

The geometric theorem begins with a supplied actual diagonal occurrence
in the one-step image of an irreducible noncoincident parent. The path
wrapper begins with a path in the literal complete child graph. Applying
either theorem to a fully addressed packet route still requires the
route's word refinement to provide the literal path or the immediate
parent and occurrence. The existing executable addressed replay does this
for its accepted finite receipts; its complete universal refinement is
not supplied here.

Likewise, `red_common_factor` proves uniqueness once the selected tiles are
located as factor occurrences; it does not yet prove the full packet
soundness/completeness contract. Strict child closure already excludes
literal coincidence descendants through `StrictSystem.not_productive`.
The remaining new connection is from the full marked-occurrence transition
system into those literal child paths, followed by the uniform argument
forcing one productive crossing.

No general C4, Concentration, G1 or PSC status is promoted by this work.
Exact Lean compilation, kernel/axiom audit and finite replay receipts must
be attached to the reviewed revision before integration.
