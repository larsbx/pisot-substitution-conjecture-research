# C4: actual inverse occurrences and track-swap quotient counts

Date: 2026-11-10. Base:
[`main@2099102`](https://github.com/larsbx/pisot-substitution-conjecture-research/commit/209910264171fef550938dd566213c19734a75b6),
the merge of [PR #536](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/536).
The [targeted literature stop/go](c4-inverse-occurrence-literature-2026-11-10.md)
preceded proof and control implementation. No governed claim is promoted.

## 1. The missing adapter

The preceding [ordered overlap-mass package](c4-overlap-mass-2026-11-10.md)
provides exact subdivision and weighted finite double counting. Its
quotient-count theorem requires uniform forward and incoming counts on
every label fiber. Calling a graph a track-swap quotient does not prove
that condition. Canceling the weights additionally requires a common
nonzero fiber size.

This package adds 69 named Lean proofs in two modules: 32 inverse-occurrence
proofs and 37 orbit-count proofs. It binds those premises to actual image occurrences. The
inverse equation is the reversal of a forward digit edge, with both
literal marks retained. Physical interior transfers from an inverse
source to its ancestor under exact positive image scaling. A diagonal
packet has only diagonal interior descendants. Thus backward ancestry
of nondiagonal interior roots has no fixed track-swap packets. Finally,
a finite swap-closed domain, retaining all digit occurrences whose two
endpoints lie in it, supplies an actual edge involution and uniform
counts on the exact swap orbits.

| Formal layer | Object retained | Scope boundary |
| --- | --- | --- |
| [OccurrenceInverse](../proof/PscVerif/PscVerif/OccurrenceInverse.lean) | Both incoming marks, the integral inverse equation, physical strip and diagonal ancestry | No existence of an integral preimage is inferred from a rational or approximate solution |
| [OccurrenceSwapCounts](../proof/PscVerif/PscVerif/OccurrenceSwapCounts.lean) | Finite ordered states, distinct digit-position pairs, actual swap orbits and their edge bijections | The finite domain is supplied; geometric completeness and finiteness are not constructed |
| [Native and Quint controls](c4-inverse-occurrence-controls-2026-11-10.md) | Concrete integral occurrences, repeated labels, orbit sizes and weakened variants | Declared finite domains, not a universal Pisot census or a new productivity theorem |

The finite domain need not be forward closed. All edges *inside* that
domain are retained, while outgoing edges to packets outside it remain
external. This matters when connecting an inverse ancestry graph to a
forward physical-mass budget.

## 2. Reverse the edge without erasing its identity

Use the existing top-minus-bottom packet convention. Let the current
packet be `p=(a,b,z)` and a proposed ancestor be `u=(A,B,y)`. Select actual
marks

\[
s(A)=P\,a\,S,\qquad s(B)=Q\,b\,T.
\]

The inverse equation is

\[
M y=z+\pi(Q)-\pi(P).
\]

It is equivalent, with the same two selected occurrences, to the forward
equation

\[
z=M y+\pi(P)-\pi(Q).
\]

Here a mark contains its prefix, selected letter and suffix. Its numeric
position is the prefix length. The already checked `markEquiv` identifies
these full marks with valid image positions, so reversing the equation
does not replace occurrences by their selected letters or resulting packet
labels. Two distinct digit pairs producing the same packet remain two
edges.

No determinant assumption is used in this reversal. In particular, the
equation is meaningful for nonunit and singular incidence matrices. It
requires an actual integral solution `y`; it does not construct one by
division or promise uniqueness. `iterateImages s k` uses the actual
iterated words; `incidenceZ_iterateImages` proves that their incidence is
`(incidenceZ s)^k`. `InverseOccurrence.iterate_equation` therefore exports
the powered equation for the very same incoming marks, including `k=0`.

Track swap sends `(a,b,z)` to `(b,a,-z)`, exchanges `P,a,S` with
`Q,b,T`, and therefore exchanges both selected positions. Swapping only
letters or residual signs would not authenticate the reversed occurrence.

## 3. Interior and diagonal ancestry

For a positive length row `ell`, the existing geometric interior predicate
is equivalent to

\[
-\ell_a<\ell z<\ell_b.
\]

Suppose `beta>0` and every image satisfies
`physicalLength ell (s A)=beta*ell_A`. The actual top prefix obeys

\[
0\le |P|_\ell,\qquad |P|_\ell+\ell_a\le\beta\ell_A,
\]

and the bottom prefix has the analogous bounds. Applying `ell` to the
inverse equation and combining these inequalities with the child strip
gives

\[
-\beta\ell_A<\beta\ell y<\beta\ell_B.
\]

Division by positive `beta` gives the ancestor strip. A merely positive
length row does not give the required image equations. The wrong-row
control from the preceding package remains a rejected premise.

The diagonal argument uses a different, weaker set of assumptions.
`Diagonal` means equal packet letters and zero **integral** residual.
Both forward image partitions are then the same word at the same
position. Two actual letter occurrences in this word can have a common
strict interior only if they are the same position. Their literal
prefixes and selected letters agree, so the child is diagonal. This
allows nonnegative lengths, with a strict child interior, and uses actual
word positions; it needs no exact
image scaling or injectivity of the physical length map.

Consequently, any finite backward path of interior digit edges starting
from a nondiagonal interior root excludes diagonal ancestors. A packet fixed by
track swap has equal letters and `z=-z`; over integral vectors this
forces `z=0`. Such backward ancestry is therefore free of fixed swaps.
If the state domain contains extra packets beyond that ancestry,
freeness of those extra packets must still be proved.

Physical alignment `ell*z=0` is not substituted for integral zero. That
substitution would need a separate injectivity theorem. Boundary-only
contacts are also excluded from the strict-interior argument.

## 4. The finite quotient counts are derived

Let `S` be a supplied finite packet set with `p in S -> swap(p) in S`.
The concrete edge type retains a source `p in S`, both valid digit
positions `i,j`, and membership of the resulting child in `S`. There is
one edge for every such positional pair, including repeated targets.

Swapping the source and exchanging `i,j` produces the edge with swapped
target. Applying the construction twice recovers the original identity.
This bijection carries outgoing edges at `p` to outgoing edges at
`swap(p)` and incoming edges at `p` to incoming edges at `swap(p)`.

The quotient label is precisely the represented orbit `{p,swap(p)}`.
It is not an arbitrary coarser map. An actual representative is chosen
only to define matrix entries; the edge bijection proves independence
of that choice.

Let `F_ij` count forward edges from a representative of orbit `i` into
orbit `j`, and let `T_ij` count incoming edges at a representative of
orbit `i` from orbit `j`. With the actual orbit cardinalities `m_i`,
the existing finite double-counting theorem now applies:

\[
m_i T_{ij}=m_j F_{ji}.
\]

A fixed orbit has size one; every other orbit has size two. If all
packets in `S` are nondiagonal, the fixed-packet theorem gives `m_i=2`
for every represented orbit, so

\[
T_{ij}=F_{ji}.
\]

For a mixed domain, retain the actual weights. Neither selecting one
representative nor naming an involution justifies discarding the fixed
orbits. Likewise, a manually supplied edge inventory needs its own swap
closure proof; vertex closure alone is insufficient.

This adapter authenticates exact finite combinatorics. A serialized
production graph must additionally be shown to enumerate this domain
and these occurrence identities before its matrix can inherit the result.

The assembled `ancestry_packet_transpose` theorem accepts a finite
swap-closed `S` contained in the actual inverse ancestry of interior
nondiagonal roots, with positive exact image scaling. It derives the
unweighted transpose directly. Containment supplies freeness; it does
not assert equality with the full ancestor set or inverse closure of `S`.

## 5. Relation to physical mass and the remaining geometry

The previous package proves that the complete represented interior
support of a supplied actual strict carrier retains every positive
forward child. Its forward matrix is conservative: `Fh=beta*h`.
The inverse ancestry domain of designated roots can be smaller and
can have positive forward exits. Inverse closure does not imply
forward closure, so the two statements are compatible.

For a chosen finite domain, the prior omitted-occurrence theorem
identifies its forward deficit with the mass of actual outgoing
occurrences omitted from the domain. The new count adapter supplies
the orbit-weight and transpose premises for those same retained edges.
Its `packet_quotient_deficit` theorem accepts an arbitrary quotient mass
function; applying it to physical mass additionally uses the previously
proved swap invariance and occurrence grouping.
This still does not prove that an inverse compact-overlap piece is empty,
that deleting an inverse edge is geometrically sound, or that any root
has positive compact overlap measure.

Before reusing a historical finite-graph certificate, reconcile its source
with current main and bind its serialized states and incoming rows to
these literal records and positional multiplicities. The next geometric
obligations are then concrete:

1. Identify each state with an actual compact inverse-overlap piece and
   prove the complete incoming-occurrence cover, including multiplicity.
2. Prove that every residue or stable-box exclusion used by a finite
   constructor removes only empty pieces, and prove completeness of its
   remaining domain.
3. Prove the required product-Haar scaling in the nonunit setting.
4. Connect a represented strict cut root to positive compact measure,
   then supply the required loss or another exclusion argument.

Positive physical interval length does not establish item 4. This package
does not discharge universal forced-crossing productivity, C4,
Concentration, global G1, or PSC. Coherent protected ancestry towers and
the construction of a common nonzero cut-derived row remain separate
routes.

## 6. Verification and replay

The [control inventory](c4-inverse-occurrence-controls-2026-11-10.md)
records exact finite domains and each deliberately weakened contract.
The dedicated C4 workflow runs the new native regression and a separate
artifact-producing Quint job. The complete Lean bank must be rebuilt and
audited at the published revision; development caches are not independent
acceptance evidence.

```sh
python tools/make_proof_bank.py --check
./tools/check_lean.sh
python tools/check_c4_inverse_occurrence_quint.py --output /tmp/c4-inverse-occurrence-quint
cd kernel
pixi run --locked mojo run -I . tests/test_c4_inverse_occurrence.mojo
```

The implementation PR records exact head, source tree, test counts,
hosted jobs and axiom-audit results after they are observed. Pending
jobs are not credited as passes. Independent human review remains
final validation debt, without blocking otherwise accepted research
progression.
