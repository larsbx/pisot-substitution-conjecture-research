# C4 bounded compact-piece covers: literature stop/go

The initial stop/go and three-source review were recorded before new
theorem-facing implementation. Concrete countermodel details and semantic
audit clarifications below were appended during development without
expanding that approved scope. Base:
`main@67921a747a16b6998156f807f7f391ecfa3fcd88`, including #537 and the
subsequent integration of #497. The append-only side ledger and
[`OccurrencePiece`](../proof/PscVerif/PscVerif/OccurrencePiece.lean) were
read first. No governed claim is promoted.

## Proposed claim and decision

**Proceed with a bounded occurrence-indexed cover and conditional sound
pruning.** The all-integral-ancestor union is already proved by
`OccurrencePiece.overlap_eq_iUnion_inverse`. Re-proving that identity would
not advance the current boundary. The new target is its restriction to a
supplied finite inventory, composition through a prescribed finite depth,
and explicit sufficient conditions for the constructor's exclusions.

Retain the complete actual marks, both positions, and intermediate packet
identities along each history. Ordered histories may avoid normalization
entirely; if a stored edge uses track-swap normalization, its adjusted
translation must be retained. Equal end packets or equal affine images do
not identify different histories. Set
coverage and occurrence counts are different outputs: a set union forgets
multiplicity, while an occurrence inventory must preserve it.

Do not claim that a fixed finite packet domain represents every genuine
compact piece. First prove the exact premise needed to restrict the existing
union, then expose the remaining compact-space instance and geometric
exclusion obligations. The bounded construction is useful even when those
obligations are unavailable.

## Three primary sources inspected

These papers were opened and the named passages inspected for this gate.
Their constructions are prior art; the proposed contribution is the
repository-specific formal binding and independently replayable scope.

| Primary source | Inspected result and use | Hypotheses that do not transfer automatically |
| --- | --- | --- |
| Akiyama--Lee, *Algorithm for determining pure pointedness of self-affine tilings*, [arXiv:1003.2898v1](https://arxiv.org/html/1003.2898v1), Section 4, equations (4.1)--(4.4), Theorem 4.1 | Paired-digit intersections give graph-directed overlap pieces. Edges retain multiplicities, and paths compose their translations. Potential, boundary-only, and actual interior overlaps are distinguished. | The spectral criterion assumes a self-affine tiling and a Meyer return set. A finite occurrence graph does not supply either premise or justify deleting a geometric piece. |
| Minervino--Thuswaldner, *The Geometry of Non-unit Pisot Substitutions*, [arXiv:1402.2002](https://arxiv.org/pdf/1402.2002), Lemma 3.1, Proposition 8.1, Theorem 8.3 | The representation space includes finite completions. The prefix-indexed compact tile equation, its within-letter measure-disjointness, and product-Haar scaling are established in that space. | Identification with the repository's compact matrix-adic factor is a separate construction. Neither finite residue arithmetic nor a projected interval proves that identification, the tile equation in that model, or positive overlap measure. |
| Thuswaldner, *Unimodular Pisot substitutions and their associated tiles*, [JTNB 18 (2006), 487--536](https://www.numdam.org/item/JTNB_2006__18_2_487_0.pdf), Lemma 3.4 and Definition 3.6, pp. 507--509 | Effective graph finiteness uses both a bounded expanding coordinate and contraction of the other coordinates. Contact edges preserve prefix/suffix labels and canonical orientation. | The result is in a unimodular contact-graph setting. Its finiteness theorem cannot replace the separate nonunit residue and compact-interpretation obligations here. |

## Existing formal boundary

Write `p=(a,b,z)` and `E(p)=K_a intersect (K_b+star(z))`. The current module
derives

\[
E(p)=\bigcup_u\ \bigcup_{e:\operatorname{InverseOccurrence}(s,p,u)}
\left(AE(u)+\star\pi(P_e)\right)
\]

from the original tile equation, injectivity of the ambient action,
commutation with incidence, and `ReflectsIntegralRange`. No topology or
measure occurs in that proof. The current normalized-slot theorem also
changes the translation to `star(z+pi(Q))` when the raw target is swapped.
That correction must survive every bounded composition.

For a supplied finite domain, an exact internal occurrence inventory is
already available through `OccurrenceGraphBinding.Row.Exact`. Internal
completeness covers all edges with represented endpoints; it says nothing
about unrepresented nonempty geometric pieces.

## Strongest justified finite-cover contract

For each source packet let `R_p` be the union of the retained occurrence
pieces. Each retained piece is a subset of `E(p)` by the existing theorem.
Consequently the exact criterion for `R_p=E(p)` is that every omitted
occurrence piece is contained in `R_p`. This criterion permits redundant
nonempty pieces and is therefore weaker than emptiness of every omission.

A convenient, locally checkable sufficient condition is:

\[
\forall u,e,\quad e\text{ is omitted}\Longrightarrow
AE(u)+\star\pi(P_e)=\varnothing.
\]

An omitted inverse piece is empty exactly when its ancestor overlap is
empty: this image-emptiness equivalence needs no injectivity. Keep this
sufficient condition explicit rather
than silently identifying it with the logically weakest cover premise.
Even if an omitted nonempty piece is redundant as a set, its occurrence
cannot be deleted from a multiplicity count or a measure sum without a
separate argument.

Once the same one-step cover holds at every intermediate packet, induction
gives a cover by length-`n` histories. The zero-depth cover is the original
overlap. Every history records all its edge choices; it is not an endpoint
set. A finite supplied packet domain and finite mark positions give a
finite internal history type. Alternatively, for nonsingular incidence,
each pair of incoming marks has at most one integral ancestor, so the
unpruned depth-`n` tree is finite without a global state bound. If `D` bounds
the total incoming mark count, `(D^2)^n` bounds its history count. Singular
incidence does not supply this uniqueness and must not inherit that bound.

Compactness is a separate conditional consequence: in an appropriate
Hausdorff topological additive group, compact tiles and continuous affine
maps give compact overlap and finite-history pieces. The algebraic set
identity itself authenticates neither the chosen compact tiles nor their
relationship to actual infinite substitution prefixes.

## Which exclusions can be justified

| Constructor decision | Sound conclusion available | Required input still visible |
| --- | --- | --- |
| Selected letters, positions, or literal prefixes disagree | This is not the claimed actual incoming occurrence. | Complete comparison with the literal source words, not a matching endpoint count. |
| Exact equation `M y=z+pi(Q)-pi(P)` has no integral solution | No integral occurrence record exists. Its paired geometric piece is empty **if** integral-range reflection holds. | A proved compact-space residue interface; arithmetic nonintegrality alone is insufficient. |
| Stable projection lies outside a difference enclosure | The ancestor overlap is empty if each entire tile projects inside its certified enclosure. | Containment of the actual compact tiles and correct projection/translation action. Samples and numerical extrema do not prove containment. |
| Integral offset lies outside a proved finite carrier | Empty overlap for the specified ancestry, using the stable enclosure, preserved physical strip, and an authenticated invertible chart. | Correct ancestry, exact positive length scaling, enclosure, inverse-chart bounds, and integer rounding. A strip test alone is not general compact emptiness. |
| Boundary contact or undecided interval sign | No emptiness conclusion. Retain the candidate. | A measure-zero result would still differ from set emptiness. |
| State/depth/coordinate resource budget exhausted | An incomplete finite result with an explicit frontier. | Exhaustion cannot remove a piece or certify full coverage. |
| Duplicate target or duplicate affine image | Retain each distinct literal occurrence/history. | Set redundancy does not justify changing adjacency multiplicities. |

One useful intermediate refinement of `ReflectsIntegralRange` is a finite
residue certificate. Suppose a homomorphism `rho` from the ambient space to
`Z^3/M Z^3` annihilates `A(G)` and sends `star(z)` to the class of `z`.
Then an ambient equation `A(x)=star(z)` forces that class to vanish, hence
`z` lies in `M Z^3`. This derives range reflection from a concrete quotient
compatibility law. Constructing the compact matrix-adic space and its
projection remains separate. In the unrestricted completion fields,
multiplication is surjective and this reflection generally fails.

## Mandatory countercontrols

1. Preserve the actual `00/11/22` two-state domain
   `{(0,1,0),(1,0,0)}`. Its inverse closure follows from the parity equation,
   yet the forward `(1,1)` occurrence exits with positive physical mass.
   It therefore rejects inverse-closure-to-forward-completeness and
   physical-deficit-to-compact-loss shortcuts. It is reducible and
   nonprimitive, so it is not a counterexample in the standing PIP class.
2. Preserve two different positional histories with the same endpoint.
   Deleting one may leave a set union unchanged while corrupting counts.
   Check actual marks and affine composition as well as the endpoint.
3. Omit a genuinely contributing set piece in a finite exact set model.
   An internally complete retained graph alone must not certify the cover.
   Separately include redundant nonempty pieces to refute the unnecessary
   claim that full set coverage forces every omitted piece to be empty.
4. Use closed enclosures with boundary contact. A displacement at a
   difference-box endpoint may give a singleton intersection, so replacing
   strict separation by a non-strict rejection is unsound for set covers.
5. Retain a nonintegral candidate with an ambient preimage in a space where
   range reflection fails. This distinguishes exact integer solving from
   geometric exclusion, and avoids claiming that rational division proves
   nonunit compact emptiness.
6. Retain wrong positive length scaling, undersized enclosure, missing
   occurrence, and exhausted-budget controls. None may be recorded as a
   geometric acceptance.

### Exact finite compact countermodels

The following models isolate missing hypotheses of the abstract interfaces.
They are not PIP substitutions and are not asserted to be actual compact
prefix tiles of the research class. Their finite sets nevertheless are
compact in the discrete topology, so compactness alone cannot repair the
failed implications.

**Missing range reflection can destroy the entire inverse union.** Let
`G=Z/3Z`, let `star(z)` be the coordinate sum modulo three, put `A(x)=2x`,
and take `s=00/11/22`, so `M=2I`. Let every `K_c=G`. Multiplication by two
is injective on `G`, the commutation law holds, and the literal tile
equations hold because every affine image of `G` is `G`. For
`p=(0,1,e_2)` its overlap and all four paired occurrence pieces equal `G`.
But each integral inverse equation is

\[
2y=e_2+j e_1-i e_0,\qquad i,j\in\{0,1\},
\]

whose third coordinate is odd. There is no integral inverse occurrence at
all, so the all-integral-ancestor union is empty. Range reflection is the
failed premise: every element of `G` has an `A`-preimage, whereas, for
example, `e_0` has no integral preimage under `2I`. This example retains
actual literal marks and demonstrates more than a failure of a numerical
solver.

**Physical exteriority is not compact emptiness.** Keep the same `G`,
`star`, and tiles, but take `s=0/1/2` and `A=id`. The incidence is `I`, so
integral-range reflection holds with preimage `y=z`; the tile equations,
injectivity, and commutation also hold. With unit physical lengths,
`p=(0,1,2e_0)` is outside the strict physical strip, while `E(p)=G`.
There is no contradiction with the inverse-ancestry strip theorem: this
packet is not in the zero-offset-root ancestry of the identity
substitution. The physical invariant needs that ancestry premise when
used in a carrier bound.

**A false enclosure makes a true separation test unsound.** In the same
identity model, take the proposed enclosure `B_c={0}` and
`p=(0,1,e_0)`. Then `star(e_0)=1` lies outside `B_0-B_1={0}`, yet
`E(p)=G`. The omitted hypothesis is precisely `K_c subset B_c`; it is false
because `K_c=G`. An exact finite difference test cannot authenticate its
own enclosure.

**Internal occurrence completeness need not give geometric coverage.**
Use `s=1/2/0`, `A=id`, coordinate-sum `star`, and `K_c=G`. The incidence
is a permutation matrix of determinant one, so integral-range reflection
holds. The tile equation and commutation also hold. Represent
`S={(0,1,0),(1,0,0)}`. At `p=(0,1,0)`, the sole literal inverse ancestor
is `(2,0,0)`, which is outside `S`. The retained incoming inventory is
internally complete and empty, but `E(p)=G`. This isolates the missing
finite-domain representability hypothesis while keeping all the current
abstract geometric hypotheses.

**A nonempty omitted actual occurrence can be redundant.** Take
`s=01/1/2`, `A=id`, `star=0`, and `K_c=G`. This incidence has determinant
one, so range reflection holds even though `star` is zero. The original
tile equations hold. At `p=(0,1,0)` the two actual incoming ancestors are
`p` and `(0,0,(1,-1,0))`. Both affine pieces equal `G`. Restricting to
`S={p}` keeps the complete set cover but removes one actual occurrence.
This refutes the unnecessary implication from set coverage to emptiness of
every omitted piece and independently confirms the distinction between
set coverage and occurrence multiplicity.

## Minimal remaining geometric task

For a particular finite constructor, the missing local geometric statement
is that each omitted occurrence piece is empty (sufficient for the
occurrence-preserving cover), or, for set equality alone, that it is already
covered by retained pieces. Establish this for the *actual* compact prefix
tiles by discharging the compact matrix-adic instance, the original tile
equation, and every used exclusion. Finite row agreement supplies none of
those discharges by itself.

For the historical twelve-source constructor, an equivalent convenient
occurrence-level target is: **at every represented source, every nonempty
paired piece has an exact integral ancestor whose canonical representative
is in the recorded domain, with the same two marks and the correct
normalization translation.** Nonsingularity gives uniqueness of the
integral solution. The existing internal-row certificate then retains that
occurrence. Prove this target by the compact residue criterion, actual
stable enclosure, and ancestry-based carrier bound; do not replace it by
closure under the constructor's already filtered rows or small observed
coordinates. Genuine closure under **all actual integral inverse
occurrences** is a sufficient alternative after the tile/range hypotheses
are supplied: there are then no omitted integral pieces. The mandatory
forward-leaking example refutes forward completeness, not this conditional
incoming-cover implication. The local representability statement above is
what permits sound geometric pruning when genuine algebraic inverse
closure is unavailable.

After a set cover is established, an equality recurrence for compact
overlap measure still needs measurable pieces, the correct nonunit
product-Haar scaling, and measure-disjointness of distinct incoming
occurrence pieces. Positive physical interval length is not a substitute
for positive compact overlap measure at a strict cut root. C4, global G1,
Concentration, and PSC remain open.

## Implementation and acceptance scope

Use Lean for finite restriction, typed history composition, and sound
exclusion implications where the necessary structures exist. Use canonical
Mojo with exact checked arithmetic and a separately written integer/set
oracle for finite inventories and countercontrols. Record the source
substitution, actual iterate, exact depth, budgets, positional record
schema, and any unresolved frontier. Regenerate the proof bank and obtain
the applicable canonical Lean/axiom and native receipts. No pending or
reduced-import development check is a complete production acceptance.
