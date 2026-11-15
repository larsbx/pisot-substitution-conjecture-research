# C4 inverse occurrences and track-swap counts: literature stop/go

Date: 2026-11-10. Recorded before the new proof and control implementation.
Base: `main@209910264171fef550938dd566213c19734a75b6` (PR #536).

## Proposed claim and decision

**Proceed with a literal inverse-occurrence adapter and finite symmetry
counting.** The preceding [ordered-mass development](c4-overlap-mass-2026-11-10.md)
proves conservation on complete forward strict support. It does not identify
the different domain used by the historical inverse-prefix graph. The next
package should connect that inverse edge equation to the existing actual
digit relation and discharge the track-swap counting hypotheses from an
explicit symmetry of occurrence identities.

For a substitution `s`, write a current packet as `p=(a,b,z)` and an
inverse ancestor as `u=(A,B,z_new)`. An inverse occurrence consists of
actual marked decompositions

\[
s(A)=P\,a\,S,\qquad s(B)=Q\,b\,T,
\qquad Mz_{\rm new}=z+\pi(Q)-\pi(P).
\]

The marks include the literal prefixes and suffixes, hence their positions;
equal letters or equal resulting packets do not identify distinct marks.
Rearranging this integral equation gives precisely the existing forward
digit packet from `u` to `p`. This algebraic reversal needs no matrix
inverse, nonsingularity, positive length row, or Pisot hypothesis. Taking
`s` to be a specified iterate covers the corresponding multi-step image
words. The identity between that iterate's incidence and `M^q` must be
proved if a powered-matrix presentation is exported; it must not be
silently substituted for the actual iterate.

Under positive letter lengths, positive scale, and the exact equations
`physicalLength ell (s A)=beta*ell A`, prove that an interior current
packet has an interior inverse ancestor. Prove separately that every
interior forward child of an algebraically diagonal packet is diagonal.
Backward ancestry from nondiagonal interior roots then contains no
diagonal packet. Swapping the two actual incoming marks and negating the
integral residual gives an involutive edge bijection.

For a supplied finite swap-closed domain and a supplied finite occurrence
inventory closed under that bijection, derive constant outgoing and
incoming counts on each swap orbit. The existing
`OccurrenceMassCounts.weighted_count_transport` is then applicable. If
the domain has no diagonal packets, every orbit has exactly two ordered
states and its weighted correspondence simplifies to the unweighted
transpose. These are finite combinatorial conclusions, not a construction
of compact overlap pieces.

## Primary sources inspected

The following primary texts were opened and their stated sections inspected
for this gate, including the hypotheses of the cited theorem.

| Source and exact locator | Construction that transfers | Boundary retained |
|---|---|---|
| Akiyama--Lee, *Algorithm for determining pure pointedness of self-affine tilings*, [arXiv:1003.2898v1](https://arxiv.org/html/1003.2898v1), section 4, equations (4.1), (4.2), (4.4), Theorem 4.1 | Inflating a pair of tiles produces edges indexed by pairs of actual digits; repeated target states retain their edge multiplicities. Reversing the affine digit equation is the elementary interface needed here. | Theorem 4.1 assumes a self-affine tiling and a Meyer return set. A packet graph with the right equation does not supply those hypotheses. The paper distinguishes empty, boundary-only and genuine interior overlaps. |
| Martensen, *A Generalized Balanced Pair Algorithm*, [arXiv:math/0309194v1](https://arxiv.org/html/math/0309194v1), section 2 and Theorem 3.10 | Ordered word letters define intervals with disjoint interiors. The Perron left length row gives exact self-similar inflation, which supplies the scaling premise for the strip transfer. | Theorem 3.10 retains termination and coincidence productivity as separate assumptions. A positive length row alone is insufficient for exact scaling, and recurrence or a finite inverse domain supplies no productivity theorem. |
| Barge--Diamond, *Coincidence for substitutions of Pisot type*, [Bull. Soc. Math. France 130 (2002), 619--626](https://www.numdam.org/item/10.24033/bsmf.2433.pdf), pages 621--623, definitions of substitution on segments, prefix vectors, strands and configurations | Substitution sends a translated letter segment to the literal ordered prefix segments translated by the incidence action. This matches the mark-preserving affine equation. | The paper's configuration argument concerns actual strands under its Pisot assumptions. Neither a finite packet nor a swap orbit reconstructs that geometry or a common legal infinite ancestry. |

Affine reversal, disjoint interiors of a word partition, involutive
symmetry, and finite double counting are standard. The intended
contribution is their formal binding to the repository's actual marks,
integral sign convention and weighted-count consumer. No new general
overlap or pure-discreteness theorem is claimed.

## Exact hypotheses and derivation boundary

### Incoming marks and the direction of the equation

The inverse edge starts at the physical child `p` and ends at the larger
letter ancestor `u`; its forward digit step starts at `u` and ends at `p`.
In the repository's top-minus-bottom convention,

\[
z=M z_{\rm new}+\pi(P)-\pi(Q).
\]

The inverse graph's row direction must therefore be reversed when
comparing with the forward matrix. The signs and both mark identities
must be carried through a track swap. A proof that only target labels
match is insufficient to authenticate occurrence multiplicities.

The equation is a relation over integral vectors. It does not promise an
ancestor for every pair of incoming marks. Failure of exact lattice
membership gives no integral edge; rounding, division in floating point,
or reduction coordinatewise modulo a determinant cannot supply one.
Uniqueness of an integral solution needs injectivity of the incidence
action when that stronger claim is requested.

### Interior strip and diagonal ancestry

For positive lengths, packet interior is the already proved strip

\[
-\ell_a<\ell z<\ell_b.
\]

Every actual mark in `s(A)` satisfies
`0 <= length(P)` and `length(P)+ell_a <= beta*ell_A`, with the analogous
bottom inequalities. Combining them with the inverse equation and
dividing by positive `beta` yields the ancestor strip. Exact image
scaling is essential. The known `s=1/012/1` wrong row `(2,1,1)` remains
a negative control; the valid row is `(1,2,1)` with scale two.

For the diagonal lemma, `Diagonal` means equal letters and zero **integral**
residual. Its two forward image partitions are the very same word at
the same location. Positive overlap between two selected intervals forces
the same position, because distinct word positions have disjoint
interiors. Their letters and literal prefixes then agree, so the child
residual is zero. This argument needs positive letter lengths and actual
marks; it does not require Pisot, irreducibility, exact scaling, or
injectivity of the physical length map. Exact scaling and positive scale
are used in the separate inverse-interior transfer.

Likewise, a fixed integral packet under `(a,b,z) -> (b,a,-z)` is diagonal:
the equality gives `a=b` and `z=-z`, and integral vectors have no nonzero
element killed by two. This also needs no Perron independence. If a
different interface substitutes physical alignment `ell*z=0` for
integral zero, injectivity of the physical map on integral vectors is
an additional premise; it must be derived from the appropriate
irreducibility hypotheses or stated explicitly. The literal package
must not silently make that substitution.

### Finite quotient counts

An involution on ordered states and an involution on actual edge
identities must commute with source and target. The state domain and
edge inventory must both be invariant. Restricting only the vertex set
does not prove the required edge closure. Choosing one representative
per orbit does not prove count uniformity.

The edge involution gives bijections of outgoing and incoming fibers
when source representatives are swapped. Together with identity on an
unchanged representative, this proves both uniform-degree premises of
the existing counting theorem. For an actual orbit quotient, each fiber
contains exactly the state and its swap; absence of fixed states gives
cardinality two. A coarser label map can have larger fibers and must not
be called the orbit quotient without an exact fiber characterization.

The typed strip alone does not make the integral state space finite.
The finite counting adapter takes a supplied finite domain. A proof that
a geometric inverse construction has a complete finite domain still
needs its stable-space and compact-residue arguments.

## Existing results and prior failed shortcuts

The [side ledger](side-notes-ledger.md) and latest mass notes were read
before selecting this target. Reuse:

- `OccurrenceTransport.DigitStep.swap`, `Packet.Interior.swap`, and
  `Packet.interior_iff_bounds` for the existing orientation and geometry.
- `OccurrenceFinite.markEquiv` for actual mark/position identities.
- `OccurrenceSuccessor.offset_affine` for physical interpretation of the
  integral affine equation.
- `OccurrenceMassCounts` for weighted double counting and
  `PhysicalMass` for its matrix consumer.

The historical interfaces are source-scoped written arguments in
[inverse finite-carrier section 3](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/51dd090a6aefeb92210410a3f7e20d51926d7e86/docs/c4-finite-overlap-carrier-2026-11-05.md)
and [physical-mass orbit counts](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/51dd090a6aefeb92210410a3f7e20d51926d7e86/docs/c4-physical-overlap-mass-2026-11-07.md).
They motivate the interface but do not count as fresh Lean acceptance.

Backward ancestry of declared roots can have positive forward exits.
Its inverse closure does not imply forward closure. The complete strict
support proved conservative in #536 is a different domain. An omitted
forward interval can give arithmetic deficit; it does not by itself
establish emptiness of an inverse compact piece or authorize deleting an
inverse occurrence.

## Required controls and acceptance

Retain controls for inverse sign reversal, exchanging both unequal mark
indices under swap, repeated letters at distinct positions, positive
versus boundary-only overlap, wrong positive length scaling, and a
non-free mixed orbit inventory. A deliberately missing swapped edge must
fail the symmetry/count hypothesis. An inverse-closed finite example
with a positive forward exit should preserve the distinction from full
forward support. A literal diagonal root must exhibit the fixed orbit
excluded by the nondiagonal-root premise.

Use Lean for the universal algebra, strip, diagonal and finite-count
theorems; use the canonical Mojo occurrence machinery and bounded Quint
mutation controls for the executable interfaces. Publish exact source
and revision receipts, regenerate and audit the proof bank, and retain
the scope of each finite test. No broad census or new numerical cutoff
is needed to establish this adapter.

## Non-claims and next geometric obligations

This package does not authenticate the complete historical serialized
inverse graph, prove all its residue/stable-box exclusions, construct
compact overlap sets, prove product-Haar scaling, or derive positive
compact measure from a strict cut root. Positive physical interval
length is not positive compact overlap measure. It provides neither a
losing source nor a contradiction for every hypothetical strict carrier.
It does not promote C4, Concentration, global G1, or PSC. Independent
human review remains final validation debt rather than a research gate.
