# Universal closure review and the independent finiteness obligation

Date: November 14, 2026. Baseline: `32015cfb9d0914cedc9867f3290ea4bcdbbbb3b7`.
This note records a pre-code source review, an attempted closure composition,
and an exact negative control. It does not close a universal claim.

## Pre-code decision

**Proceed with a narrowed control and retain the two universal obligations.**
The proposed control is the literal binary substitution
`s(0)=00001`, `s(1)=011`. Prove that every noncoincident irreducible balanced
block has an immediate coincidence child and coincident blocks are productive
at depth zero, while the actual `ChildNC` closure of `01/10` is infinite.
This tests the necessity of the finiteness argument in
`FiniteProductivity.terminates_of_finite_reachable`. It is deliberately
outside the Pisot regime. No new census or alternative arithmetic kernel is
needed: reuse the existing exact `Intertwiner2.K2` and reduction theorems.

The decision and derivation in this file were recorded before writing the
new Lean control. Compilation results, if obtained, are to be recorded
separately; a source file is not a successful replay receipt.

### Primary-source check

1. Sirvent and Solomyak, *Pure Discrete Spectrum for One-dimensional
   Substitution Systems of Pisot Type*, Canadian Mathematical Bulletin 45
   (2002), 697–710, especially Section 5 and Theorem 5.6
   ([publisher PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/4BC0FD9DBA6ECA027A32568F9E5C1D12/S0008439500017537a.pdf/pure_discrete_spectrum_for_onedimensional_substitution_systems_of_pisot_type.pdf)).
   The bounded-gap mechanism relating the balanced-pair and overlap
   procedures is prior art. The repository's swap-seed adaptation is already
   in [the overlap-depth note](bpa-termination-by-overlap-depth-2026-10-02.md).
   An algorithmic relation does not supply bounded gaps unconditionally.
2. Barge, Štimac and Williams, *Pure Discrete Spectrum in Substitution Tiling
   Spaces*, Section 3, Theorem 3.2 and Corollary 2
   ([author PDF](https://web.math.pmf.unizg.hr/~sonja/PDSfinal.pdf)).
   The finite-factor and eventual-coincidence parts of termination must both
   be supplied. Its spectral conclusion cannot be used to prove those same
   hypotheses without an independent argument.
3. Minervino and Thuswaldner, *The Geometry of Non-unit Pisot
   Substitutions*, Annales de l'Institut Fourier 64 (2014), 1373–1417,
   Section 8.2 and Theorems 9.2 and 9.10
   ([publisher PDF](https://www.numdam.org/item/10.5802/aif.2884.pdf)).
   The internal space includes finite places. Multiple tiling is available;
   the stated degree-one tiling criterion additionally uses strong
   coincidence and geometric property (F). Neither may be discarded in a
   universal hitting argument.

The existing [strict-zipper source gate](p1b-strict-zipper-literature-gate-2026-09-21.md)
also records Akiyama–Lee's residual critical component and the limitations of
Perron growth. Its known productive affine-cycle controls are retained.
The current arXiv record for [Nakaishi 2401.07771](https://arxiv.org/abs/2401.07771)
still lists only the January 15, 2024 version. The repository's
[source-level stopping-time and transport audit](nakaishi-2024-first-entry-audit-2026-10-13.md)
therefore remains applicable; this review does not re-run or silently import
the already rejected mixing-to-cancellation step.

## The attempted universal composition

The attractive proposed chain is:

1. the seed-patch overlap graph is finite;
2. cell packing and cut counts give a positive overlap;
3. root nullity excludes a strict carrier;
4. the balanced-pair algorithm terminates with coincidence.

There are two independent missing transitions.

First, the implemented geometric endpoints
`NamedPositiveOverlap.carrierOverlap_measure_pos` and
`NamedStrictExclusion.no_strictSystem_of_roots_null` take `f : Fin 2`.
Their charts, Haar product, cut capture and root certificates belong to the
two literal named substitutions. Uniformity over their finite word carriers
is not uniformity over every primitive irreducible Pisot substitution.

Second, even if strict-system exclusion were supplied for a new substitution,
the finite object in step 1 consists of labelled tile overlaps with offsets.
The finite object required by step 4 consists of complete irreducible word
pairs and all of their actual children. A finite overlap type does not bound
the distance between consecutive common boundaries. That distance is the
length of a balanced-pair state.

The accepted generic theorem already states this exactly:

```text
noStrict + IsBlock T + finite actual ChildNC reachability
  => termination with coincidence from T.
```

Under `noStrict`, `FiniteProductivity.not_terminates_iff_infinite_reachable`
identifies the remaining alternative; it does not eliminate it. The
counterexample below shows that the generic missing premise is substantive.

## Exact control: coincidence without finite forward closure

Let `s(0)=00001` and `s(1)=011`. Its source-column incidence matrix is

\[
M=\begin{pmatrix}4&1\\1&2\end{pmatrix},\qquad
\chi_M(X)=X^2-6X+7.
\]

The matrix is positive and the characteristic polynomial is irreducible
over the rationals. Its eigenvalues are `3+sqrt(2)` and `3-sqrt(2)`.
Both exceed one. Consequently this control is primitive and irreducible
but **not Pisot**, and supplies no counterexample to PSC.

Both literal images start with `0`. Hence inflating any nonempty balanced
pair gives a first diagonal block `([0],[0])`. Every noncoincident
irreducible balanced block has this immediate `ChildNC` child; coincident
blocks are productive at depth zero. In particular no finite strict system
exists, by the existing `StrictSystem.not_productive` theorem (or by
`no_strictSystem_of_strongCoincidence`).

Write

\[
D(u,v)=\binom{u}{01}-\binom{v}{01},
\]

using the repository's scattered-subword count. For balanced pairs,
`Intertwiner2.k2_subst` and antisymmetry give

\[
D(s(u),s(v))=(4\cdot2-1\cdot1)D(u,v)=7D(u,v).
\]

`Intertwiner2.k2_join` makes `D` additive over the complete ordered balanced
reduction. Also `|s(u)| <= 5|u|` for every word.

Suppose the `ChildNC` reachable set `R` from `01/10` were finite. Every
member is a nonempty irreducible balanced block. The finite set of ratios
`|D(T)|/|T.1|` therefore has a maximum `r`, attained at a state `T`. Since
the seed has `D=1` and length two, `r >= 1/2 > 0`. In particular `T` is
noncoincident, so its **complete** child row lies in `R`. Counting every
occurrence, including repeated children, gives

\[
\begin{aligned}
7|D(T)|
 &=\left|\sum_{U\text{ in the child row of }T}D(U)\right|\\
 &\le\sum_U |D(U)|
 \le r\sum_U |U.1|
 =r|s(T.1)|
 \le5r|T.1|
 =5|D(T)|.
\end{aligned}
\]

This contradicts `|D(T)|>0`. Thus the actual seed closure is infinite
despite immediate productivity. No search cap, numerical root approximation,
or claim about an unobserved infinite execution is used.

The argument is an elementary specialization of the existing defect
intertwiner and growth bound. No novelty is claimed for that mechanism.
Its direction also explains its limit as a PSC attack: for a binary Pisot
matrix the degree-two multiplier is `|det M|=beta |alpha|<beta`, while the
Perron root is at most the maximum image length. The strict `7>5` growth
gap is therefore excluded by the Pisot hypothesis itself. On three letters
the corresponding exterior-square multipliers likewise stay below the
Perron scale. The control demonstrates a missing logical premise; it does
not furnish a new obstruction inside the PIP class.

## Why the accepted packing proof cannot supply the missing bound

`NamedCutCount.integerStarts_count_and_strip` proves

\[
X_n\le L\,\# Z_n,
\]

where `Z_n` consists of the actual common-cut integer starts. Its `L` bounds
the physical lengths of **all** reduction factors in the supplied finite
strict carrier. The cell-packing estimate then gives

\[
\frac{c}{L}X_n\le c\,\#Z_n\le(X_n+W_q)\mu(O).
\]

Choosing the neighborhood and cell depth first, then letting `X_n` diverge,
produces the positive lower bound `c/L`. Finiteness supplies a single `L`.
If only a level-dependent `L_n` is known, the coefficient `c/L_n` may tend
to zero. For example, `X_n=L_n=n+1` and `#Z_n=1` satisfy the lower count,
but `c <= (n+1) epsilon` eventually holds for every `epsilon>0`. This
cannot give positive measure to a limiting compact set. The issue is
uniform positive cut density, not a missing normalization of Haar measure.

The existing `NamedPositiveOverlapControls` separately guards bounded strip
growth, moving cell width, containment and open-set-to-compact-set transfer.
Those controls are not rerun as new research here.

## Remaining universal obligation at occurrence level

For a cyclic seed-reachable strict-zipper overlap `(i,j,w)`, BH asks for
some composable sequence of actual ordered child occurrences whose final
offset is zero. In the repository convention this means finding `m` and
literal image-prefix Parikh vectors `p,q` with

\[
M^m w=p-q,\qquad p\in P_m(i),\quad q\in P_m(j),
\]

with the associated occurrence chain realized. Periodic affine equations,
bounded stable projections, local digit admissibility, multiple tiling and
positive measure do not supply that pointwise assertion. A path with no hit
may still have an alternative productive branch; the established non-unit
affine-loop examples guard this distinction.

The existing overlap-depth theorem turns a bound on such actual hits into
a balanced-factor length bound `2 beta^D ell_max`. Using that result in the
reverse direction without proving the hit would assume BH. Separately,
one-sided residual A1′ concerns the remaining first-letter-fixed hub pair.
Neither universal premise is discharged by this review or by the accepted
parameter-family theorem. The standing universal target is ternary PIP,
with nonunits allowed; an all-alphabet PSC conclusion would require a
further dimension-general argument.

## Verification status

The control is implemented in
`proof/PscVerif/PscVerif/UniversalClosureReduction.lean`, under namespace
`Psc.UniversalClosureReduction`. Its principal endpoints are:

```text
all_blocks_productive : IsBlock T → Productive substitution T
infinite_seed_reachability :
  {U | ReflTransGen (ChildNC substitution) seed U}.Infinite
productive_but_not_terminating :
  (∀ U, IsBlock U → Productive substitution U) ∧
  ¬ TerminatesWithCoincidence substitution seed
```

The source also checks the literal incidence matrix, its exact rational
characteristic polynomial, and two distinct real roots exceeding one.
The displayed rational irreducibility argument is explanatory; no separate
irreducibility endpoint is claimed. The finite-carrier contradiction uses
the ordered reduction list throughout, retaining repeated child occurrences.

The final local replay used Lean `4.34.0-rc2`, `-j2`, and
`-DautoImplicit=false`, with outputs confined to a private overlay. Its
complete profiler log contains no error or warning and records successful
`.olean` serialization. The source and private source copy are byte-identical,
with SHA-256
`aaf84f504e5609b7d74be4187ec325e195e5facc098386b42e36b469f2318e24`.
The generated object has SHA-256
`e65194c5f9299cae462b25f01bdf708ed8d62473a47d91cf84bbbbc026bbadb1`.
The terminal process result was consumed across context compaction, so its
explicit exit integer is not retained in this local receipt. This development
replay is not source-isolated acceptance: the independent focused gate must
check the two literal endpoint types and all constants in this module before
promotion. Earlier unsuccessful development attempts receive no acceptance
credit.

The subsequent independent imported-object audit completed with exit zero
in 20.414 seconds. It accepted both literal endpoint types, checked module
ownership, and scanned all 35 owned constants, including 28 theorem constants
(generated declarations included), with only `propext`, `Classical.choice`,
and `Quot.sound` in their axiom closures. The integrated audit covered eight
modules, 618 constants, 547 theorem constants, eleven endpoints, and
22 rejected controls. Its receipt ties the control to the source and object
hashes above. This is a successful local imported-object audit; the fresh
source-isolated hosted compilation remains a separate acceptance step.

All governed C4, G1, BH, A1′ and PSC statuses remain unchanged. This control
closes the precise generic shortcut tested here; it leaves the missing
Pisot-specific bounded-gap and occurrence-hitting arguments explicit.
