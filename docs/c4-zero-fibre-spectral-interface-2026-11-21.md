# From the zero fibre to coincidence rank and invariant-measure spectrum

**22 November status.** The finite-automaton route supplies the zero-fibre
witnesses and equal-fibre proximality. Merged #650 proves the measured
real translation theorem for `k ≥ 2`. The recurrence proof in #652 gives
another construction of the zero-fibre witnesses. The interface analysis
below describes the historical stage after #643.
[Measured theorem](c4-family-measured-spectrum-2026-11-21.md) · [Convex-window proof](c4-zero-fibre-anchor-proof-2026-11-22.md)

This note audits the shortest remaining interfaces after PR #643 at
`7a5025ed7b8104413477ea7fbd15b52206e0959c`. It separates the new elementary
periodic expansion proof from the still missing witness-existence and
measure-theoretic implications. The pre-code source decision is
[zero-fibre witnesses](c4-zero-fibre-witness-stop-go-2026-11-21.md).

## Existing machine-checked endpoints

Write `S = geometry k hk`, where `hk : 1 <= k`, and let `g` be the
constructed full-history solenoid realization. The following declarations
are already in `Psc.ParameterFamilySolenoid` at the inspected PR head:

- `continuous_solenoidRealize`, `solenoidRealize_surjective`,
  `solenoidRealize_finite_fibres`;
- `solenoidRealize_translate` and `solenoidRealize_inflate`;
- `fixed_tiling_over_zero` and `periodic_of_realize_zero`;
- `denseRange_translate`;
- `solenoidRealize_fibres_eq_of_equivariant`;
- `common_tile_of_zero_fibre_witnesses`.

The last theorem takes the two zero-image equalities and three `Agree 1`
premises. It does not construct those agreements. Its downstream consumer
is `Psc.ParameterFamilyTiling.periodic_common_tile_of_origin_witnesses`,
which accepts three equalities of closed origin patches. The generic
proof lives in
`Psc.PeriodicPartnerLegalCoincidence.periodic_common_tile_of_origin_witnesses`.
Primitivity and the periodized swap certificate have already supplied the
legal-patch coincidence transfer. None of these endpoint statements has
coincidence rank or an invariant-measure `L2` conclusion.

## New formal increment: one periodic common tile supplies every radius

`PscVerif.PeriodicPartnerProximal` uses the existing legal hull and its
inflation. It defines the explicit geometric predicate

```text
ExactProximal S T U :=
  forall R > 0, exists t,
    Agree R (translate t T) (translate t U).
```

Its main theorem is
`Psc.PeriodicPartnerProximal.exactProximal_of_periodic_common_tile`.
The inputs are `1 < S.beta`, two positive inflation periods, and one
shared labelled tile. The periods need not agree. The output is the
predicate above. No solenoid, maximal-factor, Meyer, coincidence-rank or
measure assumption is added.

Here is its geometric proof. A tile `(a,x)` shared by `T` and `U` gives
exact agreement after the common shift `c = x + length(a)/2`, on the open
window of radius `r = length(a)/2`. Unique tile coverage proves that
agreement; it does not discard either side of an origin seam. At depth
`d`, the existing agreement expansion gives radius `beta^d r` and the
shift becomes `beta^d c`. Choose `d` to be a sufficiently large common
multiple of the two periods. Inflation then returns the original pair,
while `beta^d r` exceeds the requested radius.

Conversely, one positive exact common-translation window contains a tile
shared by the original pair. Consequently
`exactProximal_iff_common_tile_of_periodic` proves the equivalence of these
two geometric conditions for periodic tilings. This is an equivalence of
conditions, not a proof that every zero-fibre pair satisfies them.

`originPatch_eq_of_agree` also exposes the general positive-radius bridge
to the closed origin patch. Its conclusion includes both tiles when the
origin is a boundary. The proof is the generic form of the private bridge
in PR #643, with no three-letter restriction.

## What the published results supply

The references below have been inspected directly. They concern the
specified tiling systems and their specified maximal or geometric factors;
their conclusions do not apply to an arbitrary finite-to-one map.

### Strong regional proximality

Barge, Stimac and Williams, *Pure discrete spectrum in substitution tiling
spaces*, DCDS 33 (2013), 579--597,
[DOI](https://doi.org/10.3934/dcds.2013.33.579),
[author PDF](https://web.math.pmf.unizg.hr/~sonja/PDSfinal.pdf), Section 2,
Theorem 2.3 and Corollary 1, provide the finite-to-one maximal
equicontinuous factor and identify its fibre relation with strong
regional proximality. Their global hypotheses are primitivity,
aperiodicity and finite local complexity. Their Definition 2.2 of
`(m,d)`-Pisot family type additionally requires a diagonalizable expansion
whose eigenvalues are algebraic conjugates of common degree `d` and common
multiplicity `m`, and form a Pisot family. For this one-dimensional family,
the expansion is scalar, with the established cubic Pisot number as its
only eigenvalue, so `m=1` and `d=3`. Strong regional proximality uses new
tilings `T',U'` matching `T,U` at the origin and matching each other after one common
translation, at every radius. It does not say that `T,U` themselves have
equal origin patches. The proof of Theorem 3.1 consumes only the closed
origin version before using the legal-patch transfer and periodicity.

The exactification underlying that corollary is Barge--Kellendonk's
Theorem 3.4 in the inspected author preprint: repetitive Meyer tilings
have the same regional and strong regional proximal relations. The
uniform discreteness of the relevant puncture differences removes the
residual small translation. This geometric argument is not replaced by
ordinary topological approximation alone.

### Coincidence rank and generic fibres

Barge and Kellendonk, *Proximality and pure point spectrum for tiling
dynamical systems*, Michigan Math. J. 62 (2013), 793--822,
[DOI](https://doi.org/10.1307/mmj/1387226166),
[inspected author preprint](https://arxiv.org/pdf/1108.4065), define
coincidence rank using maximal sets of pairwise nonproximal members of a
maximal-factor fibre. In the inspected preprint:

- Lemma 2.10 proves independence of the base point;
- Lemma 2.12 identifies rank one with proximality being the full
  maximal-factor fibre relation;
- Theorem 5.4 gives full Haar measure to fibre-distal points for primitive,
  aperiodic, FLC Meyer substitution tilings;
- Theorem 2.25 applies to a minimal system with an ergodic invariant Borel
  probability measure, finite minimal rank, and almost-everywhere fibre
  distality; under these hypotheses it equates minimal rank one with
  continuous eigenfunctions spanning `L2` and with closed proximality;
- Lemma 5.12 connects nonproximal same-fibre pairs to disjoint tiles in
  the substitution setting.

Baker, Barge and Kwapisz, *Geometric realization and coincidence for
reducible non-unimodular Pisot tiling spaces with an application to
beta-shifts*, Ann. Inst. Fourier 56 (2006), 2213--2248,
[DOI](https://doi.org/10.5802/aif.2238),
[published PDF](https://www.numdam.org/item/AIF_2006__56_7_2213_0.pdf),
Theorem 4.2 supplies uniformly finite fibres and almost-everywhere
coincidence-rank multiplicity for its geometric realization. Theorem 5.1
identifies eigenvalues and pulled-back eigenfunctions. Corollary 5.2
states the equivalence between rank one and pure discrete tiling-flow
spectrum. These are published mathematical inputs, not Lean declarations
in the inspected closure.

## The minimal next formal interfaces

### 1. Existence for every pair over zero

The missing geometric theorem still has to quantify over all `k >= 2`
and all `T,U` with `g(T)=g(U)=0`. One may prove either the original three
agreements or, after the new equivalences, an actual shared tile. A
single positive family example or a finite enumeration does not discharge
that quantifier. Merely assuming maximality or the witnesses in a new
structure does not discharge it either.

The published route goes through maximal-factor identification, ordinary
regional proximality, and Meyer exactification. A direct analysis of the
literal zero fibre may avoid parts of that route, but must actually
construct the required tilings and translation.

### 2. Propagation to coincidence rank one

Once every zero-fibre pair shares a tile, the new theorem and existing
zero-fibre periodicity give exact proximality for every such pair. There
are two useful ways to finish the topological rank step.

One route formalizes coincidence rank and its independence of the base
point. The zero fibre then has no pairwise nonproximal set of size two,
and its nonemptiness supplies rank exactly one. The correspondence
between the concrete map and the maximal factor must be included if the
definition is the published maximal-factor definition.

A smaller one-way route first proves all fibres of the concrete map are
proximal. Here is the mathematical argument, not yet a Lean theorem in
this increment. Suppose `T,U` lie in one fibre but their common translates
remain separated by some positive `delta` in an ordinary compatible
metric. Translate `T` toward a fixed zero-fibre tiling `V`, and use
compactness to obtain a corresponding limiting tiling `W` from `U`.
Continuity and equivariance give `g(W)=g(V)=0`. The separation by
`delta` persists under every common translate of the limit pair.
Zero-fibre periodicity and a common tile, however, give arbitrarily large
exact common-translation windows, contradicting that separation.

In fact this transport argument only needs one fixed zero-fibre anchor
`V` to be exactly proximal to every member of its fibre. It does not
require the pairwise zero-fibre statement as an initial hypothesis:
the first coordinate of any alleged nonproximal pair is translated
toward that chosen `V`. Thus the weakest useful geometric input for
this route is a common tile between `V` and each zero-fibre `U`.
The stronger all-pairs witness statement remains the requested target,
and the new family witness equivalence can compare it to this anchor
version without silently assuming proximality is transitive.

This argument needs the formal bridge from exact proximality to ordinary
topological proximality and the corresponding compactness/limit
infrastructure. The existing ordinary hull is compact and has the
correct small-translation window basis; this increment does not add its
compatible ordinary metric or a general proximality library. These are
formal infrastructure obligations, not additional mathematical
hypotheses on the family.

If all concrete fibres are proved proximal, maximality can instead be
deduced afterward: every equicontinuous factor identifies proximal
pairs, hence factors through this continuous onto compact-group map.
That avoids relying on a written target identification for this
direction. It must not be used circularly to obtain the missing
zero-fibre witnesses.

### 3. From rank one to almost-everywhere singleton fibres

Rank one does not assert that every exceptional fibre contains only one
tiling. In particular, the zero fibre may contain distinct proximal
tilings. Finite fibres alone also give no almost-everywhere injectivity.

The needed next conclusion is precisely

```text
for Haar-almost every z in the solenoid,
  exists exactly one T with g(T) = z.
```

One can obtain it by formalizing the relevant part of BBK's generic
multiplicity theorem, or by proving the substitution fibre-distality
result and using rank one. The latter needs only the implication from
almost-everywhere fibre distality plus proximal fibres to singleton
fibres; it does not require the converse spectral direction. This is a
substantive measure-theoretic substitution theorem. An abstract finite
proximal extension should not silently be assigned this property.

### 4. The invariant-measure `L2` endpoint

For a one-way pure-discrete conclusion, it suffices to construct the
ordinary hull's translation-invariant Borel probability measure `mu`,
show `g_* mu` is normalized Haar measure, and use almost-everywhere
singleton fibres to make pullback by `g` onto `L2`. Characters of the
compact abelian solenoid span its Haar `L2`; equivariance makes their
pullbacks translation eigenfunctions. Surjectivity of pullback therefore
gives density of their linear span in the actual hull's `L2` space.

Equivalently, once a measurable inverse exists on a full-Haar-measure
set, one can construct `mu` as its pushforward of Haar measure and prove
invariance from equivariance. The set of singleton fibres is invariant,
and its inverse is equivariant there. Moreover, any invariant probability
measure on the hull pushes forward to Haar measure: the target translation
orbit is dense, so an invariant probability measure on the target is
translation invariant under the whole compact group. Almost-everywhere
singleton fibres then force that hull measure to be precisely the same
pushforward by the inverse. Thus this route also proves uniqueness of the
invariant hull measure. It does not replace the intended invariant-measure
endpoint with an arbitrary choice of measure or introduce a separate
unique-ergodicity theorem as an unproved premise.

This direction does not require classifying every possible measurable
eigenfunction or proving the converse. It does require the Borel and
invariant-measure setup, the almost-everywhere inverse or equivalent
surjectivity theorem for pullback, and character-density/eigenfunction
lemmas. The inspected family closure currently provides no declaration
of the hull's invariant measure, its Koopman representation, or this
density conclusion. Matrix/Pisot spectral lemmas already named
`SpectralPisot` do not provide these dynamical assertions.

## Published-target correspondence that must remain explicit

BBK Section 3 states that its intrinsic return lattice `Sigma` equals
`Gamma` in the irreducible Pisot case. For the literal family this is the
written reason for using the full integer lattice in the existing target.
The comparison must additionally match two-sided histories to the
nonnegative desubstitution indexing, normalize the unstable direction by
the Perron length functional, and reconcile the sign for `T-t`.

There is a domain issue as well: BBK's footnote 5 on page 2218 explicitly
allows finitely many nonrecurrent translation orbits in its strand-space
presentation that need not belong to the usual hull. The proof of its
Theorem 5.1 uses the unique minimal subset. A formal comparison for the
repository must restrict to, or identify, the ordinary legal/minimal
hull with the published recurrent subsystem and carry its invariant
measure. An equality of ambient target types alone does not prove that
domain correspondence.

The already checked
`solenoidRealize_fibres_eq_of_equivariant` is useful after the published
map has been placed on this actual domain with the same normalized
target action. Its theorem type cannot supply that placement itself.

## Evidence and non-claims

The new generic module has compiled with Lean 4.34.0-rc2 against the
independently rebuilt exact PR #643 source closure. The separate receipt
records its source digest and compiler exit status. An axiom audit must
continue to distinguish standard Lean axioms from introduced hypotheses;
a theorem conditional on a witness retains that hypothesis even when
its axiom closure is standard.

No universal zero-fibre witness-existence theorem, coincidence-rank-one
theorem, almost-everywhere injectivity theorem or invariant-measure
spectral theorem is claimed by this module. The family retains its
separate written proof using the published balanced-pair criterion.
Universal BH, residual A1-prime and C4 are outside this increment.
