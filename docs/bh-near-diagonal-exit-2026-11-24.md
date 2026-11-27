# Uniform literal coincidence for two higher-determinant bands

**Formal continuation, 27 November:** the [complete three-band Lean assembly](bh-diagonal-closure-2026-11-27.md) now discharges the actual entry, diagonal classification, signed progress and termination obligations. The dated component scope below is retained as the record of the earlier contribution. The [spectral transfer](bh-three-band-spectral-transfer-2026-11-27.md) states the resulting family conclusion and its verification boundaries.

**Status.** Written all-source theorem. The separate Lean scope and
the executable acceptance are recorded below.
[Source review](bh-near-diagonal-stop-go-2026-11-24.md)

For \(r\ge12\) and \(r+1\le k\le r+2\), let
\[
  \sigma_{k,r}(0)=1,\qquad \sigma_{k,r}(1)=01^k2,\qquad
  \sigma_{k,r}(2)=0^r1.
\]
Every strict ordered packet with these types and an integral
three-coordinate displacement has a literal path to \(1/1\) at
full integral displacement zero. In particular this gives the BH hit
and the stronger labelled coincidence for each actual seed overlap.

## Arithmetic and the central region

Set
\[
 P(X)=X^3-kX^2-2X-r,\quad
 B=r/\beta,\quad A=\beta-k,\quad \theta=(k-1)/\beta,
\]
where \(\beta\) is the root in \((k,k+1)\). Such a root exists because
\(P(k)=-2k-r<0\) and \(P(k+1)=k^2-1-r>0\).
The cubic equation gives \(\beta A=2+B\) and hence
\[
 P(X)=(X-\beta)(X^2+A X+B).
\]
We have \(\beta>k\ge13\), \(4/5<B<1\), \(0<A<1/4\),
\(A+B>1\), \(A\le3(1-B)\), and \(B\le\theta<1\). For example
\(\beta<r+3\) gives \(B>4/5\),
\(\beta(A+B-1)=2-(k-r)+B-A>0\), and
\(\beta(1-B)\ge1\) gives the bound on \(A\).
The discriminant \(A^2-4B\) is negative. The two other roots are
complex with modulus \(\sqrt B<1\). The only real root is between
consecutive integers, so the monic cubic has no rational root.
The incidence matrix is primitive since its square has all entries
positive. It has determinant \(r\).

Use tile lengths \((1,\beta,1+B)\), which scale by \(\beta\) on the
literal images. For the top-minus-bottom prefix column
\((x,y,z)\in\mathbb Z^3\) the physical displacement is
\(D=x+\beta y+(1+B)z\). A central packet has types \(1/1\) and
\(|D|\le k-1\). Such a packet is strict.

For an integer \(t\), put \(e=t+A y+B z\).
To set the next second coordinate to \(t\), the two ordinals within
the runs of \(1\) must differ by
\(h=t-(x+k y+z)=e-D\). If \(|e|\le\theta\), then
\(|h|\le k-1+\theta<k\). Both ordinals can be taken in
\(\{0,\ldots,k-1\}\), using \(\max(h,0)\) and \(\max(-h,0)\).
Their original zero-based image positions are one larger. The child is
\[
  (1,1;\ y+r z,\ t,\ y).
\]
Its physical displacement equals \(\beta e\). It therefore stays
central and the chosen child is an actual strict overlap.

## A decreasing choice inside the region

Write \(Q(z,y)=Bz^2+Azy+y^2\) and \(w=Ay+Bz\). Negating both
coordinates and the chosen integer preserves the bounds and energy,
so consider \(w\ge0\).

If \(t\) lies between \(-w\) and \(0\), convexity in the second
argument gives
\[
 Q(y,t)\le\max\{Q(y,0),Q(y,-w)\}<Q(z,y)
 \quad\text{when }(z,y)\ne(0,0).
\]
Indeed \(Q(y,-w)=BQ(z,y)\), and
\[
 Q(z,y)-Q(y,0)=
 A(z+y/2)^2+(B-A)z^2+(1-B-A/4)y^2>0.
\]
Both coefficients after the square are positive. Try \(t=-\lfloor w\rfloor\).
If its residual exceeds \(\theta\), the next integer
\(t=-\lfloor w\rfloor-1\) has \(|e|<1-\theta\le1-B<\theta\).

For \(Q(z,y)>4\), this other choice also decreases energy. With
\(H=Ay+2Bz\), \(d=1-B\), and \(E=Q(z,y)\), one has
\[
 H^2\le4BE<(E-d)^2,\qquad
 Q(y,t)=BE-He+e^2\le BE+d(|H|+d)<E.
\]
The middle strict inequality follows from
\((E-d)^2-4BE=E(E-2(1+B))+d^2>0\).
For \(Q\le4\), the lower bound
\(Q\ge(z^2+y^2)/2\) reduces the check to \(|z|,|y|\le2\).
In fact the coefficient bound
\(Q\ge(B-A/2)(z^2+y^2)\) excludes the pairs with both absolute
values equal to 2. If \((|z|,|y|)=(1,2)\), then
\(Q\ge B+4-2A>4\). If \((|z|,|y|)=(2,1)\) with equal signs,
\(Q\ge4B+2A+1>4\). In the opposite-sign case the nonnegative
\(w=2B-A\) is between \(1\) and \(1+B\). For the axes the
possible \(w\) are \(0,A,2A,B,2B\), all with fractional part
at most \(B\). For \(|z|=|y|=1\), the possible nonnegative
\(w\) are \(B-A\) and \(A+B\). The latter is between \(1\) and
\(1+B\). In every remaining case truncation fits the window.
Lean checks all small integer pairs using these inequalities.

Each nonzero pair thus admits a literal central child with strictly
smaller energy. The lower bound \(Q\ge(z^2+y^2)/2\) makes each
integer sublevel finite. Consequently some descendant has \(z=y=0\).
Take \(t=0\) once more to erase the remaining first coordinate.
This gives the typed packet \((1,1;0,0,0)\) with both original tracks.

## Entry from every strict overlap

The general half-width lemma `OccurrenceWidth.reaches_half_mass`
applies since every length is at least one and \(\beta>3\). Follow
its actual child path to a packet of overlap width at least \(1/2\).
Inflate that packet three more times. In the rest of this section use
units in which a tile \(1\) has length one. The common subinterval of
the inflated domains has length at least \(\beta^2/2>12\), so choose
a window of length \(12\) strictly inside it.

In either word \(\sigma^3(a)=\sigma(\sigma(\sigma(a)))\), tile gaps
are maximal runs of symbols other than \(1\), including end runs.
Every such gap has one of the following forms.

- A gap containing the \(0^r\) from an image of \(2\) is that whole
  zero run with at most a preceding \(2\) from the end of an image
  of \(1\). Its length is at most \(B+(1+B)/\beta<5/4\).
- Any other gap is a singleton \(0\), a singleton \(2\), or the
  seam \(20\) of two images. Its length is at most
  \((2+B)/\beta=A<1/4\).

This list follows from the three literal images. Every image has a
\(1\), and only the image of \(1\) can end in a non-\(1\).
The second sort of gap includes end gaps. For the first sort, successive
\(2\) letters in the parent word \(\sigma^2(a)\) have at least \(k\)
parent letters \(1\) between them. Each \(2\) ends its particular
image of \(1\), following that image's \(k\) occurrences of \(1\).
In the third-level word those intervening \(k\) blocks have length
\(k\beta\). Even after including the last \(2\) of the last block
with the later gap, the spacing between the gap intervals exceeds
\(12\). Therefore each track contributes at most one long gap to the
window.

Remove those at most two closed gap intervals. The remaining at most
three open components have total length greater than \(12-2(5/4)\),
so one has length greater than \(3\). In that component every gap
is shorter than \(1/4\) on either track. Choose a point between one
and \(5/4\) units from its left end. If it belongs to a top tile \(1\),
that tile lies inside the component. Otherwise the next top tile \(1\)
starts less than \(1/4\) units later, so it also lies inside the
component. In both cases existence follows from the bound on each
gap and the available room at the right. The point may be chosen
away from the finitely many endpoints.

The midpoint of this top tile belongs to a closed bottom tile \(1\)
or lies in a short bottom gap. In the first case the two tiles
have overlap at least \(1/2\). In the second case the next bottom
tile \(1\) begins within \(1/4\) of the midpoint, so the overlap
exceeds \(1/4\). The two unit tiles consequently have offset of
absolute value at most \(3/4<\theta\).

These two marks lie at specific positions in the two third-level
images. At each previous depth take their actual ancestors in the
image partitions. A point in their common strict interior stays
strictly inside both ancestor intervals when scaled back. The two
ordered ancestry tracks thus give a composable literal path of three
edges, with the affine full-coordinate shift given by the original
prefix marks. This enters the central region proved above.

## Balanced-pair consequence and scope

The usual fixed-parameter Pisot enclosure is finite here. For a root
\(\tau\) of \(P\), use the linear functional
\(f_\tau(x,y,z)=x+\tau y+(1+r/\tau)z\).
It is a left eigenrow for the incidence matrix. For a nonreal root
\(\lambda\), the real map \(d\mapsto(f_\beta(d),f_\lambda(d))\)
is injective. Multiplying the three conjugate row values by their
roots evaluates the quadratic
\(yX^2+(x+z)X+rz\) on the three distinct roots, so a kernel vector
must be zero. The physical offset is bounded on strict packets.
The other row contracts with modulus \(\sqrt B\) under inflation,
and the forcing from a pair of proper image prefixes is bounded.
Choose the larger of the maximum seed value and the radius
\(F/(1-\sqrt B)\), with \(F\) bounding the forcing. This encloses
every strict literal child. A bounded set in these real coordinates
has only finitely many integral preimages.

The finite enclosure covers each seed and is closed under every
strict literal edge. The all-source labelled path therefore applies
to each member. The prior `terminates_of_closed_diagonal_cover`
contract yields actual balanced-pair termination with coincidence for
every irreducible balanced seed. In particular all swap seeds qualify.
For the tiling flow the spectral consequence follows using
[Barge, Štimac and Williams, Corollary 2](https://doi.org/10.3934/dcds.2013.33.579).
That last implication uses the published criterion.

Together with the earlier finite instances and the bivariate proof
for \(k\ge r+3\), the canonical \(01/10\) case is covered for
\(r\ge4\), \(k\ge r+1\). The remaining band of this family is
\(k=r\), \(r\ge12\). Its maximal literal run-index difference is
\(r-1\), so the window used in the descent is smaller than \(B\).
The other BH chambers and A1′ keep their existing scopes.

## Lean boundary and replay

`BHNearDiagonalDescent.choose_rounding` proves the strict quadratic
descent. `BHNearDiagonalLiteral.central_hits_zero` realizes it on the two
literal run positions at each step and proves termination on the integer
sublevel. The direct Lean compiler checked both modules using the pinned toolchain.

The remaining formal geometry is to produce two marks of type 1 in
the literal third-level images of any half-width packet, with common
physical width at least beta/4 in the original length units. The
written long-gap argument above proves this statement. The review
includes a draft of the corresponding ordered-mark assembly separately
from the checked patch. The finite Pisot enclosure and spectral
application are at their written scopes.

The native replay builds every literal child row of all three swap-seed
closures at \(r\in\{12,13,16,20\}\) and \(k-r\in\{1,2\}\). Every strict
vertex has a half-width descendant. Every half-width packet has the
required unit overlap in exactly three further steps. In the central
window the code uses the stated rounding rule and checks the selected
digit pair, all three coordinates and the energy decrease. It checks
the largest permitted run-index difference, rejects endpoint contact,
and rejects applying the two-band window at \(k=r\).

Run from the repository root with the pinned toolchains.

```sh
(cd proof/PscVerif && lake build PscVerif.BHNearDiagonalLiteral)
(cd proof/PscVerif && lake env lean BHNearDiagonalAudit.lean)
(cd kernel && pixi run --locked mojo run -I . tests/test_bh_near_diagonal_exit.mojo)
python3 tools/make_proof_bank.py --check
```

The exact replay completed on eight parameter pairs. It covers 73,552
packets, 436,695 ordered child occurrences and 9,304 central selections,
of which 508 used the alternate rounding. An exploratory determinant-28
stress run reached the memory limit. The general Lean build was also
killed during this replay. The focused core files had already compiled.
The new axiom audit and the ordered-entry draft await completed runs.
