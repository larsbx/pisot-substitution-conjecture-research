# Spectral transfer for the three bands and the complete higher-determinant domain

**Status, 27 November 2026:** complete written spectral transfer, dependent on
the published criteria identified below. The arithmetic for the full domain, three-band
all-source literal exits, finite all-child carriers and full-factor BPA
termination are checked in Lean. The tiling-space construction and
application of the external spectral theorems are written mathematics. The older finite parameter certificates retain their
executable scope; they have not been imported into Lean. Independent human
review is pending.

For
\[
 \sigma_{k,r}(0)=1,\qquad
 \sigma_{k,r}(1)=0\,1^k2,\qquad
 \sigma_{k,r}(2)=0^r1,
\]
the new input covers every integral strict packet when
\(r\ge12\) and \(r\le k\le r+2\). This note supplies the remaining
mathematical bridge to pure discrete spectrum of the **tiling
\(\mathbb R\)-action**. Combining this input with the previously recorded
finite and bivariate certificates gives the following domain statement.

**Theorem, with the evidence scopes in Section 7.** For every pair of integers
\(r\ge4\), \(k\ge r\), the balanced-pair algorithm on the literal seed
\(01/10\) for \(\sigma_{k,r}\) terminates with coincidence. With the positive
Perron tile lengths, its substitution tiling flow has pure discrete spectrum.
On the three bands \(r\ge12,\ r\le k\le r+2\), the argument also gives
termination with coincidence for every fixed irreducible balanced seed.

The latter stronger conclusion is confined to the new all-source region.
The older bivariate certificate is a canonical-seed result. This note makes
no first-proof or general Pisot substitution conjecture claim.

## 1. Targeted primary-source stop/go

This review continues the
[actual-arithmetic source decision](bh-diagonal-arithmetic-stop-go-2026-11-27.md)
and the
[residual-exit source decision](bh-diagonal-residual-stop-go-2026-11-27.md).
The exact question is whether the now checked literal paths discharge an
existing spectral criterion, including its finite-factor or finite-overlap
hypotheses. Five primary sources were inspected.

| Primary source | Exact result used or tested | Decision for this family |
| --- | --- | --- |
| Barge, Štimac and Williams, [*Pure discrete spectrum in substitution tiling spaces*](https://web.math.pmf.unizg.hr/~sonja/PDSfinal.pdf), Section 2, Section 3 and Corollary 2; [published version](https://doi.org/10.3934/dcds.2013.33.579) | Their balanced-pair termination definition requires a finite set of all irreducible factors of all iterates and productivity of every such factor. For a Pisot substitution with irreducible incidence characteristic polynomial, termination for one distinct-letter swap implies pure discrete tiling spectrum. Their standing assumptions include aperiodicity and FLC. | Apply after the finite-carrier construction and the literal full-factor bridge in Sections 3–5. Use the corrected published criterion, not the earlier argument that the authors identify as having a gap. |
| Akiyama and Lee, [*Algorithm for determining pure pointedness of self-affine tilings*](https://arxiv.org/pdf/1003.2898), Definition 2.4, Theorems 2.5 and 2.7, Lemma 3.2; [published version](https://doi.org/10.1016/j.aim.2010.07.019) | Overlap coincidence requires one common finite depth. For self-affine tilings with Meyer return set it is equivalent to pure point spectrum. A scalar Pisot expansion meets their Meyer criterion; a Meyer control-point set gives finitely many overlap classes. | A second route is valid in the new all-source region after the actual integral representation and padding argument in Section 6. |
| Lee and Solomyak, [*Pisot family self-affine tilings, discrete spectrum, and the Meyer property*](https://arxiv.org/pdf/1002.0039), Corollary 2.13; [published version](https://doi.org/10.3934/dcds.2012.32.935) | For a diagonalizable expansion whose eigenvalues are conjugate with equal multiplicities, its spectrum being a Pisot family is equivalent to the control-point set being Meyer. | The expansion here is the one-dimensional scalar \(\beta\). This supplies Meyer before any pure-discreteness conclusion; no converse from pure point spectrum is used. |
| Barge, [*The Pisot Conjecture for \(\beta\)-substitutions*](https://arxiv.org/pdf/1505.04408), Theorem 15 | The tiling systems of Pisot \(\beta\)-substitutions have pure discrete spectrum. | Relevant prior art, but matching the expansion number or characteristic polynomial does not identify the present literal substitution with that numeration system. Section 8 records the remaining distinction. |
| Barge, [*Pure discrete spectrum for a class of one-dimensional substitution tiling systems*](https://doi.org/10.3934/dcds.2016.36.1159), main criterion | A primitive, nonperiodic Pisot substitution that is injective on initial letters and constant on final letters has pure discrete tiling spectrum. | These endpoint-map hypotheses fail for the present words and their positive powers. They do not directly replace the new exit argument. |

**Decision: proceed with the written transfer.** The missing finite-carrier
premise has an elementary contracting-conjugate construction, already
outlined in the
[near-diagonal note](bh-near-diagonal-exit-2026-11-24.md).
It is completed below and linked to the existing checked full-factor
implication. The alternative overlap route also closes, with Meyer and
finite-type uniformization explicitly retained. Neither route needs a
unimodular hypothesis or an unproved finiteness property of a Rauzy
representation.

## 2. Actual arithmetic on the full stated domain

The three-band specialization is in
[BHDiagonalPisot.lean](../proof/PscVerif/PscVerif/BHDiagonalPisot.lean) and
[BHNearDiagonalPisot.lean](../proof/PscVerif/PscVerif/BHNearDiagonalPisot.lean).
The wider endpoint
`BHHigherDeterminantPisot.primitive_irreducible_pisot` in
[BHHigherDeterminantPisot.lean](../proof/PscVerif/PscVerif/BHHigherDeterminantPisot.lean)
now checks the arithmetic throughout \(r\ge4,\ k\ge r\), including root
existence and the positive literal eigenlength row. The following derivation
explains that formal proof, so the older parameter regions inherit no unstated
arithmetic assumption.

Counting the actual images, with source letters indexing columns, gives
\[
 M=\begin{pmatrix}0&1&r\\1&k&1\\0&1&0\end{pmatrix},
 \qquad
 M^2=\begin{pmatrix}1&k+r&1\\k&k^2+2&k+r\\1&k&1\end{pmatrix}.
\]
Thus \(M^2\) is strictly positive, \(\det M=r\), and
\[
 P(X)=\det(XI-M)=X^3-kX^2-2X-r.
\]
We have \(P(k)=-2k-r<0\) and
\[
 P(k+1)=k^2-r-1\ge k^2-k-1>0.
\]
The intermediate value theorem supplies a root
\(k<\beta<k+1\). Set \(A=\beta-k\), \(B=r/\beta\).
Then \(0<A\), \(0<B<1\), \(\beta A=2+B\), and
\[
 P(X)=(X-\beta)(X^2+AX+B).
\]
The discriminant of the remaining quadratic is negative, since
\[
 A^2=\frac{(2+B)^2}{\beta^2}<\frac9{\beta^2}
       <\frac{4r}{\beta}=4B.
\]
The second strict inequality follows from
\(4r\beta>4\cdot4\cdot4=64>9\).
Its roots \(\lambda,\overline\lambda\) are nonreal and satisfy
\[
 |\lambda|^2=B<1.
\]
Consequently \(\beta\) is the unique real root. A rational root of this monic
integer cubic would be an integer, while \(\beta\in(k,k+1)\) is not an
integer. A cubic over \(\mathbb Q\) without a rational root is irreducible.
It follows that \(\beta\) is a degree-three Pisot number and is irrational.

The positive row
\[
 \ell=(1,\beta,1+B)
\]
satisfies \(\ell M=\beta\ell\): the three image lengths are respectively
\(\beta\), \(2+k\beta+B=\beta^2\), and \(r+\beta=\beta(1+B)\).
Since \(M\) is primitive and \(\ell\) is positive, this is its Perron
eigenvalue and its positive geometric length row. Multiplying by \(\beta\)
gives the division-free row \((\beta,\beta^2,\beta+r)\) used by the finite
certificate encoding.

The root in the all-source endpoint and the root in the arithmetic endpoint
are the same: both are roots in the bracket \((k,k+1)\), and the factorization
above proves uniqueness. Thus changing between those endpoints introduces
no second choice of geometry.

## 3. The tiling hypotheses, including aperiodicity

Give a tile of type \(a\) the interval length \(\ell_a\). The original words
subdivide each inflated interval exactly because of the length identity.
All images are nonempty.

A legal fixed tiling can be constructed directly. In the image of a type
\(1\) tile, the first type \(1\) occurrence has prefix length \(1\) and has
nonempty suffix. Put the original tile on
\([a,a+\beta]\), with \(a=-1/(\beta-1)\). The chosen child begins at
\(\beta a+1=a\), so the original tile is a tile of its own image.
Moreover \(a<0<a+\beta\). The nested patches
\(\Phi^n([a,a+\beta],1)\) have supports
\([\beta^n a,\beta^n(a+\beta)]\), which exhaust \(\mathbb R\).
Their union is a fixed tiling \(T\), and every finite patch is legal.

Primitivity supplies repetitivity. A legal word occurs in some
\(\sigma^m(c)\). Every \(\sigma^2(b)\) contains \(c\), so every
\(\sigma^{m+2}(b)\) contains that word. The lengths of these finitely many
supertiles have a finite maximum. In any sufficiently long legal word,
decomposition inside a higher iterate contains a whole such supertile;
at most two partial supertiles meet its ends. Thus the original word
occurs with a uniform gap bound. This also proves minimality of the legal
symbolic hull, without an aperiodicity assumption.

Finite local complexity is immediate for these interval tiles. In a bounded
interval there are only boundedly many consecutive tiles, because the
minimum tile length is \(1\). There are finitely many words of a bounded
length and finitely many subpatches of each word, up to translation.

For aperiodicity, suppose the legal symbolic hull had a periodic point.
Minimality would make the hull its finite shift orbit. Let \(q\) be the
normalized letter-count column in one period; it is a positive rational
column with \(\mathbf1^{\mathsf T}q=1\). Substitution maps that periodic
point to another legal point, whose normalized frequency column is
\[
 \frac{Mq}{\mathbf1^{\mathsf T}Mq}.
\]
All points of the finite shift orbit have the same column \(q\), so
\(Mq=cq\), with the positive rational number
\(c=\mathbf1^{\mathsf T}Mq\). Multiplying by \(\ell\) gives
\(\beta\,\ell q=c\,\ell q\); positivity gives \(c=\beta\), contradicting
irrationality. A translation period of a labelled interval tiling would
induce a nonzero index period of its ordered tile-type word. Hence every
tiling in the associated hull is aperiodic.

The substitution is therefore primitive and aperiodic, the fixed tiling is
repetitive and FLC, and its hull is the usual substitution tiling space with
its translation-invariant probability measure. These are the standing
geometric hypotheses of the criteria reviewed in Section 1.

## 4. A finite carrier from the actual Pisot embedding

Fix \(r,k\) in the new all-source region, and fix one irreducible balanced
word pair \(U/V\). A packet consists of two ordered tile types and a full
integer displacement \(d=(x,y,z)\). Its physical top-minus-bottom
displacement is
\[
 f_\beta(d)=x+\beta y+(1+r/\beta)z.
\]
The packet is strict precisely when
\[
 -\ell_{\rm top}<f_\beta(d)<\ell_{\rm bottom}.
 \tag{1}
\]
In particular \(|f_\beta(d)|<\beta\), since \(\beta>4\) and \(1+B<2\).

### 4.1 Conjugate rows and bounded forcing

For each root \(\tau\) of \(P\), put
\[
 f_\tau(d)=x+\tau y+(1+r/\tau)z.
\]
All roots are nonzero. The identity
\(1+r/\tau=\tau^2-k\tau-1\) gives the equivalent polynomial expression
\[
 f_\tau(d)=(x-z)+(y-kz)\tau+z\tau^2.
 \tag{2}
\]
Direct multiplication gives \(f_\tau(Md)=\tau f_\tau(d)\).
For one actual pair of image occurrences, let \(u\) be the top proper-prefix
Parikh column minus the bottom proper-prefix Parikh column. The child has
the exact full-coordinate displacement
\[
 d'=Md+u,\qquad
 f_\lambda(d')=\lambda f_\lambda(d)+f_\lambda(u).
 \tag{3}
\]
The collection \(\mathcal D\) of all such differences is finite: there are
three finite literal images and finitely many pairs of their marked
occurrences. Let
\[
 F=\max_{u\in\mathcal D}|f_\lambda(u)|,\qquad c=|\lambda|<1.
\]
Let \(\mathcal S\) be the finite set of strict packets formed by the actual
marks of \(U/V\), aligned at their common left endpoint. Choose
\[
 R=\max\left(\{0,F/(1-c)\}\cup
                  \{|f_\lambda(d_p)|:p\in\mathcal S\}\right).
 \tag{4}
\]
Then \(cR+F\le R\). Thus every literal child of a packet whose conjugate
coordinate has modulus at most \(R\) also has conjugate modulus at most
\(R\). No arbitrary choice of a rounded or relabelled child is made here:
(3) applies to every pair of original image occurrences.

### 4.2 Finiteness and closure

Consider the real-linear map
\[
 E:\mathbb R^3\longrightarrow\mathbb R\times\mathbb C,\qquad
 d\longmapsto(f_\beta(d),f_\lambda(d)).
\]
It is injective. If \(E(d)=0\), then reality of \(d\) gives
\(f_{\overline\lambda}(d)=0\) as well. By (2), the real polynomial
\((x-z)+(y-kz)X+zX^2\), of degree at most two, vanishes at the three
distinct roots \(\beta,\lambda,\overline\lambda\). It must be zero, whence
\(z=y=x=0\). Domain and target both have real dimension three, so \(E\)
is an isomorphism of finite-dimensional real vector spaces. The inverse
image of
\([-\beta,\beta]\times\{w:|w|\le R\}\) is bounded. A bounded subset of
\(\mathbb R^3\) contains only finitely many points of \(\mathbb Z^3\).

Define \(\mathcal C\) to contain exactly all typed integral packets satisfying
(1) and \(|f_\lambda(d)|\le R\). There are only nine ordered type pairs, so
\(\mathcal C\) is finite. It covers all strict seed marks by (4).
If \(p\in\mathcal C\) and \(p\to q\) is any actual `InteriorStep`, the
definition of that edge supplies strictness of \(q\), and (3) supplies its
conjugate bound. Consequently \(q\in\mathcal C\).

This is the required finite carrier, closed under **every** literal strict
child. It is not a finite-state assertion deduced from pointwise
termination. Its construction uses the contracting conjugates and the
integral lattice before applying the exit theorem.

## 5. From the carrier to all actual factors and spectrum

The checked endpoint
`BHDiagonalAllSources.three_band_all_source_exit` in
[BHDiagonalAllSources.lean](../proof/PscVerif/PscVerif/BHDiagonalAllSources.lean)
says that, for the constructed \(\beta\), every full strict integer packet
has a finite path of `InteriorStep` edges to a packet \(q\) with
\[
 q_{\rm top}=q_{\rm bottom},\qquad q_\delta=0.
 \tag{5}
\]
It has no seed-realizability or finite-carrier premise. Apply it to every
member of \(\mathcal C\). Closure ensures that the entire chosen path stays
in \(\mathcal C\), although the path theorem itself did not need that fact.

The exact checked bridge is
`BHBoundedFactors.terminates_of_closed_diagonal_cover` in
[BHBoundedFactors.lean](../proof/PscVerif/PscVerif/BHBoundedFactors.lean).
Every argument of that theorem has now been supplied:

| Bridge argument | Present construction |
| --- | --- |
| Literal substitution and positive lengths | Original words \(\sigma_{k,r}\) and \(\ell=(1,\beta,1+B)\) |
| Positive scale and exact image-length scaling | \(\beta>k\ge12\) and \(\ell M=\beta\ell\) |
| Irreducible balanced seed | The fixed \(U/V\); in particular \(01/10\) |
| Finite packet set covering all seed overlaps | \(\mathcal C\) from Section 4 |
| Closure under all strict literal children | Equations (1)–(4), with original prefix differences |
| Labelled diagonal reachability for every member | The all-source theorem, with both equal types and full integer zero |

The bridge concludes `StrictSystem.TerminatesWithCoincidence` for the actual
seed. Its finiteness part is about actual irreducible factors of iterates,
via the full-factor correspondence in
[TerminationFactors.lean](../proof/PscVerif/PscVerif/TerminationFactors.lean).
For productivity, the bridge places the first marks of each actual
irreducible factor back in its whole iterate. Deleting the preceding
balanced factors preserves the full packet. The actual occurrence path
lifts inside the factor and reaches the singleton coincidence provided by
(5). Thus both clauses of the published BPA definition are obtained.

For the canonical seed, \(0\ne1\) and \(01/10\) is an irreducible balanced
pair: neither proper one-letter prefix has the same Parikh vector.
Section 2 supplies the primitive Pisot substitution and irreducible
incidence characteristic polynomial; Section 3 supplies the tiling
hypotheses. Barge–Štimac–Williams, Corollary 2, now gives pure discrete
spectrum of the \(\mathbb R\)-action.

The finite-carrier instantiation is now checked in
[BHPisotFiniteBPA.lean](../proof/PscVerif/PscVerif/BHPisotFiniteBPA.lean). It
uses the existing proper contraction theorem and a finite union of complete
strict-packet forward orbits, an equivalent finite-carrier construction to
Section 4. The family endpoint
[BHThreeBandBPA.all_blocks_full_factor_coincidence](../proof/PscVerif/PscVerif/BHThreeBandBPA.lean)
proves the full-iterate definition for every irreducible balanced seed with
only the natural parameter bounds. The external tiling spectral theorem
is applied in written mathematics; it is not represented by a Lean axiom
or a new dynamical Lean theorem.

## 6. Independent overlap-coincidence transfer on the three bands

The new all-source region also admits a direct geometric transfer. This
section records the actual overlap representation and the uniform depth
that would be missed by a bare pointwise-exit assertion.

### 6.1 Every actual overlap has a full integral packet

Use the fixed legal tiling \(T\) from Section 3 and its left endpoints.
The difference of any two endpoints is the positive or negative length of
the finite intervening word, hence lies in \(f_\beta(\mathbb Z^3)\).
Every return vector \(v\), being the difference between two endpoints of
tiles of the same type, also lies in that group.

For an Akiyama–Lee overlap \((u,v,w)\), the top tile at \(u\) is translated
by \(-v\) and compared with the bottom tile at \(w\). Its relative start
displacement \(u-v-w\) is therefore \(f_\beta(d)\) for some
\(d\in\mathbb Z^3\). The two given types and this \(d\) form a strict packet
exactly by (1). In fact \(d\) is unique: (2) and the degree-three
irreducibility show that \(f_\beta(d)=0\) for integral \(d\) only when
\(d=0\).

Inflation sends this displacement to
\(\beta(u-v-w)\). Selecting literal top and bottom image occurrences adds
their actual prefix-length difference, which is precisely the image of
\(Md+u_{\rm prefix}\) in (3). Every selected strict child of the packet is
therefore an actual child overlap of those original tiles. As \(T\) is
fixed by substitution, these children stay in \(T\). The return translation
also stays valid: if \(v\) joins two tiles of one type, choosing the same
image occurrence in both shows that \(\beta v\) is again a return vector.
This inductively realizes the full path, not only its endpoint label.
Condition (5) makes the terminal tiles of the same type at exactly the
same position, which is a geometric coincidence.

### 6.2 Meyer, finite types and a common depth

The expansion of \(T\) is the one-dimensional linear map
\(Q:x\mapsto\beta x\). It is diagonalizable, its single eigenvalue has
multiplicity one, and \(\{\beta\}\) is a Pisot family by Section 2.
Akiyama–Lee Theorem 2.7 supplies the Meyer return set \(\Xi(T)\).
Lee–Solomyak Corollary 2.13 supplies a Meyer control-point set.
After translating each prototile to its control point, Akiyama–Lee
Lemma 3.2 supplies finitely many potential-overlap classes, hence finitely
many actual overlap classes. The change from control-point coordinates
to left endpoints adds only a fixed type-dependent offset; it preserves
the finiteness of the actual classes.

Choose one representative of each actual overlap class. Section 6.1 and
the all-source theorem give a coincidence depth \(n_i\) for representative
\(i\). Equivalent overlaps have the same ordered types and relative
displacement, so the identical image-position choices work for them.
There are finitely many representatives; let
\[
 N=\max\bigl(\{1\}\cup\{n_i\}\bigr).
\]
If a chosen path reaches coincidence early, choose the same position in
the two identical nonempty image words at each further step. Equal types
and full zero are preserved. This pads the path to length exactly \(N\).
Every actual overlap consequently has a coincidence in its \(N\)-fold
inflation, as required by the common-depth definition. Akiyama–Lee
Theorem 2.5 gives pure point dynamical spectrum, the same conclusion as
the tiling pure discrete spectrum in Section 5.

Meyer is established from the expansion arithmetic before the spectral
conclusion. The finite set used here is the set of actual overlap types;
it is distinct from the seed-specific finite carrier of Section 4.
Neither construction asserts one finite state set or one depth bound
uniform in the unbounded parameters \(r,k\).

## 7. Combining the parameter regions without enlarging their evidence

The integer domain \(r\ge4,\ k\ge r\) is the disjoint union of the following
three regions.

| Parameters | Available coincidence/termination input | Verification scope used here |
| --- | --- | --- |
| \(r\ge12,\ r\le k\le r+2\) | Every strict full integral typed packet has an actual path to equal-letter full zero; Section 4 then gives a finite carrier for each irreducible balanced seed. | Uniform literal theorem, actual PIP arithmetic, finite carrier and full-factor BPA termination in Lean; the spectral transfer is written. |
| \(4\le r\le11,\ r\le k\le r+2\) | Complete finite carriers for all three unordered swap seeds, with every ordered strict child and labelled-zero rank verified. | The 24 exact Mojo certificates recorded in the [higher-determinant carrier note](bh-higher-determinant-carrier-2026-11-24.md). Those finite graphs have not been imported into Lean; their application uses the same proved carrier contract. |
| \(r\ge4,\ k\ge r+3\) | Canonical \(01/10\) seed factors have track length at most \((r+2)(k+4)\); the family newborn exclusion gives productivity in this finite actual factor set. | The exact bivariate word certificate and written proof in the [two-parameter carrier note](c4-two-parameter-carrier-2026-11-14.md), using the [bilateral newborn exclusion](c4-bilateral-newborn-family-2026-11-14.md). |

For the finite region, the recorded verifier checks complete ordered child
rows, including children of coincidences, together with actual shortest
ranks to labelled zero. Its signed field encoding is decoded into the
full integer coordinates before comparison with the packet contract.
The cited replay covers all 24 integer parameter pairs, not a sample of
an infinite region. This note does not rerun those large certificates or
change their evidence level.

For the bivariate region, the finite partition certificate bounds all
irreducible factors because irreducible factorization refines every
balanced partition. Productivity follows by considering any nonproductive
factors: they would form a nonempty finite fully strict child-closed
system, which the separate family theorem excludes. The resulting full
BPA termination is exactly the hypothesis needed for the same distinct
letters \(0,1\). No all-source path theorem is inferred for that region.

Thus every parameter pair in the stated domain has canonical-seed
termination, and Section 2 gives the Lean-checked arithmetic over that entire domain.
The Barge–Štimac–Williams application completes the domain theorem at the
mixed scopes shown in the table.

## 8. Prior-art assessment and boundaries

The expansion number belongs to a familiar numeration family. Its greedy
expansion of \(1\) is the three digits \(k,2,r\): after the first digit the
remainder is \(A\), then \(\beta A=2+B\) with \(0<B<1\), and
\(\beta B=r\) gives zero remainder. Barge's theorem for Pisot
\(\beta\)-substitutions therefore supplies pure discreteness for the
corresponding numeration substitution. It does not, by itself, identify
that tiling hull with the hull of the particular words
\((1,01^k2,0^r1)\). No literal conjugacy, return-word identification or
other spectrum-preserving equivalence to that substitution is supplied
by the present review.

The initial-letter map of the present words is
\[
 0\mapsto1,\quad1\mapsto0,\quad2\mapsto0,
\]
so it and all its positive powers are noninjective. The terminal-letter
map is
\[
 0\mapsto1,\quad1\mapsto2,\quad2\mapsto1.
\]
It permutes \(1,2\) in a two-cycle, so no positive power is constant.
The direct initial/final-letter criterion reviewed in Section 1 is
therefore unavailable, including after taking powers or simply reversing
all words.

The targeted source and exact-family searches did not identify a published
theorem already stated for this entire literal two-parameter family.
That limited search does not establish novelty. The appropriate claim
here is a repository family-closure milestone with inspectable links to
published transfer theorems.

The determinant is \(r\ge4\). Both transfers above work for these nonunit
substitutions: the finite enclosure uses forward integral updates, and
the spectral criteria used here do not assume determinant \(\pm1\).
No integral inverse of \(M\), unit-only torus realization, or Euclidean-only
nonunit Rauzy representation is used.

The result concerns the geometric tiling flow with Perron lengths. A
claim about the constant-roof symbolic \(\mathbb Z\)-action would require
its own transfer statement and is not made here. The three-band
all-source theorem, the family-domain conclusion, and the corresponding
strong-coincidence results remain family-specific. Universal BH, the
other C4 chambers, residual A1-prime and universal PSC are outside this
note.

## 9. Formalization boundary

The checked chain now includes `BHDiagonalAllSources`, actual arithmetic
over the whole `r>=4,k>=r` domain in `BHHigherDeterminantPisot`, the generic
finite-carrier implication in `BHPisotFiniteBPA`, and parameter-only
full-factor termination in `BHThreeBandBPA`. The contraction core was
extracted unchanged into `GeometricFPisotCore`, with its original public
names re-exported by the legacy module. The following steps have complete
written arguments above but have not been assembled as an end-to-end Lean
spectral theorem:

- Constructing the legal tiling hull and its actual overlap encoding.
- Importing or formalizing the external Meyer and spectral theorems.
- Importing the 24 finite graphs and the older bivariate executable
  certificate into the Lean kernel.

These are formalization boundaries, not added hypotheses in the written
derivation. No new computation or test in this note substitutes for the
unbounded proof, and no external spectral theorem has been added as a
Lean axiom.
