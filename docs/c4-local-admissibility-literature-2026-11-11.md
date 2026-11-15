# C4 local incoming admissibility: literature stop/go

This gate was recorded before the new theorem-facing implementation and
tests. Base: merged `main@222ce957cf5ffc85cf482937b735b27e22f46379` (#539).
`AGENTS.md`, the side-notes ledger, the existing occurrence-piece and
bounded-cover interfaces, and the
[previous compact-cover gate](c4-compact-cover-literature-2026-11-11.md)
were inspected first. No governed C4 claim is promoted.

## Decision and scope

**Proceed with a source-local admissibility interface and an unconditional
union over all selected paired marks.** Replace a global sufficient
condition only where the proof needs a local one. Do not assert that the
new local condition holds for authentic compact Pisot tiles without a
separate geometric construction.

The bounded targets are:

1. From the literal tile equation, prove the full finite paired-mark union,
   including pairs whose inverse equation has no integral solution.
2. Under an injective ambient action and incidence commutation, derive an
   integral incoming cover from local admissibility of nonempty paired
   pieces. Keep the integer-lifting premise visible.
3. State an exact retained-set cover criterion using **all** raw paired
   pieces. This criterion must not require global range reflection or
   discard nonintegral pairs before testing coverage.
4. Give a sufficient represented-pair condition for a supplied finite
   domain and iterate it only where it holds at every intermediate source.
   Preserve complete occurrence addresses and their multiplicities.
5. Prove conditional exclusion using authenticated projected tile profiles.
   A finite profile computation does not establish its own tile enclosure.

These are set-theoretic and arithmetic interfaces. They neither construct
the authentic compact tiles nor prove product-Haar scaling, a measure
recurrence, positive compact overlap, global graph finiteness, or PSC.

## Three primary sources inspected

The passages below were opened and inspected for this gate. Their
graph-directed constructions are prior art. The new work is the precise
formal distinction between raw pairs, integral occurrence records,
represented records, and the hypotheses for passing between them.

| Primary source | Inspected passage and use | Hypothesis boundary |
| --- | --- | --- |
| Akiyama--Lee, *Algorithm for determining pure pointedness of self-affine tilings*, [arXiv:1003.2898v1](https://arxiv.org/html/1003.2898v1), Section 4, equations (4.1)--(4.4), Theorem 4.1 | Intersecting the two tile unions produces the paired-piece union. The graph counts full paired-digit choices with multiplicity and distinguishes potential, boundary, and actual overlaps. | The spectral statement assumes a self-affine tiling and a Meyer return set. Neither follows from a finite abstract paired-piece identity. |
| Minervino--Thuswaldner, *The Geometry of Non-unit Pisot Substitutions*, [arXiv:1402.2002](https://arxiv.org/pdf/1402.2002), Section 3, Lemma 3.1, Proposition 8.1, Theorem 8.3 | The nonunit representation uses full completion fields; actual compact tile coordinates satisfy bounded valuation restrictions. The paper proves its prefix tile equation, measure-disjointness, and product-Haar scaling in that representation. | A full field factor is not its valuation ring or a finite residue quotient. Identifying the repository carrier, star map, admissible translations, and compact tiles requires a separate proof. |
| Thuswaldner, *Unimodular Pisot substitutions and their associated tiles*, [JTNB 18 (2006), 487--536](https://www.numdam.org/item/JTNB_2006__18_2_487_0.pdf), Lemma 3.4 and Definition 3.6, pp. 507--509 | Contact-graph finiteness is derived using bounded expanding coordinates and contraction in the other coordinates. Edges retain both literal decompositions and an orientation. | The theorem is unimodular and uses geometric bounds. Local incoming admissibility cannot replace those premises or establish a globally finite nonunit graph. |

## The unconditional finite union

Use the repository sign convention. For a packet `p=(i,j,z)`, write

\[
E(p)=K_i\cap(K_j+\star z).
\]

A selected pair consists of complete actual marked decompositions
`s(a)=P i S` and `s(b)=Q j T`, including their positions. Define

\[
C(p;P,Q)=
 (A K_a+\star\pi(P))\cap
 (A K_b+\star(z+\pi(Q))).
\]

The literal tile equation alone gives

\[
E(p)=\bigcup_{\text{all selected pairs }(P,Q)} C(p;P,Q).
\]

This is distributivity of intersection over the two incoming tile unions.
It requires no integral inverse solution, global range reflection,
injectivity of `A`, incidence commutation, topology, or measure. There are
`d_i*d_j` selected pairs, where `d_c` counts all literal incoming occurrences
of `c` across the substitution words. In particular the count is at most
`D^2` if `D` is the total number of literal marks. This bound does not
require injective incidence.

Equal sets do not identify two selected pairs. The finite pair type must
retain the ancestor letters and both literal marks. Its cardinality and
the union it indexes answer different questions.

## Local lifting and represented covers

The exact inverse equation for a selected pair is

\[
M y=z+\pi(Q)-\pi(P).
\]

Define local admissibility at `p` to mean that **every nonempty selected
paired piece** has an integral solution to this equation. Equivalently,
every selected pair with no integral solution has empty paired piece.
Neither formulation needs injectivity of `M`.

When `A` is injective and `A(star(y))=star(M y)`, an integral solution gives
the existing actual inverse-occurrence record with ancestor `u=(a,b,y)`,
and

\[
C(p;P,Q)=A E(u)+\star\pi(P).
\]

Consequently local admissibility and the literal tile equation suffice for
the all-integral incoming cover at this source. No injectivity of integral
incidence is needed for this set identity. Incidence injectivity is needed
to infer uniqueness of the ancestor displacement from the pair, and hence
to bound the full integral incoming record type by the number of pairs.

For a supplied finite domain `S`, a convenient sufficient condition is:
every nonempty selected pair at `p` has **some** integral solution whose
ancestor packet belongs to `S`. Call this the represented-pair condition.
It is stronger than bare set coverage. If it holds at every source in
`S`, the represented one-step covers iterate to a cover at every prescribed
finite depth. Every history retains its intermediate packet and both marks
at each step. A finite domain and finite literal marks make this retained
history type finite even when the unrestricted integral incoming type is
not finite.

Local admissibility at the initial source alone does not license the same
claim at depth two. The local premise must hold at the intermediate
sources, or follow from a proved invariant on the reached sources.

### Where incidence injectivity is essential

Under the action assumptions above, local admissibility together with
representation of **every** nonempty actual inverse ancestor implies the
represented-pair condition. This implication needs no injectivity of `M`.

The reverse implication does need integral-incidence injectivity if it is
to conclude representation of every nonempty inverse ancestor: a witness
that one lift lies in `S` need not represent another lift of the same pair.
Do not present these two contracts as equivalent without that premise.
The singular countercontrol below isolates this point.

## Exact retained-set criterion without range reflection

Let `R_S(p)` be the union of affine pieces indexed by retained actual
inverse occurrences with ancestor in `S`. Each retained piece lies in
`E(p)` under the literal tile equation and the existing action hypotheses.
The unconditional raw union therefore gives the exact criterion

\[
E(p)=R_S(p)
\quad\Longleftrightarrow\quad
\forall\text{ selected pairs }(P,Q),\;
C(p;P,Q)\subseteq R_S(p).
\]

This criterion includes nonintegral pairs. It assumes neither global range
reflection nor local admissibility. A nonempty nonintegral piece can be
redundant in the retained set union; local admissibility is sufficient for
an integral occurrence cover but is not necessary for equality of sets.

Checking only omitted **integral** occurrences is insufficient before an
integral incoming cover is proved. That check can be vacuous when there
are no integral incoming occurrences although `E(p)` is nonempty. The
`e_2` countercontrol below reproduces exactly this failure.

Set redundancy cannot justify changing occurrence counts or summands in a
measure argument. Even when a retained union is the whole overlap, a
faithful inventory of literal paired contributions must still identify
which selected pairs were excluded and why.

## Full-field range and local residue exclusions

The following is an elementary deduction from the formal definitions,
not a further theorem attributed to the cited papers. Multiplication by a
nonzero algebraic scalar is surjective on a product of full completion
fields: divide in each field. Contraction does not change that fact.

If the abstract ambient action `A` is surjective and
`ReflectsIntegralRange` holds, then the integral incidence action is
surjective. For each `z`, choose `x` with `A x=star(z)` and apply reflection
to obtain `y` with `M y=z`. Conversely, surjectivity of integral incidence
implies reflection directly. Thus a nonsingular integer matrix with
`abs(det M)>1` cannot satisfy global range reflection in a model with a
surjective ambient action. No injectivity of `star` is needed for this
obstruction.

This diagnoses why global reflection is too strong for the unrestricted
nonunit field product. It does **not** establish local admissibility.
Actual compact supports, lattice translations, and residue compatibility
must still exclude the offending selected pairs. The valuation support
information in the nonunit source suggests a place to seek such input;
it is not an identification of the repository's compact/residue factor.

A conditional projected-profile lemma is approved within this gate. Let
`rho : G -> R` be additive, let `A_R` act additively on `R`, and assume

\[
\rho(Ax)=A_R(\rho x),\qquad \rho(K_a)\subseteq B_a.
\]

Then the image under `rho` of an actual paired piece is contained in

\[
(A_R B_a+\rho(\star\pi(P)))\cap
(A_R B_b+\rho(\star(z+\pi(Q)))).
\]

An empty projected intersection proves that the original paired piece is
empty. No injectivity of `rho`, `A_R`, or `M` is needed for this exclusion.
Providing such a certificate for every selected nonintegral pair proves
local admissibility. A nonempty projected intersection proves no actual
intersection. The enclosure `rho(K_a) subset B_a` and the commuting action
are geometric premises, even when `R` is a finite residue group and the
projected test is exact. Boundary contact and inconclusive profiles must
be retained.

There is a further distinction for a **finite** residue target. A product
of characteristic-zero fields is divisible as an additive group. Any
additive homomorphism from that entire group to a finite group is zero:
if `n` annihilates the target, write `x=n*y` and obtain
`rho(x)=n*rho(y)=0`. Thus a nontrivial reduction modulo a residue ideal
cannot be a global finite-valued additive map on the unrestricted field
product. This is another elementary algebraic deduction, not an assertion
that the abstract profile lemma fails.

Useful residue information can instead come from a projection to a full
local field followed by certified containment in valuation-module cosets,
or from reduction on an authenticated common support module containing
the relevant translated pieces and preserved by the action. The module,
its quotient, and that containment must be constructed and proved. The
abstract finite-group controls below do not provide this construction.

## Required abstract countercontrols

The models below isolate logical implications. They are not PIP
substitutions or authenticated compact prefix tiles of the research
class. The cyclic-group models have finite discrete compact carriers; the
singular model can use the same carrier. Thus adding compactness alone
does not remove the failures.

### Global reflection can fail while the local represented cover holds

Take `s=00/1/2`, `M=diag(2,1,1)`, `G=Z/3Z`, `A=id`,
`star(z)=z_1+z_2 mod 3`, and `K_a=G` for every letter. The literal tile
equations and action commutation hold. Global reflection fails at `e_0`:
`star(e_0)=0` has an ambient preimage but `M y=e_0` has no integral
solution.

For the domain `{(1,2,0),(2,1,0)}`, each source has a unique selected
incoming pair. Both prefixes are empty, the only integral ancestor is the
source itself, and its nonempty affine piece is `G`. Thus local
admissibility and the represented-pair condition both hold. This is a
strict weakening of the global sufficient hypothesis.

### Local admissibility is not necessary for set coverage

Take `s=00/11/22`, `M=2I`, `G=Z/3Z`, `A(x)=2x`,
`star(z)=z_0+z_1+z_2 mod 3`, and all `K_a=G`. At `p=(0,1,0)`, the four
selected pairs have positions `i,j in {0,1}` and inverse equations

\[
2y=j e_1-i e_0.
\]

All four paired pieces equal `G`. Only `(i,j)=(0,0)` is integral. Hence
local admissibility fails on three nonempty selected pairs, while the
single integral retained piece for ancestor `p` already covers `E(p)=G`.
This accepts the exact set criterion and rejects necessity of local
admissibility. It does not make the four literal pair addresses identical.

### Dropping nonintegral pairs can destroy coverage

Keep the same model and change the source to `p=(0,1,e_2)`. The four
inverse equations are

\[
2y=e_2+j e_1-i e_0.
\]

Every right-hand side has odd third coordinate. There is no integral
inverse occurrence, while all four raw paired pieces and `E(p)` equal
`G`. The integral union is empty. A criterion quantified only over omitted
integral occurrences passes vacuously and must be rejected as a coverage
certificate.

### A represented lift need not represent every lift

Take `s=0/0/0`; its incidence matrix has all columns `e_0`. Let `G` be a
nonempty additive group, `A=id`, `star=0`, `K_0=G`, and
`K_1=K_2=empty`. The literal tile equations hold. At `p=(0,0,0)`, the
only nonempty selected paired piece has both ancestor letters zero and
both prefixes empty. The supplied domain `S={p}` represents it using
`y=0`.

For every integer `n`, however, `y=(n,-n,0)` is another integral lift of
the same pair, and the corresponding ancestor overlap equals `G`. Every
nonzero such lift is outside `S`. Thus represented-pair coverage holds,
but representation of every nonempty inverse ancestor fails and the full
integral incoming type is infinite. This control requires the incidence
injectivity premise in the claimed equivalence, while leaving the
finite raw-pair union and finite retained histories valid.

### Mandatory inverse-closed but forward-leaking domain

Preserve the existing actual-occurrence control for `s=00/11/22` and
`S={(0,1,0),(1,0,0)}`. The parity equations make this domain inverse closed,
but the forward position pair `(1,1)` has a positive physical-overlap
contribution and leaves the domain. Inverse closure is not forward
completeness. Neither this control nor the finite compact models identify
physical interval length with compact-overlap Haar measure. The diagnostic
must continue to expose the positive forward exit.

## Minimal missing geometric lemma and acceptance boundary

For a faithful integral incoming cover at a supplied source, the new
minimal local lifting obligation is:

> For the authenticated compact tiles and exact embedding/action, every
> nonempty selected paired piece has integral inverse displacement.

For restriction to the proposed finite constructor, add representation of
at least one such ancestor in the domain for every nonempty pair. This
single represented-pair contract can be used instead of separating local
admissibility and representation; equivalence with representation of all
actual inverse ancestors requires injective integral incidence. If only a
set cover is needed, the raw paired-piece containment criterion above is
logically weaker and exact.

Authenticated residue or stable-coordinate profiles can discharge
individual exclusions. They require containment of the entire actual
compact tiles, compatible action and translation maps, and a proved
argument for every rejected pair. Finiteness budgets, exact integer
nonintegrality, samples, and physical interval lengths cannot substitute
for these premises.

The approved implementation should keep canonical Mojo checks and an
independent integer oracle for finite addresses, counts, residue profiles,
and these controls. They verify finite claims only. Passing them cannot
establish the missing authentic compact instance, nonunit product-Haar
scaling in that instance, strict-cut-root positivity, C4, global G1,
Concentration, or general PSC closure. Issue #461 remains open.
