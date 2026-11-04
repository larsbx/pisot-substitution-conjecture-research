# A compact M-adic counting bridge for non-unit cut pairs

**Status:** written, scoped proof; independent human mathematical review
pending. This note constructs its own compact residue space and proves the
counting statements there. It does not assert an unproved identification
with an entire adelic representation space, a tiling of degree one, or PSC.
The companion [finite occupancy certificate](c4-nonunit-residue-occupancy-2026-11-04.md)
explains why retaining residue data matters.

The ingredients are standard: a matrix-adic completion, finite-index
cut-and-project counts, Perron--Frobenius and a compact graph-directed
construction. The contribution here is their explicit assembly for the
repository's literal balanced-cut and two-track arguments. The
[literature gate](c4-nonunit-residue-occupancy-literature-gate-2026-11-04.md)
records the prior art and the hypotheses.

## 1. Standing hypotheses and the space actually constructed

Let `sigma` be a primitive, irreducible Pisot substitution on three letters.
Write `M` for its nonsingular column-incidence matrix, `beta>1` for its
Perron root, `D=abs(det M)`, `ell>0` for a left length vector, and `f>0`
for its right frequency vector with `sum f_c=1`. Put `ellbar=ell f`.
Let `E^s`, `pi`, `M_s`, `Phi(x)=(ell x,pi x)` and `kappa` have the meanings
in the companion note. The arguments also work in higher degree with the
corresponding contracting space, but no higher-alphabet implementation is
claimed here.

Define the compact abelian group

```text
H_M = inverse_limit_q (Z^3 / M^q Z^3),
iota(x) = (x mod M^q Z^3)_q,
E_hat = E^s x H_M,
x_star = (pi x, iota(x)).
```

The bonding maps are the natural reductions. Give `H_M` Haar probability
measure `nu`. A level-`q` residue cylinder has measure `D^-q`. Give `E_hat`
product measure `mu=lambda x nu`. This is a compact finite-place factor
attached to the integral module, together with the contracting Euclidean
space. We do **not** identify `E_hat` with the full, generally noncompact,
finite-place product used in every formulation of non-unit Rauzy tiles.

For `D=1`, `H_M` is the one-point group and the construction reduces to
the Euclidean one.

### The matrix action and the missing determinant factor

Multiplication by `M` induces a continuous endomorphism `T` of `H_M`.
It is injective. If `T h=0`, the representative of `h` at level `q+1`
satisfies `M x in M^(q+1) Z^3`, so nonsingularity gives `x in M^q Z^3`.
The level-`q` component of `h` is therefore zero for every `q`.

The image of `T` is exactly the kernel of reduction to `Z^3/M Z^3`.
For the reverse inclusion, take a compatible sequence whose level-one
residue is zero. Choose each level-`q+1` representative in `M Z^3`, divide
it by `M`, and reduce modulo `M^q Z^3`. Different choices differ by
`M^q Z^3`, and the resulting sequence is compatible. This constructs
the inverse to `T` on that kernel.

Thus `T` is an isomorphism onto an index-`D` clopen subgroup, and
`nu(T B)=nu(B)/D` for measurable `B`. Since
`abs(det M_s)=D/beta`, the internal action

```text
A(z,h) = (M_s z, T h)
```

satisfies

```text
mu(A B) = beta^-1 mu(B).                                    (1)
```

It contracts the Euclidean factor and sends the whole compact factor into
the zero cylinder of increasing depth. In particular `A^n` tends uniformly
to zero on bounded subsets of `E^s` times `H_M`.

Equation (1) is the determinant correction absent from Euclidean-only
non-unit volume arguments. In the classical full internal space the
corresponding scaling is [Minervino--Thuswaldner, Lemma 3.1](https://arxiv.org/pdf/1402.2002).
Here it follows directly from finite subgroup indices.

## 2. The integral lattice and regular-cylinder counting

Let

```text
Gamma = { (ell x, x_star) : x in Z^3 } in R x E_hat.
```

This is a discrete cocompact subgroup. Discreteness follows by projection
onto the lattice `Phi(Z^3)` in `R x E^s`. If `B` is a bounded half-open
fundamental parallelepiped for that lattice, then `B x H_M` is a measurable
fundamental domain for `Gamma`: subtract the unique integral lattice
translate placing the first two coordinates in `B`, and adjust the last
coordinate by the same `iota(x)`. Its measure is `kappa`.

The physical projection is injective because the entries of `ell` are
rationally independent. The internal projection is dense. Indeed, in any
fixed residue cylinder `r mod M^q`, its Euclidean coordinates contain
`pi(r+M^q Z^3)`. This is dense in `E^s`: irreducibility excludes an
annihilating integer character of `pi(Z^3)`, and `M_s^q` is invertible.

For a regular internal rectangle `U x [r]_q`, with `U` a bounded finite
box union, the fixed-coset count in the companion note gives

```text
#{ x in Z^3 : 0 <= ell x < X, x_star in U x [r]_q }
     = X lambda(U)/(kappa D^q) + o(X)
     = X mu(U x [r]_q)/kappa + o(X).                         (2)
```

Finite unions obey the same formula. To see this without double counting,
refine their cylinders to a common finite depth and their Euclidean boxes
to disjoint regular pieces. No limit in `q` is interchanged with the limit
in `X`.

These regular sets are sufficient for compact outer approximation.
The product space is locally compact and metrizable, `mu` is Radon, and
open boxes times clopen residue cylinders form a base. A compact set can
therefore be covered by a finite regular union with measure arbitrarily
close to its measure. Consequently (2) can bound counts of points in a
shrinking neighborhood of **any fixed compact set**, without assuming its
boundary is null.

## 3. Lifted prefix sets and their measures

Choose `k>=1` and a one-sided fixed point `w` of `sigma^k`. Define

```text
R_hat_c = closure { p(P)_star : P c is a prefix of w }.
```

They are compact: the Euclidean prefix projections are bounded by the
Pisot discrepancy bound, and `H_M` is compact. Their Euclidean projections
are exactly `R_c`, since projection of a compact set is closed and contains
the defining prefix set densely.

Counting the actual `c`-vertices of prefixes `sigma^(kn)(w_0)` in regular
outer covers and applying Perron--Frobenius and (2) gives

```text
mu(R_hat_c) >= kappa f_c / ellbar > 0.                       (3)
```

For every positive multiple `m` of `k`, the literal decomposition of the
fixed point into `sigma^m`-images gives the compact set equation

```text
R_hat_c = union_{sigma^m(d)=P c S}
            ( A^m R_hat_d + p(P)_star ).                    (4)
```

The union is indexed by actual occurrences. It is finite, so taking
closures commutes with this union. Both inclusions follow from the fixed
point word decomposition, with no replacement of prefixes by suffixes.

Write `v_c=mu(R_hat_c)`. From (1) and (4),
`beta^m v <= M^m v` componentwise. Pairing with `ell>0` forces equality
in every coordinate. Therefore

```text
v = s f for some s>0,
the distinct occurrence pieces in (4) are measure-disjoint. (5)
```

The first statement uses the uniqueness of the positive Perron vector
of the primitive matrix `M^m`; the positivity was established in (3).
The second follows because a finite union has the sum of the measures
of its pieces only when every pairwise intersection is null.

### A one-pair coincidence consequence

Let `c` and `c'` be distinct letters. If `sigma^n(c)=P a S` and
`sigma^n(c')=P' a S'` with `p(P)=p(P')`, take
a multiple `m` of `k` with `m>=n`. Inflating the witness preserves the
equal prefixes and gives the same following letter. The two occurrences
in (4) then have identical translation and different source letters.
By (5), their intersection has measure zero. Injectivity and the scaling
of `A^m` give

```text
left SC(c,c') => mu(R_hat_c intersection R_hat_c') = 0.      (6)
```

This proof works for `D>1` as well as `D=1`. Its conclusion is about
the **lifted** sets. It cannot be projected to a Euclidean null-overlap
claim. The classical full-space analogue is consistent with
Minervino--Thuswaldner, Theorem 8.3 and Section 8.2; no degree-one tiling
or spectral conclusion is being imported from those statements.

## 4. Strict balanced cuts in the lifted space

Let `C` be a supplied nonempty finite fully strict child-closed set of
irreducible noncoincident balanced pairs for `sigma`. Every factor in
every complete inflation belongs to `C`. Let `A(C)` be its unordered
first-letter cut pairs, and `L_max` its largest physical state length.
Define

```text
Z_hat = union_{ {c,c'} in A(C) }
           (R_hat_c intersection R_hat_c').
```

**Theorem M1 (lifted cut-pair bound).**

```text
mu(Z_hat) >= kappa/L_max > 0.                               (7)
```

*Proof.* Fix a source `(u,v)` of physical length `L` and inflate it by
`n` divisible by `k`. Complete factorization gives at least
`beta^n L/L_max` proper factor starts. Each is a distinct integer Parikh
vector `x` with `0<=ell x<beta^n L` and following cut pair in `A(C)`.

For an occurrence within `sigma^n(d)`, compare the prefix in the top
word with one in `w` obtained by placing that same letter `d` after a
fixed prefix `Y_d` of `w`. Their difference is `M^n z`, for `z` in a
fixed finite set determined by `u` and the `Y_d`. Its internal image is
`A^n z_star`, tending uniformly to zero. The bottom word has the same
property. Hence the lifted cut is near both corresponding compact sets.

Given a regular open cover `U` of `Z_hat`, all these cut points belong
to `U` for sufficiently large `n`. Otherwise compactness would give a
limit in one of the pair intersections outside `U`. Formula (2), with
`X=beta^n L`, now bounds the number of cuts by
`beta^n L mu(U)/kappa+o(beta^n)`. Divide and take the infimum over such
covers to obtain (7).

**Theorem M2 (lifted two-track bound).** For every letter `c`,

```text
mu(R_hat_c) >= 2 kappa f_c / ellbar,
theta_hat_c := kappa f_c/(ellbar mu(R_hat_c)) <= 1/2.         (8)
```

Both tracks of `sigma^n(u,v)` have the same number of `c`-vertices.
They are disjoint as integer lattice points: a shared Parikh prefix
followed by `c` would supply the coincident factor `(c,c)`. The preceding
approximation, regular-cover count and Perron asymptotics apply to their
union and prove (8). By (5), `theta_hat_c=kappa/(ellbar s)` is independent
of `c`. No identification of this number with the reciprocal of an
integer covering degree is needed or claimed here.

For a supplied strict strongly connected component, the existing correctly
phased per-pair cut frequencies can also be inserted in exactly the same
counting proof: whenever a represented pair has a literal cut density
`delta_e>0` along a stated subsequence, its lifted overlap has measure at
least `kappa delta_e`. The frequency premise remains separate; transients
do not inherit an SCC's positive density.

## 5. A precise target for finite upper certificates

**Corollary M3 (finite-cylinder approximation).** For a compact
`K subset E_hat`, let `K_r^(q)` be the Euclidean projection of the
part of `K` in cylinder `[r]_q`, and put

```text
K^[q] = union_r (K_r^(q) x [r]_q).
```

Then the compact sets `K^[q]` decrease to `K`, and

```text
mu(K^[q]) = D^-q sum_r lambda(K_r^(q)) decreases to mu(K).   (9)
```

The inclusion at successive depths follows by reducing the residue. If
`(z,h)` is in every `K^[q]`, choose `(z,h_q)` in `K` agreeing with `h`
through depth `q`. Then `h_q` tends to `h`, so compactness puts `(z,h)`
in `K`. The measure statement is continuity from above, with finite
initial measure. For two compact sets `K,L`, the same argument gives
`mu(K^[q] intersection L^[q])` decreasing to `mu(K intersection L)`.

For `q` a multiple of the fixed-point period `k`, equation (4) gives
the **exact finite slice formula**

```text
(R_hat_c)_r^(q)
  = union_{sigma^q(d)=P c S, p(P) mod M^q Z^3=r}
        ( M_s^q R_d + pi p(P) ).                            (10)
```

All points of `A^q R_hat_d` have zero residue at depth `q`; this proves
the cylinder restriction. Euclidean projection of `R_hat_d` is `R_d`,
which proves (10). Multiples of `k` are cofinal, so they suffice in (9).

Consequently a proposed certificate for a represented cut pair `e={c,c'}`
has a concrete acceptance condition. Supply certified bounded measurable
Euclidean outer sets `B[c,r]` containing the slices in (10), a fixed depth
`q` that is a positive multiple of `k`, and a certified lower bound
`delta_lower>0` for that pair's literal strict
cut density. It is enough to prove

```text
D^-q sum_r lambda(B[c,r] intersection B[c',r])
       < kappa delta_lower.                               (11)
```

The left side bounds the true lifted overlap from above, whereas the
strict cut argument bounds it from below. Every occurrence in (10) must
be represented; omitting a child invalidates an outer bound. The
normalization of `lambda`, `kappa` and the certified density must agree.
Floating point pictures and point-cloud occupancy do not certify (11).

If the true lifted overlap is strictly below a proposed threshold, (9)
shows that some finite residue depth has an intersection measure below
that threshold. This does **not** provide a uniform depth, an effective
rate, or the needed exact Euclidean outer enclosures. Nor has a strict
PIP component with a certified positive density been supplied here.
Equation (11) is a precisely specified next certificate, not a completed
exclusion theorem for an unknown component.

## 6. What has advanced and what remains open

Equations (2), (7) and (8) supply a non-unit **residue-space version** of
the repository's regular-window and strict-cut counting arguments. They
are no longer contingent on pretending that the Euclidean contraction
has determinant `1/beta`. Equation (6) also records the correct place
to apply the one-pair disjointness argument in the non-unit case.

This does not by itself exclude a hypothetical strict Pisot component.
Its cut pairs have no strong-coincidence witnesses, by the existing word
argument. Combining (6) with (7) therefore reproduces that necessary
condition; it does not prove a contradiction for an unwitnessed pair.

The useful next target is an occurrence-compatible **upper bound** for
the measure of a represented lifted overlap, below the positive lower
bound forced by its strict cut frequency. Finite residue cylinders provide
exact arithmetic constraints for such a bound. They must be combined with
certified Euclidean enclosures and every actual child occurrence. No finite
residue separation alone proves all-depth separation, and equal integral
prefix translations cannot be separated by adding more residue levels.

This note establishes neither that upper bound nor a complete finite
ancestry model, a degree-one multiple tiling, general strong coincidence,
G1, BH, A1', C4 or PSC. Identifying this compact integral-module lift with
a particular localized adelic model is a separate representation theorem
if a downstream argument needs it. The proofs here do not need that
identification.
