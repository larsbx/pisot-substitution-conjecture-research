# A forward length bound for the two-parameter family

**Status:** exact bivariate certificate and a written termination proof.
Independent human review pending.

**Theorem.** For integers $r\ge4$ and $k\ge r+3$, let
$\sigma_{k,r}=(1,01^k2,0^r1)$. Every irreducible balanced factor in the
iterates of $01/10$ has length at most $(r+2)(k+4)$ on each track.
The balanced-pair algorithm for this seed terminates with coincidence,
and the corresponding substitution tiling flow has pure discrete spectrum.

This continues [issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
The preceding [source review](c4-two-parameter-carrier-stop-go-2026-11-14.md)
records which spectral and balanced-pair hypotheses apply.

## Bounded balanced partitions imply finite forward carriers

Let $S$ be a finite set of nonempty balanced word pairs containing a seed.
Suppose each image of a member of $S$ is a concatenation of members of
$S$. If $L$ is the largest track length in $S$, induction partitions
every iterate of the seed into blocks of length at most $L$. Each
partition boundary equates the two prefix Parikh vectors. The
irreducible factorization cuts at every such equality, so it refines
every one of these partitions. This bounds all irreducible factors
by $L$, even if a certificate block has an interior cut.
Finiteness follows over a finite alphabet.

Include both orientations of every pair in the certificate and adjoin
all three singleton coincidences. Swapping complete tracks commutes
with substitution and concatenation. The substitution of a singleton
coincidence is a sequence of singleton coincidences. It suffices
therefore to check the recorded orientations and rows for the
nonsingletons.

## The bivariate certificate

The [Mojo certificate](../kernel/tests/test_c4_two_parameter_carrier.mojo)
has 30 rows including the seed and two singleton coincidences. Use
$u=r-4\ge0$ and $v=k-r-3\ge0$. The atoms are
$A=01^k2$, $B=1^k2$, and $C=0^r1$. The letters `E,F,G` before a colon
stand for runs of $1/1$ of respective lengths $k-r,k-r+1,k-1$.
A prime on a child index swaps its tracks. A repeat after a child
applies to its preceding diagonal run as well, and a repeat after a
parenthesis applies to the enclosed sequence. For example, the first
row is
$$
\sigma_{k,r}(01/10)=(10/01)(1/1)^{k-1}(12/21).
$$

Each recorded pair has equal Parikh vectors, and the checker verifies
every occurrence row by concatenation on the two respective tracks.
The quantitative bound is coefficientwise after substituting
$r=4+u$, $k=7+u+v$. Every track length is bounded by the expansion of
$(r+2)(k+4)$, the length of $A^{r+2}1^{2(r+2)}$.

For the unbounded word check, take a word $w$ of length $\ell$ on digits
$0,1,2$ and associate to it
$$
P_w(X)=\sum_{i=0}^{\ell-1} w_i X^i.
$$
Its length and polynomial determine the word, including any terminal
zeros. For words $w,z$ and an integer $m\ge0$,
$$
P_{wz}=P_w+X^{|w|}P_z,\qquad
P_{w^m}=P_w\frac{1-X^{m|w|}}{1-X^{|w|}}\quad (|w|>0).
$$
The [word checker](../kernel/psc/c4_polynomial_word.mojo) applies these
identities using full polynomial exponents in $u,v$ and sparse integer
numerators. Parikh counts and lengths are tracked separately and use
addition for concatenation and multiplication by $m$ for repetition.
When comparing words the checker clears a common denominator. It
tests exact equality of sorted exponent-polynomial keys and their
signed coefficients. Every repeat has nonnegative coefficients on
the domain. Every denominator exponent has positive constant
coefficient and nonnegative remaining coefficients. Under
specialization all denominators are therefore nonzero elements of
$\mathbb Q(X)$. Distinct exponent polynomials can agree at individual
parameters. This causes no problem because specialization preserves
equality of the complete formal numerators.

The checker reuses the kernel's sparse integer polynomials and bounds
coefficient sums and products before submitting them to the existing
arithmetic. No specialization of $r,k$ is used in the symbolic
checks. The argument establishes a finite carrier for each parameter
pair with an explicit word-length bound. The number of actual
irreducible states is not claimed to be uniformly bounded by the 30
partition templates.

## Coincidence and spectrum

The incidence matrix has positive square and characteristic polynomial
$X^3-kX^2-2X-r$. These parameters are primitive irreducible Pisot by
the [family calculation and bilateral newborn exclusion](c4-bilateral-newborn-family-2026-11-14.md).

In the finite actual carrier, let $T$ be the set of factors with no
descendant singleton coincidence. Every child of such a factor also
has no descendant coincidence. Thus a nonempty $T$ would be a finite
fully child-closed strict system, forbidden here by the bilateral
newborn exclusion. This proves productivity of every factor. Together
with finite closure it meets
[Barge–Štimac–Williams, Corollary 2](https://doi.org/10.3934/dcds.2013.33.579)
for the distinct letters $0$ and $1$, giving the spectral conclusion.

## Replay and remaining scope

```sh
cd kernel
pixi run --locked mojo run -I . tests/test_c4_two_parameter_carrier.mojo
cd ..
python -m pytest tests/test_c4_two_parameter_carrier_oracle.py
```

An independent literal scanner compares every ordered child occurrence
at seven parameter pairs, including the boundary $k=r+3$ and
$(r,k)=(21,24)$. The native verifier rejects a track flip, reordered
children, fewer coincidences, negative repeat counts, and equality
that would follow from comparing the letter polynomial without length.
The literal replay also shows that the attempted extension to
$(r,k)=(4,6)$ fails to reconstruct a track.

For $r\ge4$, the remaining Pisot bands are $k=r$, $r+1$, and $r+2$.
The zero allowed repeat $k-r-3$ at the proved boundary becomes negative
on these bands. Some literal searches there exceed their resource
limits and receive no termination or nontermination verdict. This
proof does not provide universal forward-carrier extraction for C4.
