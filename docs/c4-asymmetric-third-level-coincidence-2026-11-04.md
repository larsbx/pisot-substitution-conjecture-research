# Uniform asymmetric third-level strong coincidence — 2026-11-04

**Status:** A two-parameter uniform literal-word result, building on the
merged symmetric [PR #476](c4-uniform-third-level-coincidence-family-2026-11-04.md).
It is a **family-scoped proof**, not a general PSC/C4/G1/PDS resolution.
Canonical Mojo and an independent exact Python oracle require current-head
hosted acceptance. No governed-claim promotion is requested.

## Stop/go and prior work

The previously merged symmetric family used images
`(01,1^k 2 1^k,012)` and an equal-Parikh prefix followed by the
same next letter in all three third images. The necessary definition
is the **literal strong-coincidence** condition from
[Barge–Diamond (2002)](https://www.numdam.org/item/BSMF_2002__130_4_619_0/),
not equality of letter addresses without abelianized-prefix equality.
The next warranted question is whether equality of the **two run
lengths** is a mathematical premise of that certificate.

It is not. Unequal runs change the coincidence address without
changing the incidence matrix for a fixed run **sum**. Continue by
generalizing the existing canonical verifier rather than duplicating
an unrelated finite-census engine; keep the old symmetric API intact.

## Two-parameter non-unit Pisot family

For *all integers* a,b >= 1, define

~~~text
sigma_{a,b}(0) = A = 01
sigma_{a,b}(1) = B = 1^a 2 1^b
sigma_{a,b}(2) = C = 012
s = a+b >= 2,  |B| = s+1.
~~~

Its incidence matrix depends **only on the sum** s:

~~~text
M_s = [1  0  1]
      [1  s  1]
      [0  1  1]

M_s² = [  1     1     2]
       [s+1   s²+1  s+2]
       [  1    s+1    2] > 0,

det M_s = s >= 2,
f_s(x) = x³ - (s+2)x² + 2s x - s
       = x²(x-2) - s(x-1)²,
disc(f_s) = -s(4s²-13s+32) < 0.
~~~

The matrix square proves primitivity. To prove irreducibility,
a rational root of monic `f_s` would be an integer z.
For every integer z <= 2, both terms in the last expression
are nonpositive and cannot both vanish, so `f_s(z)<0`.
For z >= 3, `f_s(z)=0` would force
`(z-1)² | z²(z-2)`. But
`gcd((z-1)²,z²(z-2))=1`, and `(z-1)²>1`.
Thus no rational root exists; the cubic is irreducible.

The quadratic `4s²-13s+32` has negative discriminant
`169-512=-343` and positive leading coefficient,
so the characteristic discriminant is negative.
The unique real root `beta_s` obeys

~~~text
f_s(s)   = -s < 0
f_s(s+1) = s²-s-1 > 0
s < beta_s < s+1.
~~~

The two remaining roots are complex conjugates, and their
squared modulus is `det(M_s)/beta_s=s/beta_s<1`.
Therefore **every** `sigma_{a,b}` is primitive,
irreducible Pisot and non-unimodular. This is an algebraic
parameter-uniform proof, not a finite spectral screen.

## Uniform asymmetric common address

Put

~~~text
p_{a,b} = a(s+1)+1 = a(a+b+1)+1,
Q_{a,b} = (1, a s, a).
~~~

For all three source letters t=0,1,2 the exact literal
third-generation image `sigma_{a,b}³(t)` has
(1) prefix Parikh vector **Q** through its first **p** letters,
and (2) next letter **1** at zero-based index **p**.

The proof is a complete word identity. With the definitions
`A,B,C` above:

~~~text
sigma²(0) = A B
sigma²(1) = B^a C B^b
sigma²(2) = A B C

sigma³(0) = A B^(a+1) C B^b
sigma³(1) = (B^a C B^b)^a (A B C) (B^a C B^b)^b
sigma³(2) = A B^(a+1) C B^b A B C.
~~~

Since a>=1, `sigma³(1)` starts with `B^a C`.
Its prefix of length `p=a|B|+1` is exactly
`B^a0`, followed by the second letter `1`
of `C=012`. Its Parikh vector is
`(1,a(a+b),a)`.

The prefix of length p in `sigma³(0)` is the
two-character word `A`, followed by the word
`B^a` **with its final letter removed**.
The removed letter is 1 because b>=1. Thus the
prefix Parikh vector is

~~~text
Parikh(A) + Parikh(B^a) - e_1
= (1,1,0) + (0,a(a+b),a) - (0,1,0)
= (1,a(a+b),a) = Q.
~~~

It is followed immediately by the removed letter **1**.
Finally `sigma³(2)` begins with all of `sigma³(0)`,
so the same prefix and next-letter statement holds.

This proves a **simultaneous, common-address strong-coincidence
certificate for all three unordered letter pairs** for
every a,b>=1, irrespective of whether the runs are symmetric.
No upper bound on a or b is used.

## Complete balanced-factor consequence

Let T=(u,v) be any nonempty **irreducible noncoincident**
Parikh-balanced pair, legal or not. Its first two letters
are distinct, otherwise the one-letter common prefix would
already have been a balanced cut.

The words `sigma³(u)`, `sigma³(v)` start with
`sigma³(u[0])` and `sigma³(v[0])`. At position p
they have equal complete prefix Parikh vectors Q,
and at p+1 they still have equal prefixes because
their next letters both equal 1.

Thus the **complete actual balanced-factor reduction**
of `sigma³(T)` contains the diagonal one-letter child
`(1,1)` at positions [p,p+1). In a strictly child-closed
noncoincident system, every iterated child must remain
noncoincident, contradicting the full three-generation
factorization. Consequently **no nonempty strictly
child-closed noncoincident balanced-pair component exists
for any a,b>=1**.

The argument is uniform, conditional on the exact
family images, and does not require global BPA finiteness,
seed reachability, a nonunit realized-overlap dictionary,
or G1 extraction.

## Fixed-incidence, variable word addresses

At any fixed sum s>=2, all s-1 positive splittings
`(a,b)=(1,s-1),...,(s-1,1)` share **exactly the
same incidence matrix, characteristic polynomial, Perron
spectrum and determinant**. Yet this explicit common
strong-coincidence occurrence lies at

~~~text
p_{a,b}=a(s+1)+1,
~~~

and takes s-1 distinct values. At s=4, the three
substitutions have explicit common addresses
`6, 11, 16`, despite identical incidence.

This is an important **word-realizability warning** for
C4: rational rank, Perron spectrum and incidence alone
do not determine occurrence addresses. It does **not**
claim the displayed p is the *earliest* possible
strong-coincidence position.

## Canonical and independent reproducibility

The existing canonical module
`kernel/psc/c4_third_level_coincidence_family.mojo`
is extended with `asymmetric_middle_family(a,b)`
and `verify_asymmetric_third_level(a,b)`. The old
symmetric functions delegate to the generalized
source and preserve their public names. The executable
checks `1<=a,b<=16`, keeps exact whole words and
Parikh prefixes, and raises on invalid or capped inputs.

The canonical
`kernel/tests/test_c4_third_level_coincidence_family.mojo`
adds the unequal-run grid, all three literal two-letter
swap reductions, fixed-incidence varying-index control
and invalid-run refusals.

The independent
`tests/test_c4_third_level_coincidence_family_oracle.py`
uses separately written exact string substitution and
full balanced factorization. It checks the bounded
asymmetric grid, the integer incidence/characteristic
constraints, three true swap diagonals and the fixed-s
address difference. These finite tests are **not** the
proof for arbitrary positive a,b.

~~~sh
cd kernel && pixi run --locked mojo run -I . tests/test_c4_third_level_coincidence_family.mojo
cd .. && python -m pytest -q tests/test_c4_third_level_coincidence_family_oracle.py
bash tools/verify_all.sh provenance
~~~

**Acceptance limit:** the symbolic word proof above is
directly inspectable, but the exact new GitHub HEAD has
not yet produced a completed hosted canonical Mojo
or independent-oracle acceptance receipt. Preserve the
distinction between paper proof, bounded local
arithmetic and independent reviewed/machine-checked
results.

**Non-claims:** This result is family-specific. It
does not show that general three-letter strong
coincidence implies pure discrete spectrum, prove
C4 for arbitrary primitive irreducible Pisot
substitutions, or settle BH #139, A1' #138,
G1 #44, #84 or the Pisot Substitution Conjecture.
No governed claim status is promoted.
