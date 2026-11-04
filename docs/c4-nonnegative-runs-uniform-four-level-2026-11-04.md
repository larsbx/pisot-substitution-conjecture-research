# C4 nonnegative-run quadrant: uniform strong coincidence by level four

**Date:** 2026-11-04. **Status:** A parameter-uniform literal-word
argument extending merged [PR #477](c4-asymmetric-third-level-coincidence-2026-11-04.md)
to BOTH previously excluded run-zero boundary rays. Includes exact
bounded Mojo and independently written Python controls. **Does not
prove general C4, G1, BH, A1′, PDS or the Pisot Substitution
Conjecture.**

## Source attribution and stop/go

Merged #477 proves that `(01,1^a 2 1^b,012)` has simultaneous
third-level letter coincidence whenever `a,b>=1`. The condition
`a,b>=1` is needed **for its exact third-level address identity**;
it need not be part of a strong-coincidence theorem for the entire
family. The two zero-run rays are not covered by that argument, and
one of them has a genuinely different next-letter and generation.

This note uses only the standard Barge–Diamond notion: the **same
next letter preceded by prefixes of equal Parikh vectors** (not
simply matching characters at equal positions). See
[Barge–Diamond (2002)](https://www.numdam.org/item/BSMF_2002__130_4_619_0/)
and the earlier [source-specific
argument](c4-uniform-third-level-coincidence-family-2026-11-04.md).
A diagonal in the **complete literal balanced-factor reduction**
is the exact consequence. No claim about general pure discreteness
from strong coincidence is made.

## Full nonnegative-run family and exact Pisot hypotheses

For every two nonnegative integers `a,b>=0` with `s=a+b>=1`,
define

~~~text
sigma(0) = A = 01
sigma(1) = B = 1^a 2 1^b
sigma(2) = C = 012

M_s = [1  0  1]
      [1  s  1]
      [0  1  1]

M_s² = [  1       1      2]
       [s+1   s²+1     s+2]
       [  1     s+1     2] > 0.

det M_s = s,
f_s(x)=x³-(s+2)x²+2s x-s
      =x²(x-2)-s(x-1)².
disc(f_s)=-s(4s²-13s+32)<0.
~~~

`M_s²>0` proves primitivity. The monic cubic has no integer
root. For every integer `z<=2`, `f_s(z)<0`.
For `z>=3`, `f_s(z)=0` would force
`(z-1)²|z²(z-2)`; these integers have gcd 1,
a contradiction. Therefore the cubic is irreducible over Q.

The quadratic `4s²-13s+32` has negative discriminant
`169-512=-343` and positive leading coefficient, so the
cubic has precisely one real root `beta_s`.
For `s>=2`, `f_s(s)=-s<0` and
`f_s(s+1)=s²-s-1>0`; hence `beta_s>s`.
For the previously excluded **unit case s=1**,
`f_1(2)=-1` and `f_1(3)=5`, giving
`2<beta_1<3` and again `beta_s>s`.
The two complex conjugates have squared modulus
`det(M_s)/beta_s=s/beta_s<1`.

**Consequently every member with s>=1 is primitive
irreducible Pisot.** Exactly s=1 is unimodular;
the entire subfamily s>=2 is non-unimodular.
The excluded point (a,b)=(0,0) has singular incidence
and is not part of this Pisot theorem.

## Three exact literal occurrence formulas

For each allowed pair, the complete letter words at a single
common substitution generation have equal Parikh prefixes and
identical following letters. The generation depends on the
run-zero chamber.

| Parameter chamber | Generation n | Exact common cut p | Prefix Parikh Q | Common letter |
| --- | ---: | --- | --- | --- |
| a=0, b>=1 | 2 | 0 | (0,0,0) | 0 |
| a>=1, b>=1 | 3 | a(a+b+1)+1 | (1,a(a+b),a) | 1 |
| a>=1, b=0 | 4 | a³+a²+4a+1 | (a+1,a³+2a,a(a+1)) | 1 |

The strictly positive middle row is the already proved
identity of #477, reused rather than rederived. The two boundary
rows have separate proofs below.

### Left run zero: second-level common first letter

Take a=0 and b>=1, so `B=2 1^b`.
The full second-generation images are

~~~text
sigma²(0)=AB,
sigma²(1)=CB^b,
sigma²(2)=ABC.
~~~

Since both `A=01` and `C=012` start with 0,
**all three images begin with letter 0**.
Their length-zero prefix Parikh vectors are (0,0,0).
Hence level n=2, p=0, following letter 0 is a
simultaneous strong-coincidence certificate for every b>=1.
No claim of a positive interior address is required.

### Right run zero: fourth-level common letter

Take a>=1 and b=0. Here

~~~text
B=1^a 2, |B|=a+1, U=B^a C, |U|=a²+a+3.
sigma²(0)=AB; sigma²(1)=U; sigma²(2)=ABC.

sigma³(0)=A B^(a+1) C,
sigma³(1)=U^a ABC,
sigma³(2)=A B^(a+1) C ABC.

sigma⁴(0)=AB U^(a+1) ABC,
sigma⁴(1)=(U^a ABC)^a (AB U ABC),
sigma⁴(2)=sigma⁴(0) (AB U ABC).
~~~

Set

~~~text
p=a³+a²+4a+1,
Q=(a+1,a³+2a,a(a+1)).
~~~

The first p letters of `sigma⁴(0)` are exactly

~~~text
AB U^(a-1) B^a 0,
~~~

where `0` is the first character of the subsequent
`C=012`. Indeed the length is

~~~text
|AB| + (a-1)|U| + a|B| + 1
= (a+3)+(a-1)(a²+a+3)+a(a+1)+1 = p.
~~~

The next character is the second character of C, namely 1.
Because B ends in 2 but has exactly a copies of 1,
the Parikh vector of this prefix is

~~~text
Parikh(AB)+(a-1)Parikh(U)+a Parikh(B)+e_0
=(a+1,a³+2a,a(a+1))=Q.
~~~

The first p characters of `sigma⁴(1)` are

~~~text
U^a A 1^(a-1).
~~~

This follows because `|U^a|=a³+a²+3a`, leaving
`p-|U^a|=a+1` characters into the following ABC.
Since A=01 and B begins with `1^a`,
these additional a+1 characters are `A1^(a-1)`;
the next character is the remaining **1** of B.
The prefix Parikh is

~~~text
a Parikh(U)+Parikh(A)+(a-1)e_1
=(a+1,a³+2a,a(a+1))=Q.
~~~

Finally `sigma⁴(2)` **starts with the entire**
`sigma⁴(0)`. It therefore shares the same
length-p prefix and next letter 1.

These are exact word identities for every positive integer a,
not an extrapolation from a few finite computations.

## Complete balanced-pair consequence: no fully strict component

Take an arbitrary nonempty irreducible noncoincident
balanced pair `T=(u,v)`. Its first letters are distinct;
otherwise a one-letter diagonal would contradict
irreducibility and noncoincidence. Choose the appropriate
row of the table, with generation `n<=4`, cut p,
common prefix Parikh Q and following letter c.

The genuine complete inflated pair `sigma^n(T)` begins
with `sigma^n(u[0])` and `sigma^n(v[0])`.
Its full Parikh-prefix differences vanish at p, since the
two first-letter images both have prefix Q. They still vanish
at p+1, because the next letter on both tracks is c.
Therefore the actual complete irreducible balanced-factor
decomposition includes a one-letter **diagonal (c,c)**
on [p,p+1).

**Uniform family conclusion:** For *every* a,b>=0 with
a+b>=1 and *every* nonempty irreducible noncoincident
balanced root T, the **complete literal reduction of
sigma^n(T)** contains a genuine diagonal child by
some n<=4, with the explicit choice of n in the table.
Thus no nonempty finite fully strict child-closed
noncoincident component exists for any member of this
whole two-dimensional nonnegative quadrant.

The argument assumes neither legality of an initial
swap seed, finite termination of the entire BPA, global G1
extraction, a special incidence determinant nor a uniform
overlap-to-balance dictionary.

## Computational controls and limits

The canonical `kernel/psc/c4_third_level_coincidence_family.mojo`
adds a *distinct* bounded `nonnegative_middle_family` and
`verify_nonnegative_runs` interface. Existing symmetric
and strictly-positive asymmetric APIs preserve their old
input refusal behavior; no older test semantics change.

- In Mojo, a,b each run from 0..8 for independent exact
  letter-word certificate checks, omitting (0,0).
  Full balanced-factor swap tests use a,b from 0..5.
  Invalid, singular and over-cap inputs raise.
- The independent Python oracle separately reconstructs
  the same three cases from source words. Its finite grid
  covers a,b from 0..9 and all two-letter swap balanced
  factors from 0..6. It also verifies the *s=1* unimodular
  Pisot case and s>=2 nonunit spectral arithmetic.
- For a>=1,b=0, the first few **explicit** generation-four
  addresses are `p=7,21,49,97` for a=1,2,3,4, with
  Parikh vectors `(2,3,2),(3,12,6),(4,33,12),(5,72,20)`.
  These are literal source addresses, not incidence-deduced
  least coincidence depths. No minimality assertion is made.

~~~sh
cd kernel && pixi run --locked mojo run -I . tests/test_c4_third_level_coincidence_family.mojo
cd .. && python -m pytest -q tests/test_c4_third_level_coincidence_family_oracle.py
bash tools/verify_all.sh provenance
~~~

The exact family proof is fully symbolic and independent of
the executable caps. The canonical Mojo and independent Python
test files require **fresh exact-HEAD hosted acceptance** before
they may be described as verified by the repository's full CI.

## Negative controls and remaining work

The excluded (0,0) input has det M=0; the unit s=1
inputs cannot be mislabeled as nonunit. This statement
does not assert that our displayed address is the
**earliest** coincidence. Earlier real-phase/productive PIP
finite-cone negatives and the primitive full-rank reducible
strict control are unchanged. The legal-seam/newborn filters
of draft #475 and other ordered-carrier work concern a
different possible mechanism and should not be conflated
with this explicitly coincident family.

The new uniform family result does **not** settle general
C4, BH #139, A1′ #138, G1 #44, #84, pure discrete spectrum
or the Pisot Substitution Conjecture. It does not prove a
general all-state bound of four for arbitrary primitive
irreducible Pisot substitutions, or that strong coincidence
alone implies general PDS. No governed claim statuses are
promoted; independent human review and possible Lean
formalization are separate from the written proof.
