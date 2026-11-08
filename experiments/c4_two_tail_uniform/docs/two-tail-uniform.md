# Uniform depth five for the 102 and 120 run families

**Status:** written parameter-uniform proof with executed exact Python controls;
independent human review and proof-assistant formalization pending. The finite
replays do not replace the unbounded word identities. No general C4, A1', BH,
G1, BPA-termination, pure-discreteness or PSC claim is promoted.

Date: November 6, 2026. Inspected repository main:
`ba09fdbd770248905a297303b8de45b3d7c5018d`, containing merged #499. That
revision records C4 as a conditional theorem depending on #138; this note
neither edits nor reclassifies that node. PR #497 was inspected at
`49bc7e1af11b6ab04f84b79f8737500b6de3748b`. The current #500 Lean effort
is separate and is not evidence for the new word identities.

This continues the canonical-periodic-root exploration, but the final
proofs are direct finite-generation word identities. No assumption about
existence of balanced returns, finite balanced-pair closure, compact
subtile measures or a successful graph spectral test is required here.

## 1. The uniform statement

For integers a,b>=0 with s=a+b>=1, and t in {102,120}, define

```
sigma(0)=A=01,
sigma(1)=B=1^a 2 1^b,
sigma(2)=C=t.
```

**Theorem (two-tail uniform source coincidence).** For every such source
and every pair of distinct source letters, there is an equal-Parikh-prefix,
common-next-letter witness at a generation n<=5. By propagating the witness,
each pair has one at the same generation 5. The positions may differ between
pairs; a simultaneous three-letter witness is NOT asserted on the boundary
a=0. When a>=1, all three letter images have a simultaneous witness at n=4.

**Corollary (arbitrary-root productivity).** The complete fifth inflation of
EVERY nonempty balanced word pair contains a genuine one-letter diagonal.
No bound on original word length is imposed. Therefore no nonempty all-
noncoincident collection can be fully child-closed under sigma, or under
any power of sigma. This is not a finite-generation assertion about the
entire descendant set and does not imply BPA termination by itself.

The constant 5 is sharp as a common bound for pairwise source-letter strong
coincidence over the union of these two families. It is not claimed to be
the least productivity time of every balanced root.

Everything below uses zero-based positions: a prefix of length p has
Parikh vector Q with |Q|_1=p, and the common following letter occupies p.

## 2. Common incidence and Pisot verification

All parameters and both tail orders have

```
M_s = [[1,0,1],[1,s,1],[0,1,1]],
det M_s=s,
f_s(x)=x^2(x-2)-s(x-1)^2
      =x^3-(s+2)x^2+2s x-s.
M_s^2=[[1,1,2],[s+1,s^2+1,s+2],[1,s+1,2]] > 0.
```

Thus the source is primitive. A reducible monic cubic over Q has an integer
root. For any integer z<=2, f_s(z)<0. For z>=3, a root would require
(z-1)^2 | z^2(z-2), but these two integers are coprime, an impossibility.
So f_s is irreducible.

Its discriminant is -s(4s^2-13s+32)<0, since the quadratic has negative
discriminant and positive leading coefficient. Thus the Perron root beta
is the only real root, and the other roots form a complex conjugate pair.
Because f_s(s)=-s<0, beta>s. Their squared modulus is s/beta<1. Every
source in the theorem is primitive irreducible Pisot; it is a unit exactly
at s=1. This algebra is independently checked symbolically, not by a
floating-point root classification.

## 3. Exact block expansions

Write F,G,H for sigma^2(0),sigma^2(1),sigma^2(2). For either tail,

```
F=AB,     G=B^a C B^b.
```

The remaining words are as follows:

| Word | Tail 102 | Tail 120 |
|---|---|---|
| H | BAC | BCA |
| U=sigma^3(0) | FG | FG |
| V=sigma^3(1) | G^a H G^b | G^a H G^b |
| W=sigma^3(2) | GFH | GHF |
| sigma^4(0) | UV | UV |
| sigma^4(1) | V^a W V^b | V^a W V^b |
| sigma^4(2) | VUW | VWU |

These are LITERAL word equalities obtained by applying the source images.
Their Parikh vectors, shared across the tail orders, are

```
p(A)=(1,1,0), p(B)=(0,s,1), p(C)=(1,1,1),
p(F)=(1,s+1,1), p(G)=(1,s^2+1,s+1), p(H)=(2,s+2,2),
|G|=s^2+s+3.
```

## 4. Positive a: simultaneous fourth-generation witnesses

### Tail 102, all a>=1 and b>=0

The fourth image of 0 begins `F G^(a+1)`, and the fourth images of 1 and
2 begin `G^a H`. The prefixes

```
F G^a                    (source 0),
G^a B A                  (sources 1 and 2)
```

have equal mass because F=AB. Their next letters are respectively the
first letter of G and the first letter of C. Both are 1: a>=1 makes B,
and hence G, start with 1; C=102 also starts with 1.

The exact simultaneous certificate is

```
n=4, z=1,
Q=(a+1, a(s^2+1)+s+1, a(s+1)+1),
p=a(s^2+s+3)+s+3.
```

No separate b=0 exception is needed for this proof.

### Tail 120, all a>=1 and b>=0

The fourth image of 0 is `F G^(a+1) H G^b`. The proposed prefixes are

```
F G^a B^a C              (source 0),
G^a H B^a                (sources 1 and 2).
```

The first inclusion follows from G=B^a C B^b. If b>0 its next letter is
the first 1 of the following B; if b=0 its next letter is the first 1 of H.

For the other sources, the initial V=G^a H G^b is followed after H by a G
if b>0. If b=0, source 1 next has another V when a>=2, or W when a=1;
source 2 next has W. Both V and W begin in G (a>=1). Thus the extra B^a
is actually present in every case, and is followed by the initial 1 of C.
This explicitly handles the small boundary (a,b)=(1,0).

The masses agree since p(F)+p(C)=p(H). Therefore

```
n=4, z=1,
Q=(a+2, a(s^2+s+1)+s+2, a(s+2)+2),
p=a(s^2+2s+4)+s+6.
```

This is a simultaneous three-letter witness, not a pairwise patchwork.

## 5. Tail 120 with a=0: all three pairs by levels 3,4,5

Now b>=1, B=2 1^b, G=C B^b, H=BCA. Every F,G,H ends in 1. Let J^- denote
J with its final 1 removed (only applied to these words here).

The third words of 1 and 2 are

```
V=H G^b,     W=G H F.
```

The actual prefixes `H G^-` and `G H^-` have common mass p(H)+p(G)-e1
and are both followed by 1. Hence for pair {1,2},

```
n=3, p=b^2+2b+8, Q=(3,b^2+b+2,b+3), z=1.
```

Put X=sigma^4(0)=UV and Y=sigma^4(1)=W V^b. They begin respectively
`F G H` and `G H F`. Remove the final 1 in those displayed prefixes:

```
F G H^- ,     G H F^- .
```

The common mass is p(F)+p(G)+p(H)-e1, giving for pair {0,1}

```
n=4, p=b^2+3b+11, Q=(4,b^2+2b+3,b+4), z=1.
```

Finally sigma^5(0) begins in X and sigma^5(2) begins in Y, because source
0 begins in 0 and source 2=120 begins in 1. The SAME prefix witnesses
therefore prove pair {0,2} at n=5, with the same p,Q,z. No parameter is
sampled or bounded in this argument.

## 6. Tail 102 with a=0: a large-b identity and two exact exceptions

Here B=2 1^b, G=C B^b, H=BAC.

The second images of 0 and 1 start `01 2` and `10 2`, respectively. This
proves pair {0,1} at n=2, p=2, Q=(1,1,0), z=2.

The second images of 0 and 2 have prefixes

```
01 2 1^(b-1),     B 0,
```

both followed by 1. This proves pair {0,2} at n=2, p=b+2,
Q=(1,b,1), z=1.

It remains to handle pair {1,2}. Set

```
U=FG, V=H G^b, W=G F H,
X=UV, Y=W V^b, Z=V U W.
```

Then the fifth images of 1 and 2 are `Z Y^b` and `Y X Z`.
For b>=3, the following are genuine prefixes:

```
P1 = Z G A 2,
P2 = G F H H G^b H G^2.
```

For the first inclusion, Y begins G F=G A B. After `G A 2` the next letter
is a 1 inside B. For the second, expand
`Y=G F H (H G^b)^b`. After the first complete V, take H G^2 from the next
V. Because b>=3, a further G remains and starts with the initial 1 of C.
Both displayed prefixes are therefore followed by 1.

Since Z=H G^b F G^2 F H, their Parikh difference is

```
p(P1)-p(P2)=p(F)+p(A)+e2-p(H)=0.
```

The common certificate is

```
n=5, z=1,
Q=(b+10, b^3+3b^2+5b+10, b^2+4b+10),
p=b^3+4b^2+10b+30.
```

The next-G step is false at b=2. The verifier includes an explicit refusal
control for extrapolating this formula to that parameter. The two exceptions
use finite fourth-generation words, not an unproved extrapolation:

* b=1: n=4, p=27, Q=(7,11,9), z=1.
  The first 28 symbols of sigma^4(1),sigma^4(2) are exactly
  `1022101212101102210110210221` and
  `2101102102210121102211022101`.
* b=2: n=4, p=50, Q=(8,27,15), z=1.
  The first 51 symbols are exactly
  `102211211012112110110221101102102211211102211211211` and
  `211011021022112111022112110121110221121110221121101`.

The certificate verifier reconstructs these finite prefixes from the
source rather than trusting the displayed strings. Tests compare both
strings byte for byte with that independent expansion.

## 7. Common generation five and all balanced roots

An equal-Parikh prefix witness (Q,z) at generation n propagates one level:
replace Q by M_s Q and z by the first letter of sigma(z). This is valid
because sigma sends the two equal Parikh prefixes to equal Parikh prefixes,
and the following equal letters to the same nonempty word. Repeating gives
a positive certificate at generation 5 for every pair.

Let (u,v) be any nonempty balanced pair. If the initial letters agree,
there is already an initial diagonal. Otherwise their level-5 certificate
occurs within the substituted initial letters of u and v. Its positions p
and p+1 are both balanced cuts, so the complete irreducible factorization
of (sigma^5(u),sigma^5(v)) contains (z,z). Earlier cuts cannot destroy these
two consecutive returns.

For closure under sigma^q, further inflate to a multiple of q at least 5.
A diagonal persists because the substitution is nonerasing. Any fully
child-closed collection containing only noncoincident pairs would have to
contain that diagonal, a contradiction. Finiteness of the collection is
not needed for this implication.

## 8. Sharpness of the common SOURCE-level bound

Take sigma=(01,211,120), which is the 120 family at (a,b)=(0,2), and the
source pair {0,2}. At levels 1 through 4, all proper equal-Parikh prefix
cuts with a following letter are as follows; positions are zero-based.

| Level | (position, next letter in image 0, next letter in image 2) |
|---|---|
| 1 | (0,0,1) |
| 2 | (0,0,2) |
| 3 | (0,0,1), (3,1,2) |
| 4 | (0,0,2), (8,2,1), (10,1,0), (29,1,2) |

All next-letter pairs differ. These finite complete scans prove there is
no witness at any level <=4. Level 5 has p=21, Q=(4,11,6), z=1 by section 5.
Thus 5 is the least possible common source-pair bound for the two families.
This is NOT a claim that every source/pair first coincides at 5, nor that
some balanced ROOT needs five generations: a swap can have other diagonals.

## 9. Relation to uniform contraction

The two families range over unbounded determinants s. For s>=2, evaluating
f_s at s and s+1 gives s<beta_s<s+1. The stable conjugate modulus
sqrt(s/beta_s) therefore tends to 1. Nevertheless the purely literal
coincidence depth stays at most FIVE. A vanishing fixed-block geometric
spectral margin does not prevent a fixed source-word escape depth.

Here is an explicit conditional contraction consequence. Suppose a finite
set of noncoincident irreducible balanced pairs contains EVERY noncoincident
child of its members (diagonal children may leave). Let N count these
noncoincident occurrences, and let L_j=ell dot p(u_j)>0. Complete fifth
inflation contains a diagonal of physical length at least ell_min. Hence

```
(L^T N^5)_j <= beta^5 L_j - ell_min,
L^T N^5 <= (beta^5 - ell_min/Lmax) L^T,
rho(N) <= beta * (1 - ell_min/(beta^5 Lmax))^(1/5) < beta.
```

This is source- and component-dependent numerical contraction obtained
from a uniform FIVE-generation word escape. It does not assert a universal
positive epsilon for all s and all Lmax, or existence of a finite BPA closure.

## 10. Exact compressed execution and evidence limits

The new producer represents substitution words by a finite DAG of literal
letters, concatenations, and repeat nodes. All lengths and Parikh vectors
are computed from those constructors. Character-at and prefix-count queries
use integer quotient/remainder in repeat nodes. No caller-supplied summary
is trusted by the theorem-facing verifier. Only a,b,tail and a positive
witness are admitted; the source DAG is reconstructed.

At level <=5 there are at most 18 cached letter-image nodes. Parameters up
to 512 bits are admitted; larger ones raise an explicit budget refusal.
The proof itself has no bit cap. Receipt examples include parameters above
10^100 whose materialized images would have hundreds of digits in their
lengths. Their actual prefix certificates are checked without expanding
those strings. This is finite exact computation, not a substitute for the
symbolic proof.

**Executed:** 19 Python tests passed. The grid a,b in {0,...,20}, a+b>0,
contains 880 source/parameter combinations across the two tails, with 2,640
exhibited certificates and 2,640 propagated fifth-level certificates.
Small literal controls independently expand strings, check the block
prefixes and completely factor 200 inflated balanced roots. The receipt's
24 parameter/tail examples are independently checked with a matrix-power
recursive source-address algorithm that imports no producer code: 288
source-prefix checks, including 168 actual materialized-word checks.
Eight symbolic identities (characteristic polynomial, discriminant,
determinant, root evaluation and Parikh formulas) are independently checked
with SymPy; production admission uses only the standard library.

The first symbolic-check attempt failed because SymPy's characteristic
polynomial generator dropped assumptions from a same-named symbol; the
corrected cross-check uses an assumption-free generator. The initial error
output and the successful rerun are both retained. It was a cross-check
harness defect, not a modification of the word certificates or proof.

Production refusals include false cuts, masses or next letters, malformed
source/pair data, unsupported tail orders, invalid repeat exponents and
budget exhaustion. python -O cannot disable those checks. An impossible
large-b formula at b=2 is explicitly rejected. Huge strings are not silently
materialized when the literal cap is exceeded.

No new Mojo execution, Lean compilation, hosted CI, repository-wide gates
or independent human review is claimed. The existing #496/#500 formal and
native evidence is separate. No branch or claim status is modified by the
standalone artifact.

## 11. Prior art and scope

Strong coincidence uses equal prefix abelianizations followed by a common
letter; Barge--Diamond, *Coincidence for substitutions of Pisot type*, BSMF
130(4), 2002, 619--626, DOI 10.24033/bsmf.2433. The publisher/Numdam landing
page and definition were read; this continuation does not claim a new audit
of the entire article or a new general SC-to-PDS implication.

The danger of substituting source order by incidence data is emphasized
in Sellami, arXiv:1002.3559 (abstract inspected). Sirvent--Starosta,
arXiv:1711.10167, concerns a pair of DIFFERENT substitutions and the lack of
an initial balanced pair (abstract inspected), not a counterexample to the
same-source word identities proved here. No theorem from those papers is
used as an unproved premise of sections 3--7.

The contribution is the two additional unbounded literal tail families,
complete boundary handling, an optimal common pairwise depth and a compact
exact positive-witness implementation. The methods of word substitution,
Parikh addition and coincidence propagation are established. No claim of
an exhaustive novelty search is made. General C4/A1'/G1/BH/PSC remains at
the inspected repository scope, not resolved by this parameter family.
