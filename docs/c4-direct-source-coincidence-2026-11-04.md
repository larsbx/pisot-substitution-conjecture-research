# C4 direct source certificates: remove the P,N template restriction

**Status:** A parameter-uniform written word proof for the 021 run family,
and a complete finite positive certificate for all 36 sources with M_2.
Independent Python replay has been executed. Native Mojo and full-repository
hosted acceptance remain pending. No general C4, G1, BH, A1', pure-discrete
spectrum, or PSC conclusion is asserted.

Baseline: main `a2e040b8cfc5ecc97083032f66164853cc272f04` (merged #485).
This work is independent of the pending #484/#486/#490 implementation stack.
The #490 counts are preserved as tests of an elimination mechanism, but its
fixed six-state template is no longer needed to exclude strict components
for the 36 sources covered below. Research target: issue #461.

## A source-level certificate excludes every strict template

A simultaneous positive certificate consists of n>=1, p>=0, a nonnegative
integer vector Q with sum Q=p, and a letter z such that, for EACH source
letter c, the literal word sigma^n(c) has prefix Parikh vector Q before
position p and has letter z at that position. No matrix-spectrum or
floating-point approximation can replace either check.

For any nonempty balanced word pair (u,v), the first substituted letters on
both sides contain this certificate. Thus sigma^n(u) and sigma^n(v) have
balanced cuts at p and p+1, and their complete irreducible factorization
contains the actual diagonal (z,z) at that position. Complete factorization
commutes with iterated inflation, since every inherited balanced cut stays
balanced. Consequently no nonempty fully strict child-closed set can exist
for this source. This deduction has NO restriction on P, N, number of
states, phase period, legal language, or bounded word length.

This is not a deduction of pure discrete spectrum from strong coincidence.
It is just the direct implication from a supplied simultaneous literal
witness to a diagonal in every balanced root. Finite witnesses do not prove
BPA finiteness or general extraction outside these covered substitutions.

## Uniform five-generation proof for a different tail order

Let a,b be arbitrary nonnegative integers with s=a+b>=1. Define

```text
sigma(0)=A=01,
sigma(1)=B=1^a 2 1^b,
sigma(2)=C=021.
```

Unlike the earlier forward family, C is 021, not 012. The proof below does
not transfer a left-coincidence witness merely because incidence is equal.
All three source letters have the following explicit simultaneous witness:

| Domain | n | p | Q | z |
|---|---:|---|---|---:|
| a=0, b>=1 | 2 | 0 | (0,0,0) | 0 |
| a>=1, b>=1 | 5 | a(s^2+s+3)+1 | (a+1,a(s^2+1),a(s+1)) | 1 |
| a=1, b=0 | 5 | 16 | (4,7,5) | 0 |
| a>=2, b=0 | 5 | a^3+2a^2+5a+6 | (a+2,a^3+a^2+2a+2,a^2+2a+2) | 0 |

These are exhibited witnesses, NOT assertions of minimum level or cut.
The paper statement has no parameter cap.

Define the exact second-, third- and fourth-level blocks:

```text
F=AB,       G=B^a C B^b,   H=ACB;
U=FG,       V=G^a H G^b,  W=FHG;
X=UV,       Y=V^a W V^b,  Z=UWV.
```

Thus the fifth images are `XY`, `Y^a Z Y^b`, `XZY`. The first and third
share the entire prefix X, and X=F G^(a+1) H G^b. The second begins with Y
when a>=1. Also |G|=s^2+s+3 and Parikh(G)=(1,s^2+1,s+1).

For **a,b>=1**, G ends with the literal word `1B`: the symbol immediately
before its last B is the last symbol of an earlier B if b>=2, or the last
symbol of C if b=1. In either case it is 1. Write G=T 1 B. The prefixes

```text
F G^(a-1) T        (first and third fifth images),
G^a 0             (second fifth image)
```

have the same mass `a Parikh(G)+e0`, the same length `a|G|+1`, and common
next letter 1. For the second image, use Y beginning in V and
V=G^a H G^b with H beginning 01. For the first/third use X and G=T1B.
The mass identity is
`Parikh(F)-e1-Parikh(B)=Parikh(A)-e1=e0`.
This proves the entire positive chamber, including a=1 and b=1.

For **a>=2,b=0**, G=B^a C and V=G^a H. The first and third fifth images
have prefix `F G^(a+1)` followed by the first 0 of H. The second fifth
image begins with Y, and Y starts with at least two V blocks. Its prefix
`G^a H B^a` is followed by the first 0 of C within the next G. The two
prefix masses agree because
`Parikh(F)+Parikh(G)=Parikh(H)+a Parikh(B)`.
Their common mass and length are the final table row.

For **a=1,b=0**, that second-V argument does NOT apply. The literal first
17 symbols of the fifth words are respectively

```text
01121202112021010
12021010211201120
01121202112021010.
```

Each has prefix mass (4,7,5) before position 16 and letter 0 there. This is
a separate finite exceptional proof, not an extrapolated boundary formula.
For **a=0,b>=1**, the second images are AB, C B^b and A C B; each begins 0.

The incidence is M_s=[[1,0,1],[1,s,1],[0,1,1]], det M_s=s, and M_s^2>0.
Its characteristic polynomial is x^2(x-2)-s(x-1)^2. It has no integer
root: it is strictly negative on integers <=2, while a root z>=3 would
force (z-1)^2 to divide z^2(z-2), whose gcd with (z-1)^2 is 1. The cubic
is therefore irreducible. Its discriminant is -s(4s^2-13s+32)<0; its unique
real Perron root beta>s because f(s)=-s. The complex conjugates have
squared modulus s/beta<1. Hence every member is primitive irreducible
Pisot, unit exactly at s=1.

Combining the explicit witnesses with the first section excludes EVERY
fully strict child-closed noncoincident component for this infinite family,
without choosing any particular Parikh or child-incidence matrix.

## All 36 sources with M_2: a finite positive certificate

The exact finite domain is

```text
sigma(0) in {01,10},
sigma(1) in {112,121,211},
sigma(2) in {012,021,102,120,201,210}.
```

The receipt records one (n,p,Q,z) for each source. A complete literal
verifier checks all three source images, not merely pairwise endpoints.
The exhibited-generation histogram is
`{1:4, 2:9, 3:4, 4:8, 5:7, 6:3, 7:1}`; every source is certified by n<=7.
The largest literal single-letter image checked has 1,692 symbols.
For example `(01,211,120)` has the level-seven witness
`p=464, Q=(75,252,137), z=1`.

The conclusion is now independent of P,N, state count and period for all
36 sources. This is strictly stronger in scope than the earlier 46,656
ordered-template exclusion. It does not claim a universal theorem about
all source orders for arbitrary total run s, nor does the finite table
prove the separate infinite 021 family (that rests on the word proof above).

## Reproduction and acceptance boundaries

```sh
python -m pytest -q tests/test_c4_direct_source_coincidence_oracle.py
python tests/test_c4_direct_source_coincidence_oracle.py
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_direct_source_coincidence.mojo)
python tools/make_proof_bank.py --check
```

The new native verifier reuses `psc.bpa.apply_substitution`,
`psc.bpa.decompose`, and the existing `ClosedRunCoincidence` receipt type.
All prior run-family APIs remain unchanged. The new 021 executable is
limited to 0<=a,b<=8, 1<=a+b<=12, and all materialized words to 500,000
symbols. These are rejection budgets, not mathematical counterexamples.
Letters are range-checked before indexing; false masses, positions, next
letters, and malformed/budget-exhausted inputs raise.

Locally, seven new Python tests pass, including all 36 literal certificates,
108 actual swap factorizations, 70 parameter combinations with independently
reconstructed block identities, both exceptional/zero boundaries, 120
longer-root or swap factorizations on the 0..4 parameter grid, and refusal
controls. A separate recursive-expansion/Counter replay checks all 36
receipts and the family formulas without importing the discovery module.
The 12 inherited #490 Python tests also pass in the supplied bundle.

Mojo and pixi are unavailable locally, and a network clone attempt failed
DNS resolution; native compilation and full-repository governance are NOT
claimed. Exact-head hosted validation remains required. The proof is a
written argument plus bounded replays, not a Lean theorem or an independent
referee endorsement. No governed claim status has changed.

## Prior art and scope

Strong coincidence means equal prefix abelianizations followed by the same
letter, not just physical or endpoint alignment; see Barge--Diamond,
*Coincidence for substitutions of Pisot type*, BSMF 130(4), 2002, 619--626,
DOI 10.24033/bsmf.2433. Balanced-pair reduction and coincidence algorithms
are established methods: Sirvent--Solomyak, *Pure Discrete Spectrum for
One-dimensional Substitution Systems of Pisot Type*, CMB 45(4), 2002,
697--710, DOI 10.4153/CMB-2002-062-3. No novelty is claimed for these notions.
The deliverable is the explicit 021 word identity and source-specific
certificates. A universal strict-carrier theorem remains outside this work.
