# C4 reversed-run family: uniform left strong coincidence at depth at most four — 2026-11-04

**Status:** New exact word-level family theorem; bounded canonical Mojo and independent literal Python tests. It does **not** close general C4, G1, BH, A1', PDS or PSC. Based on main at merge #479, 700052ba6ec783103dcc684aaab86d9f22d50f17.

## Scope and novelty

For nonnegative integers a,b with s=a+b>=1 define a distinct, reversed-word substitution

~~~text
rho(0)=A=10
rho(1)=B=1^b 2 1^a
rho(2)=C=210.
~~~

This is the wordwise reversal of the family sigma=(01,1^a 2 1^b,012) proved in #479. **Word reversal does not itself transport a left (prefix) strong-coincidence certificate to another left certificate**: it transports it to a right (suffix) one. Therefore the new prefix witnesses below require their own proof. Incidence is unchanged, with M_s=[[1,0,1],[1,s,1],[0,1,1]], det(M_s)=s, M_s^2>0 and chi_s(x)=x^2(x-2)-s(x-1)^2. The irreducible-Pisot proof of #479 applies verbatim: chi_s is irreducible over Q, has negative discriminant and Perron root beta>s, so the conjugate moduli are sqrt(s/beta)<1. The s=1 boundary is a unit; s>=2 are nonunits.

**Theorem (uniform reversal coincidence).** For every such a,b, the three actual iterates rho^n(0),rho^n(1),rho^n(2) admit the same Parikh prefix Q followed by the same letter z at one common physical index p, with n<=4:

| Chamber | n | p | Q=(#0,#1,#2) | z |
|---|---:|---|---|---:|
| b=0, a>=1 | 2 | 0 | (0,0,0) | 2 |
| a=0, b=1 | 4 | 9 | (2,4,3) | 2 |
| a=0, b>=2 | 4 | b^3+b^2+5b+6 | (b+2,b^3+3b+2,b^2+b+2) | 2 |
| a>=1, b=1 | 3 | a+5 | (1,a+2,2) | 1 |
| a>=1, b>=2 | 4 | b(s^2+2s+4)+2s+10 | (b+3,bs^2+bs+2s+b+3,bs+2b+4) | 1 |

No **least** coincidence depth is claimed. The paper result is unbounded in the parameters; the code has an explicit resource cap.

## Exact word identities, including the exceptional boundary

Write the second-generation words

~~~text
F=rho^2(0)=BA
G=rho^2(1)=B^b C B^a
H=rho^2(2)=CBA.
~~~

Then the third-generation words are GF, G^b H G^a, HGF, and the *fourth* are

~~~text
rho^4(0)=(G^b H G^a)(GF) = G^b H G^(a+1) F
rho^4(1)=(G^b H G^a)^b (HGF) (G^b H G^a)^a
rho^4(2)=(HGF)(G^b H G^a)(GF).
~~~

These follow by expanding the source words, not from equality of incidence matrices.

**b=0, a>=1.** The first-letter map sends 0->1, 1->2, 2->2, so its square is constantly 2. All three second-generation images start with 2.

**a>=1, b=1.** Here rho^3(0)=GF, rho^3(1)=GHG^a and rho^3(2)=HGF. In G=B C B^a, the prefix BC is followed by the first letter of B, namely 1. In H=CBA, the prefix CB is followed by the first letter of A, also 1. Both prefixes have Parikh Q=p(B)+p(C)=(1,a+2,2) and length a+5. The first two words begin with G, so this is a simultaneous witness.

**a>=1, b>=2.** Set h=|B|=s+1, g=|G|=s(s+1)+3, f=|F|=s+3 and h2=|H|=s+6. Define S=b*h+1 (immediately after the initial 2 of C inside G), and R=S+f. The length-f literal segment G[S:R] is exactly 10B. Thus its Parikh vector equals p(F)=p(BA). At S the next letter is 1 (the middle of C=210). At R the next letter is 1 as well: when a>=2 it begins the next B within G; when a=1 it begins the next G in the fourth-generation words. The shared first-two-word prefix extends through G^b H and the indicated R-position: this uses b>=2 if a=1.

At the common cut p=b*g+h2+R, the first two words have prefix G^b H G[:R]. The third has prefix H G F G^(b-1) G[:S], both of length p; their Parikh masses agree because G[S:R]=10B has the same mass as F. The third letter at S is 1 and the first two letters at R are 1. Simplifying p and this common mass gives precisely the last row of the table.

**a=0, b>=2.** Now B=1^b2, G=B^b C, F=BA, H=CBA. The first two fourth-generation words share G^b H G. At p=b|G|+|H|+b, their prefix is G^b H 1^b and their next letter is the 2 after the first b ones of B. The third fourth-generation word has prefix H G F G^(b-2) B^b, followed by the initial 2 of C inside the next G. The prefixes have equal Parikh mass since p(G)+p(1^b)=p(F)+b p(B): indeed G=B^b C and p(C)+p(1^b)=p(BA). This reduces to the third table row.

**a=0, b=1.** The preceding construction uses b>=2 and must not be extrapolated. Directly B=12, G=12210, H=2101210, F=1210. In the fourth words the first two share prefix G + 2101 of length 9, followed by 2. The third has prefix H + 12 of length 9, also followed by 2. Both prefixes have Parikh vector (2,4,3). This is a separate exact exceptional certificate.

## Strict-balanced-pair consequence

For an irreducible noncoincident balanced root T=(u,v), u and v start in distinct letters x,y, or their common first letter would be a diagonal factor. Inflating the full words rho^n(u),rho^n(v) gives equal Parikh prefixes Q at p because their first substituted letters rho^n(x),rho^n(y) both have the common witness. The cut at p and cut at p+1 enclose a literal diagonal (z,z) in the **complete zero-return factorisation**. Consequently every nonempty irreducible noncoincident balanced pair is productive by at most four generations, and **there is no finite fully strict child-closed noncoincident component for any member of the reversed family**.

The result is a new word-order family theorem, not an arbitrary-reversal invariance principle, nor a resolution of the general strict recurrent carrier in Issue #461. This direct strong coincidence is stronger than the C4 newborn alternative on the family, but does not settle general C4 or PSC.

## Replay and acceptance

Canonical Mojo extends the *existing* \`kernel/psc/c4_third_level_coincidence_family.mojo\` with \`reversed_closed_run_family\` and \`verify_reversed_closed_run_coincidence\`; the old APIs are untouched. The executable refuses a=b=0, negatives, a or b>8, or a+b>12. Its tests reconstruct the literal three words and true two-letter swap factors. The new independent Python \`tests/test_c4_reversed_run_family_oracle.py\` reconstructs second/third/fourth word identities, Parikh cuts, full swap factorisations, incidence checks and cap refusal.

~~~sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_third_level_coincidence_family.mojo)
python -m pytest -q tests/test_c4_third_level_coincidence_family_oracle.py tests/test_c4_reversed_run_family_oracle.py
python tools/make_proof_bank.py --check
~~~

The targeted CI checks out and verifies the exact PR SHA. Local independent Python checks are not a substitute for hosted canonical Mojo or final mathematical review. Keep this PR draft until exact-head hosted checks pass; no governed PSC claim is promoted.
