# Uniform strong coincidence in a two-parameter family of ternary Pisot substitutions

**Draft for mathematical review · November 2026**

**Abstract.** For integers \(a,b\ge 0\) with \(a+b\ge1\), consider
\(\sigma=(01,1^a21^b,012)\) and its wordwise reversal
\(\rho=(10,1^b21^a,210)\). Both have primitive irreducible Pisot incidence. For each substitution a single Parikh prefix followed by the same letter occurs simultaneously in the three substituted letter images at a common generation at most four. We give explicit witnesses in all parameter regimes. Every irreducible noncoincident balanced pair therefore has a diagonal descendant by generation four.

## Statement and conventions

A substitution acts on words by concatenation. Write \(P(w)=(|w|_0,|w|_1,|w|_2)^\top\). A witness \((n,p,Q,z)\) means that for each source letter \(i\), the first \(p\) letters of the literal word \(\tau^n(i)\) have Parikh vector \(Q\), and the next letter is \(z\). The index \(p\) is zero-based and counts letters. The physical position for Perron lengths \(\ell\) is \(\ell Q\). Put \(s=a+b\).

| Substitution and parameters | \(n\) | \(p\) | \(Q\) | \(z\) |
|---|---:|---|---|---:|
| \(\sigma,\ a=0,\ b\ge1\) | 2 | 0 | (0,0,0) | 0 |
| \(\sigma,\ a,b\ge1\) | 3 | \(a(s+1)+1\) | \((1,as,a)\) | 1 |
| \(\sigma,\ a\ge1,\ b=0\) | 4 | \(a^3+a^2+4a+1\) | \((a+1,a^3+2a,a(a+1))\) | 1 |
| \(\rho,\ b=0,\ a\ge1\) | 2 | 0 | (0,0,0) | 2 |
| \(\rho,\ a=0,\ b=1\) | 4 | 9 | (2,4,3) | 2 |
| \(\rho,\ a=0,\ b\ge2\) | 4 | \(b^3+b^2+5b+6\) | \((b+2,b^3+3b+2,b^2+b+2)\) | 2 |
| \(\rho,\ a\ge1,\ b=1\) | 3 | \(a+5\) | \((1,a+2,2)\) | 1 |
| \(\rho,\ a\ge1,\ b\ge2\) | 4 | \(b(s^2+2s+4)+2s+10\) | \((b+3,bs^2+bs+2s+b+3,bs+2b+4)\) | 1 |

These are exhibited depths. Minimality is outside the statement.

## Incidence calculation

In both cases the column incidence matrix is
\[
M_s=\begin{pmatrix}1&0&1\\1&s&1\\0&1&1\end{pmatrix},\quad
\det M_s=s,\quad f_s(x)=x^2(x-2)-s(x-1)^2.
\]
Its square is positive. For an integer \(m\le2\), \(f_s(m)<0\). If an integer \(m\ge3\) is a root, \((m-1)^2\) divides \(m^2(m-2)\), impossible because the two are coprime. The monic cubic is irreducible. Its discriminant is \(-s(4s^2-13s+32)<0\), and \(f_s(s)=-s\). Hence the unique real root is the Perron root \(\beta>s\). The conjugate pair has squared modulus \(s/\beta<1\). The substitution is unimodular exactly at \(s=1\).

## Forward word proof

Use \(A=01\), \(B=1^a21^b\), \(C=012\) and denote the second images by \(F=AB\), \(G=B^aCB^b\), \(H=ABC\).

- If \(a=0\), the second images \(AB,CB^b,ABC\) all start in 0.
- If \(a,b\ge1\), the third images are \(FG,G^aHG^b,FGH\). In the first and third, take \(A B^{a-1} B[:|B|-1]\). In the second, take \(B^a0\). Here \(B[:k]\) is the length-\(k\) prefix. Both lengths equal \(a|B|+1\). The first prefix removes the final 1 from \(AB^a\), so its mass equals \(P(B^a0)\). Its next letter is the final 1 of that copy of \(B\). In the second word, \(B^a0\) ends at the first letter of \(C\) inside \(G\), so the next letter is also 1.
- If \(b=0, a\ge1\), the fourth images are \(FG^{a+1}H,(G^aH)^a(FGH),FG^{a+1}H(FGH)\). The first and third have prefix \(FG^{a-1}B^a0\), followed by the middle letter of \(C\). The second has prefix \(G^a0 1^a\), followed by the first 1 of \(B\) inside \(H=ABC\). Their common mass follows from \(P(F)+aP(B)=P(G)+aP(1)\). This gives the stated level-four entry.

## Reversed word proof

Now \(A=10\), \(B=1^b21^a\), \(C=210\). The second images are \(F=BA\), \(G=B^bCB^a\), \(H=CBA\). The third are \(GF,G^bHG^a,HGF\). Put \(U=G^bHG^a\). The fourth images are \(UGF,U^bHGFU^a,HGFUGF\), with concatenation understood.

- If \(b=0\), the square of the first-letter map is constant at 2.
- If \(a\ge1,b=1\), use \(BC\) in the initial \(G\) of the first two third images and \(CB\) in the initial \(H\) of the third. Both prefixes are followed by 1.
- If \(a,b\ge1,b\ge2\), take \(S=b|B|+1\) and \(R=S+|F|\). The literal segment \(G[S:R]=10B\) has mass \(P(F)\). The next letter at \(S\) is 1. The next letter at \(R\) is also 1, either within \(G\) when \(a\ge2\) or at the next \(G\) when \(a=1\). When \(a=1\), the first two fourth images have that next \(G\) because \(b\ge2\). Use prefixes \(G^bH G[:R]\) in the first two fourth images and \(HGF G^{b-1} G[:S]\) in the third. Equality follows from the segment mass. Expanding their mass gives the last row.
- If \(a=0,b\ge2\), the first two fourth images share \(G^bHG\). Use prefix \(G^bH1^b\), followed by 2. In the third use \(HGF G^{b-2}B^b\), followed by 2 inside the next \(G\). Here \(P(G)+P(1^b)=P(F)+bP(B)\) because \(P(C)+P(1^b)=P(BA)\).
- If \(a=0,b=1\), one has \(B=12,G=12210,H=2101210,F=1210\). The first two fourth images start with \(G\,2101\), followed by 2. The third starts with \(H\,12\), followed by 2. Both prefixes have mass \((2,4,3)\).

## Balanced-pair consequence

A balanced pair has equal full Parikh vectors. Its canonical factorization cuts at every index where the prefixes have equal Parikh vectors. An irreducible noncoincident pair has different initial letters, since equal initial letters would give a first diagonal factor. Apply the simultaneous witness to the first substituted letter on each side. The cuts at \(p\) and \(p+1\) are consecutive and enclose the diagonal \((z,z)\) in the full inflation. Earlier cuts persist under nonerasing inflation, so the diagonal is an actual descendant in the iterated complete factorization. A fully strict child-closed collection of noncoincident balanced pairs would contain all these descendants, which is impossible. The same argument yields both left and right strong coincidence for each family member by using the two separately proved prefix witnesses and word reversal for the suffix direction.

The paper's claims concern coincidence witnesses and strict child closure. The supporting computation checks bounded parameter grids. No spectral conclusion is included.

**Provenance and prior art.** See the pinned [forward proof](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/fd3b64e2e25a7d8a7a8623a52677a8822e52f6c5/docs/c4-closed-run-family-four-level-coincidence-2026-11-04.md), [positive-run proof](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/fd3b64e2e25a7d8a7a8623a52677a8822e52f6c5/docs/c4-asymmetric-third-level-coincidence-2026-11-04.md) and [reversed proof](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/fd3b64e2e25a7d8a7a8623a52677a8822e52f6c5/docs/c4-reversed-run-family-four-level-coincidence-2026-11-04.md). Definitions and context are in [Barge–Diamond](https://doi.org/10.24033/bsmf.2433) and [Arnoux–Ito](https://doi.org/10.36045/bbms/1102714169). A specialist should check overlap with known \(\beta\)-substitutions, conjugacy classes, and established coincidence families before any novelty claim.
