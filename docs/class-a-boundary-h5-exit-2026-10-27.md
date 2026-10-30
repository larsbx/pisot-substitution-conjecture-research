# Class A minus boundary: H5 has a uniform 2–3-step typed-coincidence exit

**Status (2026-10-27):** new one-source, genuinely occurrence-indexed, *existential* coincidence witness, stacked on [PR #361](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/361). This builds on the complete H4 outgoing star, not on a claimed forward-closed 13-label carrier. **No universal BH, C4, G1 or PSC promotion.** Independent human review pending. Prior three-source literature/assumption stop-go is at \`docs/class-a-boundary-e2-stopgo-2026-10-27.md\` and \`docs/class-a-boundary-h4-2026-10-27.md\`; the present result uses the same exact proper-prefix overlap dynamics, not any unproved unimodular or tiling-realization transfer.

## Work shown

### Assumptions and hypotheses

For every \(k,t\in\mathbb Z_{\ge0}\), take the minus class-A boundary chamber
\[
\varepsilon=-1,\qquad n=k+t+3,\qquad d=2n-1-k,\qquad A=n+d,\qquad N=n-1.
\]
The actual ordered words are \(\sigma(x)=xy^Ax,\ \sigma(c)=cy^nx,\ \sigma(y)=xy^Nc\). All offsets are full three-coordinate bottom-minus-top Parikh vectors. Let \(\beta=n+2+\alpha\) be the Pisot root, \(h=1/\beta\), \(u=d/(\beta-1)=1+\alpha-2h\), and normalized positive physical lengths
\[
L_y=1,\quad L_c=b=1+h,\quad L_x=a=b+u=2+\alpha-h.
\]
The established exact polynomial certificates give \(0<h<\alpha\), \(0<\alpha+h<1\) and \(1<u<2\). These are *inherited and rechecked* by the canonical H4 certificate. No floating root estimate, presumed global tile-length independence, unimodularity, or non-unit realization inference enters.

The source
\[
H_5=(x,y,2,2,-5)
\]
is the **real** H4=(x,y,0,-2,4) last/run child with actual ordinals \((A+1,t+2)\) for every member: \(\sigma(x)_{A+1}=x,\ \sigma(y)_{t+2}=y\), and \(t+2\le N=k+t+2\). The inherited \`h4_child_allowed\` and exact \`verify_h4_packet\` verify strict geometry and the entire Parikh offset, not just equal letters. Independently its physical shift is
\[
s_{H5}=2a+2b-5=1+2\alpha,\qquad
a-s_{H5}=1-\alpha-h>0.
\]
Hence \(H_5\) itself has a strictly interior x/y overlap for all \(k,t\ge0\).

### Derivation / reduction

The incidence column update is
\[
M(2,2,-5)^\mathsf{T}=(1,-3,2d-n+5)^\mathsf{T}.
\]
Combining this with the actual proper prefixes yields **three parameter chambers** and *complete selected witness paths* (all occurrence pairs top/bottom):

| Chamber | Selected path of typed actual children | True ordinals | Length |
|---|---|---|---:|
| \(k=0\) | \(H_5\to E_0=(x,x,0,-3,4)\to V=(y,x,0,1,-1)\to C\) | \((A+1,0),(t+1,0),(2,1)\) | 3 |
| \(k=1\) | \(H_5\to E_1=(x,x,0,-3,3)\to C\) | \((A+1,0),(1,4)\) | 2 |
| \(k\ge2\) | \(H_5\to G=(y,x,0,-3,3)\to C\) | \((2d-n+3,0),(1,4)\) | 2 |

Here \(C=(y,y,0,0,0)\) is the **stronger typed-coincidence terminal**, not a zero-offset unequal-type half-coincidence.

**First child: symbolic word-index proof.** Top LAST \(i=A+1\), bottom FIRST \(j=0\) always has typed target
\[
(x,x,0,-3,d-2n+5)=(x,x,0,-3,4-k).
\]
For \(k=0,1\) its target physical shift is respectively \(1-3h\) or \(-3h\). Both are strictly between \(-a\) and \(a\), proving a real x/x overlap.

For \(k\ge2\), select the top **run** index \(i=2d-n+3=A+2-k=k+3t+10\) and bottom FIRST \(0\). The full Parikh target simplifies to
\[
(y,x,0,-3,\,2d-n+6-i)=(y,x,0,-3,3)=G.
\]
The upper word bound is exactly \(A-i=k-2\ge0\), so the index is a RUN precisely in the claimed chamber (it would be LAST at \(k=1\), nonexistent at \(k=0\)). This conditional legality is explicitly verified in the **shifted nonnegative parameter cone** \(k=2+q,q\ge0\), not by invoking a falsely all-chamber symbolic RUN index. The target shift \(-3h\in(-1,0)\) is strictly interior for y/x since \(a>2\).

**Terminal children: exact common starts.** For \(E_1\) and \(G\), the true top run \(i=1\) begins at \(a\), and the bottom x-image run \(j=4\), translated by the inflated source shift \(-3\), begins at \(-3+(a+3)=a\). Both are y tiles, so the child at \((1,4)\) is the **zero-Parikh, zero-physical-offset, equal-y terminal \(C\)**. These are actual runs since \(N=n-1\ge2\) and \(A\ge8\).

For \(k=0\), the E0 shift \(1-3h\) inflates to \(\beta-3\). Its top run index \(t+1\) against bottom FIRST \(0\) has full target \((y,x,0,1,n-4-t)=(y,x,0,1,-1)=V\). This intermediate state has physical shift \(h\in(0,1)\), a strict y/x overlap. At \(V\), the top y-image run 2 begins at \(a+1\); the bottom x-image run 1, translated by the inflated \(V\) shift \(+1\), begins at \(1+a=a+1\). The two actual y tiles coincide, so \((2,1)\) reaches \(C\). Here \(N\ge2\), including the smallest \(n=3\).

All final common child starts are **inside** the inflated parent interiors: in the \(E_1/G\) cases they start at \(a>0\), and in the \(V\) case at \(a+1>0\); each ends before its top inflated parent right boundary by the positive remaining literal run/tail. They are not boundary-only coincidences.

The existing \`symbolic_child\` verifies H4→H5, the two LAST→E branches, \(E_0\to V\) and the two distinct y/y terminal prefixes coefficientwise over \(\mathbb Q[t,k]\). For the \(k\ge2\) branch, the coefficientwise formula is checked separately from the **conditional** actual RUN bound \(k-2\ge0\); the latter is certified using the shifted cone and member-specific \`verify_member_edge\`. This avoids reintroducing the invalid all-parameter RUN assumption warned about in AGENTS.md.

### Evidence and replay

Canonical \`kernel/psc/class_a_boundary_h5_exit.mojo\`: \`certify_h5_exits\` checks exact coefficient identities and domain signs; \`h5_path(k,t)\` constructs the explicit two- or three-step true ordinal path; \`verify_h5_path\` requires the inherited H4 ancestor and verifies each edge using literal words, all Parikh coordinates and exact Perron overlap. Native \`kernel/tests/test_class_a_boundary_h5_exit.mojo\` tests 66 members spanning all three branches, checks the H4 ancestry and **every edge** including C, and refuses changed intermediate targets, negative parameters and nonexistent/incorrect RUN types. Independent Fraction oracle \`oracles/python/class_a_boundary_h5_exit.py\` and \`tests/test_class_a_boundary_h5_exit.py\` replay 108 finite members, rejecting undecidable signs after a bounded refinement rather than guessing.

From root:
\`\`\`sh
python -m pytest -q tests/test_class_a_boundary_h5_exit.py
\`\`\`
From \`kernel/\`:
\`\`\`sh
pixi run --locked mojo run -I . tests/test_class_a_boundary_h5_exit.mojo
pixi run --locked mojo run -I . class_a_boundary_h5_exit.mojo
\`\`\`
Dedicated \`.github/workflows/class-a-boundary-h5-exit.yml\` checks the exact PR head and inherited native H4 regression. The local exploratory double-precision search that identified the candidate was **not** used to certify the theorem or any claim; a separate independent Python finite oracle replays using exact rational Perron enclosures. Hosted acceptance is pending unless the exact-head workflow completes successfully.

### Negative controls

The \(k=0\) formal index \(i=A+2\) for the \(G\) route is outside the image, while for \(k=1\) index \(i=A+1\) is a LAST x and must **not** be called a RUN y. Consequently the \(k=0\) endpoint route has an extra step, and the \(k=1\) route passes through x/x, not y/x. A wrong last y/y pairing, a corrupt symbolic coefficient or a forged intermediate packet must be rejected even if the supplied final C is correct. The selected stage rank is **not** extended to every outgoing edge or to the entire H4 image.

### Non-claims / remaining gaps

This proves **H5 has an existential typed-coincidence path of length at most three** on the entire specified minus boundary chamber. It does **not** enumerate all H5 children, prove the other twelve labels in H4's image productive, or provide a globally forward-closed carrier. It does not discharge the universal occurrence-compatible BH obstruction (#139), the C4 ordered hub-residual word obligation, one-sided A1′ (#138), general G1, the internal-space/return-lattice realization interface or PSC. Human review remains pending separately from mathematical progress. The next useful step is to reuse the three H5 regimes as an actual productive base packet in a genuinely compositional typed-child carrier, preserving genuine cyclic exits rather than attempting all-edge strict descent.
