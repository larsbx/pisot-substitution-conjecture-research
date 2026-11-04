# C4: every represented cut pair has positive Perron frequency (2026-11-04)

**Status:** Proven algebraic frequency reduction for a **supplied finite fully strict child-closed** balanced-pair SCC. The pair-specific Rauzy overlap corollary is **proposed pending independent geometric audit** of the regular-window cut-and-project step in draft PR #480. General C4, G1, BH, A1', pure discreteness and PSC remain open.

**Baseline:** main a081bb0a2e258f38ad405f5b12285bcd450e9520 (merged PR #481). Research target: Issue #461. The work strengthens the union-overlap reduction of PR #480; it does not import its incorrect earlier one-pair-strong-coincidence-to-*unprimed*-disjointness claim.

## Theorem A: each cut-pair grows with positive PF frequency

Let sigma be primitive on three letters with primitive irreducible Pisot incidence M, spectral radius beta>1 and positive Perron left row ell. Let C={T_1,...,T_r} be a supplied **strongly connected fully strict child-closed** collection of actual irreducible balanced pairs. All *occurrences* in the complete zero-return factorisation of sigma(T_j) must lie in C. No diagonal, omitted child, or escaped child is allowed.

Let P be the matrix of Parikh masses, N the exact child-incidence matrix, and L_j=ell.P_j>0. Completeness gives the exact mass identity PN=MP and consequently L^T N=beta L^T. The SCC hypothesis makes N irreducible, with PF root beta and positive right Perron vector v.

For each state i define the **unordered first-letter pair** e_i (off diagonal) and the represented pair set A(C)={e_i}. For each e in A(C), I_e={i:e_i=e}. Let h be the period of N with cyclic classes C_0,...,C_(h-1) and D=sum_i L_i v_i. Define

~~~text
delta_e = (h/D) max_k sum_{i in I_e intersect C_k} v_i
        >= (1/D) sum_{i in I_e} v_i > 0.
~~~

**Theorem A.** For each e there exists a source j in I_e and a residue-zero generation subsequence n=mqh, for any fixed positive q, such that the number b_e(n,j) of *literal factor occurrences* with first pair e in the complete factorisation of sigma^n(T_j) obeys

~~~text
lim_m b_e(m q h, j)/(beta^(m q h) L_j) = delta_e.
~~~

If N is primitive (h=1), every j works, with limit (sum_{i in I_e} v_i)/D on every n.

**Proof.** Child completeness gives b_e(n,j)=sum_{i in I_e}(N^n)_{ij}. By irreducible matrix Perron–Frobenius theory, each class block of N^h is primitive and the class-wise normalized limit is

~~~text
lim_m beta^(-mh) (N^(mh))_{ij}
      = h v_i L_j/D  for i,j in the same cyclic class;
      = 0             otherwise.
~~~

The factor h follows because the PF mass sum_i v_i L_i is equal in every cyclic class, each carrying D/h. Choose the class maximizing the weighted I_e sum and j inside that nonempty class. Summing the limit over I_e gives delta_e. Passing to n=mqh does not alter the limit. The lower bound follows from maximum >= average over h classes. QED.

This is **not** a bounded-depth strong-coincidence theorem: it guarantees positive density of each represented *noncoincident* cut-pair if such a strict component exists. It does not ensure any represented pair is the genuine Barge–Diamond good edge.

## Corollary B: per-pair subtile overlap (geometric import under review)

Let E^s be M's contracting plane, pi the projection along its Perron line, and R_c the compact **positive-prefix unprimed** Rauzy subtiles for a one-sided fixed point of a power sigma^q. Define Phi(y)=(ell.y,pi y), kappa=|det Phi|>0 and planar Lebesgue measure lambda.

Conditional on independently accepting both of these geometric inputs from PR #480, §§3 and 8:

1. **Uniform cut embedding:** each common Parikh cut x of sigma^n(T_j) followed by pair {c,c'} has distance at most epsilon_n to BOTH R_c and R_c', epsilon_n->0 uniformly over finite C, for n divisible by q. The reason is the literal decomposition x=M^n p(prefix before d)+p(Q): a fixed-point prefix sigma^n(Y_d)Q c differs by M^n of one of finitely many integer prefix differences.
2. **Fixed-origin regular-window count:** for every bounded finite union U of regular planar boxes, the lattice Phi(Z^3) has count of points with internal coordinate in U and physical coordinate [0,X) equal to X lambda(U)/kappa + o(X). Irreducibility excludes any integer functional killing the Perron line; Weyl averages of the dense physical flow on the torus and lattice unfolding yield the box statement. Do NOT substitute an almost-every-translate theorem for arbitrary measurable sets.

**Corollary B (conditional on these geometric inputs):** every represented pair e={c,c'} individually satisfies

~~~text
lambda(R_c intersect R_c') >= kappa delta_e > 0.
~~~

**Proof.** Fix j and n=mqh as in Theorem A. Each distinct factor beginning at a balanced cut of sigma^n(T_j) gives a distinct integer Parikh prefix x; there are b_e(n,j) such cuts of pair e. For any regular open-box cover U of the compact intersection, sufficiently large n put all those projections inside U, since they converge uniformly to both compact subtiles. The box count with X=beta^n L_j gives

~~~text
b_e(n,j) <= beta^n L_j lambda(U)/kappa + o(beta^n L_j).
~~~

Divide and use Theorem A; then infimize over regular box covers by outer regularity. QED conditional on the two independently audited geometric inputs.

The new information is **every represented pair**, not merely the union of pair overlaps. For imprimitive N an arbitrary single source need not see every pair on every n; the class-subsequence construction above is essential.

**Important limitation:** Arnoux–Ito's implication from one positive strong-coincidence pair concerns *primed* subtiles, while their unprimed measure-disjointness theorem assumes all-pair strong coincidence. Do not silently identify these! The present conditional overlap statement alone does not contradict any known good edge or settle Issue #461. In the non-unit regime Euclidean overlap may be abundant even without a strict SCC; no adelic conclusion is claimed.

## Bounded exact controls

**Genuine strict but non-Pisot:** sigma=(012,120,201) has three irreducible balanced states (012,120), (120,201), (201,012). Every complete ordered child row is those same three states, so N is the all-ones 3x3 matrix. Unit physical letter lengths give beta=3, L=(3,3,3), v=(1,1,1), D=9 and delta_e=1/9 for each of the three pair types. At generation n>=1 each pair occurs exactly 3^(n-1) times in each inflated source and normalized frequency equals 1/9. The rank-one incidence is not irreducible cubic; this checks only the algebraic/word-count layer, not Pisot subtiles.

**Synthetic matrix-only imprimitive control:** N=[[0,2],[2,0]] with h=2, beta=2, L=v=(1,1) yields type-0 count 2^n on even n and zero on odd n. The unconditional all-n frequency would be false, whereas delta_e=1 on the correct class subsequence and a Cesaro average gives 1/2. It is *not* an actual balanced-pair PIP example.

**Fail-closed closure control:** retaining just the first state of the genuine three-state strict example omits two actual children. It must not be admitted as a closed system.

Canonical Mojo and independent Python replay all literal controls and the periodic/refusal cases. Neither executable checks a geometric measure, hypothetical strict PIP existence, or general C4.

~~~sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_pairwise_cut_frequency.mojo)
python -m pytest -q tests/test_c4_pairwise_cut_frequency_oracle.py
python tools/make_proof_bank.py --check
~~~

**Acceptance firewall:** exact-head CI and independent mathematics review are pending; the PF theorem and proposed geometric corollary have separate statuses. No governed C4/G1/BH/A1'/PSC promotion.
