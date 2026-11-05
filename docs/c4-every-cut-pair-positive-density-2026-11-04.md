# C4: every represented cut pair has positive Perron frequency (2026-11-04)

**Status:** Proven algebraic frequency reduction for a **supplied finite fully strict child-closed** balanced-pair SCC. The pair-specific Rauzy overlap corollary rests on the regular-window cut-and-project count with a written proof in #480 §8 (automated adversarial audits of 2026-11-04: holds); it carries that status, human review pending. General C4, G1, BH, A1', pure discreteness and PSC remain open.

**Baseline:** main a081bb0a2e258f38ad405f5b12285bcd450e9520 (merged PR #481). Research target: Issue #461. The work strengthens the union-overlap reduction of PR #480; it imports nothing from Arnoux–Ito; see #480 §4 for the corrected convention `R_c = −X(c)'` (the positive-prefix subtiles are Arnoux–Ito's primed family, up to sign).

## Theorem A: each cut-pair grows with positive PF frequency

Let sigma be primitive on three letters with primitive irreducible Pisot incidence M, spectral radius beta>1 and positive Perron left row ell. Let C={T_1,...,T_r} be a supplied **strongly connected fully strict child-closed** collection of actual irreducible balanced pairs. All *occurrences* in the complete zero-return factorisation of sigma(T_j) must lie in C. No diagonal, omitted child, or escaped child is allowed. Strong connectivity is essential: a cut pair carried only by transient states of a larger strict system has frequency 0 and is not covered (control: the 6-state closure of `(02,20)` under `10/102/211`, whose sink SCC carries only `{1,2}`; see #480 §5).

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

The factor h follows because the PF mass is equal in every cyclic class: with m_k = sum_{i in C_k} L_i v_i, each child of a class-k state lies in class k+1, so beta m_k = sum_{j in C_k} (L^T N)_j v_j = sum_{i in C_(k+1)} L_i (N v)_i = beta m_(k+1); hence m_k = D/h. Choose j in I_e intersect C_(k*), where k* attains the maximum; this set is nonempty because the maximum is positive. Summing the limit over I_e gives delta_e. Passing to n=mqh does not alter the limit. The lower bound follows from maximum >= average over h classes. QED.

This is **not** a bounded-depth strong-coincidence theorem: it guarantees positive density of each represented *noncoincident* cut-pair if such a strict component exists. It does not ensure any represented pair is the genuine Barge–Diamond good edge.

## Corollary B: per-pair subtile overlap (rests on #480 §3 and §8; human review pending)

Let E^s be M's contracting plane, pi the projection along its Perron line, and R_c the compact **positive-prefix** Rauzy subtiles (Arnoux–Ito's primed family up to sign; #480 §4) for a one-sided fixed point of a power sigma^q. Define Phi(y)=(ell.y,pi y), kappa=|det Phi|>0 (computed in the coordinates of E^s that define lambda) and planar Lebesgue measure lambda.

Conditional on independently accepting both of these geometric inputs from PR #480, §§3 and 8:

1. **Uniform cut embedding:** each common Parikh cut x of sigma^n(T_j) followed by pair {c,c'} has distance at most epsilon_n to BOTH R_c and R_c', epsilon_n->0 uniformly over finite C, for n divisible by q. The reason is the literal decomposition x=M^n p(prefix before d)+p(Q): a fixed-point prefix sigma^n(Y_d)Q c differs by M^n of one of finitely many integer prefix differences.
2. **Fixed-origin regular-window count:** for every bounded finite union U of regular planar boxes, the lattice Phi(Z^3) has count of points with internal coordinate in U and physical coordinate [0,X) equal to X lambda(U)/kappa + o(X). Irreducibility excludes any integer functional killing the Perron line; Weyl averages of the dense physical flow on the torus and lattice unfolding yield the box statement. Do NOT substitute an almost-every-translate theorem for arbitrary measurable sets.

**Corollary B (given these geometric inputs, proved in #480 §3 and §8):** every represented pair e={c,c'} individually satisfies

~~~text
lambda(R_c intersect R_c') >= kappa delta_e > 0.
~~~

**Proof.** Fix j and n=mqh as in Theorem A. Each distinct factor beginning at a balanced cut of sigma^n(T_j) gives a distinct integer Parikh prefix x; there are b_e(n,j) such cuts of pair e. For any regular open-box cover U of the compact intersection, sufficiently large n put all those projections inside U, since they converge uniformly to both compact subtiles. (Compactness lemma: for compact A, B and open U ⊇ A∩B there is ε>0 with N_ε(A) ∩ N_ε(B) ⊆ U.) The box count with X=beta^n L_j gives

~~~text
b_e(n,j) <= beta^n L_j lambda(U)/kappa + o(beta^n L_j).
~~~

Divide and use Theorem A; then infimize over regular box covers by outer regularity. QED, given the two geometric inputs of #480 §3 and §8 (human review pending).

The new information is **every represented pair**, not merely the union of pair overlaps. For imprimitive N an arbitrary single source need not see every pair on every n; the class-subsequence construction above is essential.

**Scope:** the positive-prefix `R_c` are Arnoux–Ito's primed subtiles up to sign (#480 §4). In the unit case a left SC pair gives `λ(R_c∩R_c') = 0` (Lemma P of #480 §4), so Corollary B and Theorem A(4) of #480 agree on SC pairs; Corollary B adds exclusion power only on cut pairs without an SC witness, through the open disjointness question. Corollary B alone does not settle Issue #461. In the non-unit regime no adelic conclusion is claimed.

## Bounded exact controls

**Genuine strict but non-Pisot:** sigma=(012,120,201) has three irreducible balanced states (012,120), (120,201), (201,012). Every complete ordered child row is those same three states, so N is the all-ones 3x3 matrix. Unit physical letter lengths give beta=3, L=(3,3,3), v=(1,1,1), D=9 and delta_e=1/9 for each of the three pair types. At generation n>=1 each pair occurs exactly 3^(n-1) times in each inflated source and normalized frequency equals 1/9. The rank-one incidence is not irreducible cubic; this checks only the algebraic/word-count layer, not Pisot subtiles.

**Synthetic matrix-only imprimitive control:** N=[[0,2],[2,0]] with h=2, beta=2, L=v=(1,1) yields type-0 count 2^n on even n and zero on odd n. The unconditional all-n frequency would be false, whereas delta_e=1 on the correct class subsequence and a Cesaro average gives 1/2. It is *not* an actual balanced-pair PIP example.

**Fail-closed closure control:** retaining just the first state of the genuine three-state strict example omits two actual children. It must not be admitted as a closed system.

Mojo checks the literal per-pair counts `3^(n−1)`, a period-two recursion and the exit count of the subset control. The Python oracle builds `N` from literal factorisations for the uniform control, computes the period and cyclic classes from the support of `N`, verifies supplied exact Perron data `(β, v, L)` (positivity and the two eigen-equations), and computes `δ_e = h·max_k Σ_{i∈I_e∩C_k} v_i / D`. For the uniform control this `δ_e = 1/9` is derived from the literal `N`; for the synthetic period-two control `N` is supplied. Neither executable computes any geometric measure, hypothetical strict PIP existence, or general C4.

~~~sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_pairwise_cut_frequency.mojo)
python -m pytest -q tests/test_c4_pairwise_cut_frequency_oracle.py
python tools/make_proof_bank.py --check
~~~

**Acceptance firewall:** exact-head CI and independent human mathematics review are pending; the PF theorem and the geometric corollary have separate statuses (the latter inherits #480 §8). No governed C4/G1/BH/A1'/PSC promotion.
