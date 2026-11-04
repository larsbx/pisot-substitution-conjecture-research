# C4 periodic-class Parikh rigidity: three independent masses in every phase — 2026-11-04

**Status:** New conditional algebraic theorem for supplied complete finite strict Pisot balanced-pair SCCs. It does not exhibit or exclude such an SCC. Independent written-proof review and exact-head hosted checks are pending. No general C4, G1, BH, A1', PDS, or PSC status change.

**Baseline:** \`main@fd3b64e2e25a7d8a7a8623a52677a8822e52f6c5\`, including merged [#482](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/482). Target: [Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461). This strengthens the earlier **global** rank-three theorem and the period-sensitive positive-frequency theorem in #482.

## 1. Exact hypotheses and scope

Let sigma be a **primitive irreducible ternary Pisot** substitution, M its integral 3x3 incidence matrix and beta>1 its Perron root. Let C be a nonempty finite **strongly connected, completely strict child-closed** set of actual irreducible noncoincident balanced word pairs T_i. The *entire occurrence-indexed complete zero-return factorisation* of sigma(T_j), with repetitions, is required to consist solely of members of C. A selected recurrent path, missing/escaping child, or diagonal child is not acceptable.

Define P in Z_{\u22650}^{3xr} by its nonzero balanced-state Parikh columns, and N in Z_{\u22650}^{rxr} by the multiplicities of ALL literal child occurrences (row child, column parent). Then

~~~text
P N = M P.
~~~

Strong connectivity makes N irreducible. Let h be its graph period and C_0,...,C_(h-1) its nonempty cyclic classes, indexed so N maps C_k to C_(k+1 mod h). Write P_k for the 3x|C_k| submatrix of the Parikh columns of class k and B_k for the integer |C_k|x|C_k| diagonal block N^h on this class.

## 2. Cubic Pisot powers remain irreducible

**Lemma 1.** For every positive integer h, the minimal polynomial f_h of beta^h over Q has degree three. In fact f_h=chi_(M^h) and is irreducible over Q.

**Proof.** Every other algebraic conjugate alpha of the irreducible Pisot beta satisfies |alpha|<1, whereas beta>1. If beta^h were rational, every embedding of Q(beta) would send beta^h to that same rational number, contradicting |alpha^h|<1<beta^h. The field Q(beta) has prime degree three, and Q(beta^h) is a nontrivial subfield, so [Q(beta^h):Q]=3. All eigenvalues of M^h are the hth powers of beta's three conjugates. Therefore its monic degree-three characteristic polynomial is f_h and is irreducible. QED.

One may compute f_h *exactly* using integer M^h: if A=M^h then

~~~text
f_h(x) = x^3 - tr(A) x^2
       + ((tr A)^2 - tr(A^2))/2 * x - det(A).
~~~

This formula is not a floating-point spectral check.

## 3. Theorem — full Parikh rank in EACH cyclic phase

**Theorem 2 (phase-wise rank/size rigidity).** Under the exact hypotheses of §1, for every class k:

~~~text
rank_Q(P_k)=3,
chi_(M^h)(x) divides chi_(B_k)(x) in Z[x],
|C_k| >= 3.
~~~

Consequently the entire strict component satisfies

~~~text
|C| >= 3h,     h <= floor(|C|/3).
~~~

In particular **no hypothetical three-, four- or five-state fully strict PIP SCC can be imprimitive**. If |C|=3h, every class contains exactly three states, P_k is rationally invertible, and

~~~text
B_k = P_k^(-1) M^h P_k.
~~~

Every phase of a hypothetical periodic carrier therefore has its *own* three independent literal balanced-state masses. Rank three in only the union of phases is not sufficient.

**Proof.** Since N maps a phase to its successor, N^h preserves each class. Restrict the h-fold intertwining P N^h=M^h P to the columns of class k:

~~~text
P_k B_k = M^h P_k.
~~~

The rational image W_k of P_k is nonzero (all balanced word states are nonempty) and M^h-invariant. By Lemma 1, the characteristic/minimal polynomial of M^h is irreducible of degree three. Its only rational invariant subspaces are 0 and Q^3; hence W_k=Q^3. This proves rank three and |C_k|>=3. Since P_k is surjective as a rational map, its kernel is B_k-invariant and the quotient action of B_k is similar to M^h. Thus chi_(M^h) divides chi_(B_k), and the polynomial divisibility is integral because both are monic integer polynomials. Summing the h class-size inequalities proves |C|>=3h. If |C_k|=3, P_k is square and invertible, giving the displayed rational-conjugacy identity. QED.

**Why this differs from the earlier global rank theorem:** global rank three only says im(P)=Q^3. The present result excludes a periodic flat system whose *individual recurrent phase* occupies a rank-one or rank-two rational Parikh plane, even if distinct planes together span Q^3.

## 4. Perron-weighted Parikh **equipartition** across phases

**Theorem 3 (exact phase balance).** Let v>0 be a right Perron vector of N, Nv=beta v (the eigenvalue equality follows from the positive left vector ell^T P of the complete strictly closed system). Write v^(k) for v restricted to class k, with zeros outside. Then

~~~text
P v^(0) = P v^(1) = ... = P v^(h-1) = (P v)/h > 0
~~~

componentwise. Thus **every phase carries the same Perron-weighted mass of every original source letter**, not merely equal total physical length. In particular every class contains states whose combined Parikh supports contain 0, 1 and 2.

**Proof.** Each N^h v^(k)=beta^h v^(k). Hence M^h P v^(k)=beta^h P v^(k). This nonzero nonnegative vector is a positive scalar c_k times the unique positive Perron right eigenvector of M. Moreover N v^(k)=beta v^(k+1), and P N=M P, so M P v^(k)=beta P v^(k+1). Since M acts on its Perron vector by beta, c_k=c_(k+1), and all scalars agree. Sum over all h classes to obtain (P v)/h. QED.

**Limit:** This statement is over the real/algebraic Perron field; it is not an assertion that each individual Parikh *integer column* equals another column or that literal letter counts are exactly equal at finite depth.

## 5. Exact synthetic saturation and negative controls

Use the true PIP incidence matrix M_2 for sigma=(01,112,012):

~~~text
M = [1 0 1; 1 2 1; 0 1 1],  chi_M=x^3-4x^2+4x-2, det M=2, M^2>0.
~~~

For h=2,3,4 construct **synthetic algebraic** block-cyclic systems of r=3h states with phase blocks

~~~text
P = [I, M, M^2, ..., M^(h-1)]  (3 by 3h).
N_(k+1,k) = I (0<=k<h-1),    N_(0,h-1) = M^h,
all other 3x3 blocks zero.
~~~

Then PN=MP, N is irreducible of period h, every B_k=M^h and every P_k=M^k is rationally invertible. This saturates the size bound |C|=3h for **every** tested h. In the PF right eigenvector of this synthetic N, phase k has v^(k)=beta^(h-1-k) v_M, so P_k v^(k)=beta^(h-1) v_M identically, independently confirming Theorem 3. All matrix arithmetic is integer and exact.

**These are NOT actual irreducible noncoincident balanced word pairs.** In particular the basis columns of P_0=I cannot be Parikh masses of noncoincident irreducible balanced words of length one. Algebraic saturation is explicitly **not** a C4 counterexample. A real strict primitive but **reducible-characteristic** four-state control, sigma=(10,102,211), has global Parikh rank two and must be refused as a PIP-phase certificate. Likewise a broken intertwiner or incorrect cyclic-phase designation must fail closed.

The canonical bounded Mojo checker checks the supplied integer M,P,N, phase labels, full PN=MP, forward phase transitions and three-by-three Parikh minors; the independent Python oracle reconstructs the block matrices, char(M^h) irreducibility by exact integer roots, determinant certificates, equipartition identities symbolically, and malformed inputs. Neither executable builds an actual strict SCC from word rows; that is a separate prerequisite. No Lean machine-checked theorem is claimed.

## 6. Research consequence and next test

Before attempting to construct or exclude an imprimitive strict carrier for Issue #461, its **every cyclic phase** must separately have at least three actual noncoincident balanced factors with independent masses. For |C|<6, the matrix N must be primitive, so the all-generation/every-source Perron frequency formula of merged #482 applies without selecting a cyclic subsequence.

A reproducible next eliminator is the equality case |C|=3h: test all nonnegative integral rational-conjugacy templates B_k=P_k^(-1) M^h P_k with **actual** endpoint-signature, newborn and literal child-closure constraints; reject synthetic templates before calling them balanced-pair realizations.

~~~sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_periodic_parikh_rigidity.mojo)
python -m pytest -q tests/test_c4_periodic_parikh_rigidity_oracle.py
python tools/make_proof_bank.py --check
~~~

**Claim firewall:** this is an exact algebraic theorem assuming a complete strict SCC, not a construction/exclusion of any PIP SCC. General C4, G1, BH, A1', PDS and PSC remain open; hosted exact-head and independent proof review are pending.
