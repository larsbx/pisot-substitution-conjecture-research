# Nakaishi (2024) PSC claim: first-entry audit and transfer boundary

**Date:** 2026-10-13  
**Source:** Kentaro Nakaishi, *Pisot Substitution Conjecture and Rauzy Fractals*, arXiv:2401.07771v1 (15 January 2024), https://arxiv.org/html/2401.07771v1  
**Disposition:** **Do not import universal PSC, tiling, or strong coincidence claims.** Retain the arguments as candidate techniques pending independent repair/verification.  
**Scope:** targeted source audit, not a formal refutation of the conjecture or a complete review of the paper. No claim promotions.

## Comparison to our programme

Nakaishi uses the prefix–suffix SFT, Parry measure and weak mixing, a special cylinder, polynomial/Garsia separation, and Rauzy fractals in an adelic representation space to claim onefold tiling and PDS for every irreducible Pisot substitution, with strong coincidence as a consequence (paper §§9–15, notably Proposition 5 and Theorem 6). Our shortest route uses proved bounded discrepancy, proved finite seed-patch exact overlap graphs, the **open** one-seed overlap-productivity premise (#84), proved coincidence-density implications and an audited imported PDS implication (Theorem 5.38). The aligned and strict-zipper components (#138/#139) remain open. See `docs/conjecture-ledger.md` and `docs/completion-ledger-2026-10-09.md`; the finite-domain box certificates are not universal closure.

## Specific proof-obligation defect: Proposition 5 (§13)

The paper defines \(\tau_2(x,\omega)\) as the **first simultaneous** hit of \(\mathcal C\times\mathcal C\) by \((T^n x,T^n\omega)\). Its §12 quantities \(s_j\), by contrast, partition first hits of **\(\omega\) alone** to \(\mathcal C\) along the selected times \(N_0,N_1,\ldots\). In §13 Proposition 5, immediately after equation (29), the proof asserts for every \(\omega\) in the chosen cylinder \(Z=\langle z_0\cdots z_{N_0}\rangle\) that
\[
\tau_2(x,\omega)=N_k\quad\Longleftrightarrow\quad
\text{the first hit of }T^{N_i}\omega\in\mathcal C\text{ is at }N_k.
\]
But its construction has \(T^{N_0}x\notin\mathcal C\) (cf. §12, equation (24)), while the set
\[
F=\{\omega\in Z:T^{N_0}\omega\in\mathcal C\}
\]
has positive Parry measure (the term explicitly subtracted in Proposition 5). Every \(\omega\in F\) has a second-coordinate first hit at \(N_0\) but **cannot** have a simultaneous hit there. For those points which later hit \(\mathcal C\times\mathcal C\), the claimed equivalence fails. Under the preceding simultaneous-recurrence Lemma 10 this is not merely an empty exceptional case. Thus the identity
\[
s_j-m(F)=\sum_{k=1}^{j}m\{\omega\in Z:\tau_2(x,\omega)=N_k\}
\]
is not established by the definitions and (29). Its use to contradict Proposition 4 consequently does not establish Proposition 5 as written. Verify whether a strengthened conditioning argument or corrected entrance-time decomposition can repair the step before drawing any final verdict about the full paper.

**Dependency boundary:** Proposition 5 supplies vanishing polynomial parts used in the subsequent proof of Theorem 6 (onefold Rauzy tiling), then the PDS and strong-coincidence conclusions. The above is a *specific unclosed argument*, not a mathematical counterexample to PSC or proof that no alternate argument exists.

## Exact corrected stopping-time partition (2026-10-14 continuation)

The first-entry objection can be made **exact**, without numerical estimates or assumptions about independence. This is a finite-union identity in the measurable space of §12.

Use precisely the paper's notation: let \(Z=\langle z_0\cdots z_{N_0}\rangle\), where \(T^{N_0}x\notin\mathcal C\) by (24), and let \(N_1<N_2<\cdots\) enumerate **all** visits of \(x\) to \(\mathcal C\) after \(N_0\). For \(k\ge0\), put

\[
E_k=Z\cap T^{-N_k}\mathcal C,\qquad
H_j=\bigcup_{k=1}^{j} E_k.
\]

The **second-coordinate-only** first-hit events in (25) are disjoint:

\[
F_0=E_0,\quad
F_k=E_k\setminus\bigcup_{i=0}^{k-1}E_i\ (k\ge1).
\]

Thus the §12 definition of \(s_j\), with no dynamical assumption beyond the definition, gives

\[
\boxed{s_j=\sum_{k=0}^j m(F_k)=m(E_0\cup H_j).} \tag{A}
\]

The **first simultaneous** hit events are instead

\[
J_k=E_k\setminus\bigcup_{i=1}^{k-1}E_i\quad(k\ge1).
\]

Because \(x\) misses \(\mathcal C\) at \(N_0\), the \(N_k\ (k\ge1)\) are all its later entry times, and (29) excludes joint entries earlier than \(N_1\) on \(Z\), one has

\[
J_k=\{\omega\in Z:\tau_2(x,\omega)=N_k\},
\qquad
\sum_{k=1}^j m(J_k)=m(H_j). \tag{B}
\]

If \(\tau_2=\infty\) on an exceptional set, (B) remains valid for every *finite* \(j\); Lemma 10 handles the almost-everywhere limit. Inclusion–exclusion applied to (A) and (B) now yields the **correct replacement** for the first equality of §13 Proposition 5:

\[
\boxed{
\sum_{k=1}^j m\{\omega\in Z:\tau_2(x,\omega)=N_k\}
=s_j-m(E_0)+m(E_0\cap H_j).
} \tag{C}
\]

The source omits the final term \(m(E_0\cap H_j)\). In its own construction \(z_{N_0}=I=(u_0:\emptyset)\) and §12's \(b(N_0)=1\) cylinder-count formula gives

\[
m(E_0)=\alpha^{-L}m(Z)>0. \tag{D}
\]

Moreover, by (23) \(Z\) lies in the chosen fibre \(\Delta_\epsilon(x)\); Lemma 10 / (21) says almost every \(\omega\in Z\) eventually enters \(\mathcal C\times\mathcal C\) with \(x\). Hence \(m(H_j)\uparrow m(Z)\), and therefore

\[
m(E_0\cap H_j)\uparrow m(E_0)>0. \tag{E}
\]

Combining (C)–(E) with Proposition 4's \(s_j\to m(Z)\) gives only

\[
m(Z)=m(Z)-m(E_0)+m(E_0);
\]

**the asserted contradiction disappears**, including in the limit. In fact the correction term is eventually strictly positive, and converges to exactly the mass subtracted by the paper.

An event-level negative control is already \(x\)'s indicator \((0,1,1)\) and \(\omega\)'s indicator \((1,0,1)\) at \((N_0,N_1,N_2)\): the first \(\omega\)-hit is \(N_0\), whereas the first joint hit is \(N_2\). This simple Boolean schedule is **not** asserted to be a concrete substitution-system witness; the positive-mass mismatch in the paper's actual fibre follows from (D)–(E) without one.

**Repair boundary.** Proposition 5 would require an *additional* argument showing that, in the hypothesized nonvanishing-polynomial scenario, the positive-mass early-hit set cannot undergo subsequent joint returns (for example, \(m(E_0\cap H_\infty)=0\)). That is not a consequence of ordinary weak mixing: the paper's Lemma 10 implies the opposite under the standing fibre construction. A plausible alternative must establish a new **hypothesis-dependent algebraic obstruction** to those returns, or bypass this subtraction entirely. Neither repair is supplied here. This result refutes the displayed event identification, **not** the general PSC, nor the abstract validity of the Garsia and geometric ingredients separately.

## Additional independent calibration and repair criterion (2026-10-14)

The earlier set-theoretic correction stands. The following uses an actual primitive mixing SFT to rule out a generic weak-mixing repair and checks the separate algebraic requirements against Theorem 3.

### Primitive mixing SFT countercalibration (preserved from the original PR #261)

Use the one-sided full binary shift with fair Bernoulli (Parry) measure,
\(\mathcal C=[11]\), \(Z=[1]\), \(N_0=0\), and
\(x=0(110)^\infty\). All later \(x\)-entry times are
\(N_k=1+3(k-1)\). There is no joint hit through \(N_0\).
Let \(p(E)=m(E)/m(Z)\); the following table uses \(p\), not \(m\).

| \(j\) | \(s_j/m(Z)\) | \(p(A_0)\) | \(p(H_j)\) | \(p(A_0\cap H_j)\) | printed \(s_j/m(Z)-p(A_0)\) |
| --- | --- | --- | --- | --- | --- |
| 1 | 1/2 | 1/2 | 1/4 | 1/4 | 0 |
| 2 | 5/8 | 1/2 | 7/16 | 5/16 | 1/8 |
| 3 | 23/32 | 1/2 | 37/64 | 23/64 | 7/32 |

For example, the subcylinder \([111]\subset Z\) has second-coordinate first
entry at zero and joint first entry at one. Its conditional mass is \(1/4\).
This is not a null-set discrepancy. For \(k\geq2\), the candidate two-symbol
blocks are mutually disjoint and independent, with hit probability \(1/4\).
The probability of avoiding \(r\) such blocks is \((3/4)^r\to0\);
the same tail argument proves infinitely many joint hits almost surely.
In particular, the early-hit group also eventually hits jointly.

Closed forms for \(j\geq1\) independently replay the table and the limit:
\[
 p(H_j)=1-(3/4)^j,\quad
 p(A_0\cap H_j)=1/2-(1/4)(3/4)^{j-1},\quad
 s_j/m(Z)=1-(1/2)(3/4)^{j-1}.
\]
The full shift is mixing, but the fixed \(x\) is periodic; recurrence here
is proved explicitly, not inferred by applying Fubini to an arbitrary \(x\).
This control tests the event equivalence with an overlapping cylinder.
It is **not** a Pisot substitution/Rauzy counterexample, does not realize the
paper's geometric construction or numerical size constraints, and tests
no polynomial-cancellation conclusion.

Exact scratch calibration on October 14 enumerated every fair binary tail
through coordinate \(N_j+1\), conditional on coordinate zero being 1:
4, 32 and 256 tails for \(j=1,2,3\). Integer counts divided by those
denominators reproduce every table entry. A separate Boolean check enumerated
all 1,020 membership patterns for \(A_0,\ldots,A_j\), \(1\leq j\leq8\),
checking the disjoint partitions and inclusion-exclusion identity. No random
sampling, capped search, floating arithmetic, or infinite-limit simulation
was used. These are auxiliary finite checks of a directly proved identity,
not a canonical research-code certificate; the definitions and closed forms
above provide a replayable basis without a new Python-only kernel.

### Removing the early-event set does not resurrect the contradiction

On \(Z'=Z\setminus E_0\), the first second-coordinate time and first joint time agree, but both cumulative distributions converge to \(m(Z')=m(Z)-m(E_0)\). Their normalized conditional distributions both converge to one. Conversely, requiring \(m(E_0\cap H_\infty)=0\) directly contradicts the selected recurrent fiber together with \(m(E_0)>0\); this is a source-level contradiction, not a rate-of-mixing consideration.


### Theorem 3 transfer audit: two independent missing bridges

A corrected stopping-time identity alone does not rescue Proposition 5. More significantly, Theorem 3 in §10 **claims** (subject to the Definition 9 radius mismatch audited below) that, **for a particular pair that simultaneously enters the special cylinder at time d**, nonzero polynomial part implies failure of membership in the shrinking adelic neighborhood at level d+1. Equivalently,

\[
\big((T^d x,T^d\omega)\in\mathcal C\times\mathcal C\big)
\ \wedge\ \big(\Psi(\omega)+\gamma\in O_{d+1}(\Psi(x))\big)
\quad\Longrightarrow\quad F_d(x,\omega;\gamma)=0. \tag{F}
\]

There are two separate, unproved transfers in any attempt to use (F) to contradict the recurrence of a **positive-measure** cylinder.

1. **Quantifier/support bridge.** The contradiction assumption of Proposition 5 concerns the selected pair (x,y). It does not say that the polynomial parts are nonzero for almost every other \(\omega\) in the cylinder \(Z\). At each *fixed* time d, the polynomial part depends on finitely many prefix-suffix symbols, and may be locally constant on a sufficiently refined cylinder. But the intersection of such cylinders over **all** d can have zero Parry measure: in the fair binary shift, the decreasing cylinders \([0^d]\) all have positive measure \(2^{-d}\), while their intersection is the measure-zero singleton \(0^\infty\). A proof needs to construct a positive-measure family on which the relevant nonvanishing is preserved, or derive another measure-level algebraic obstruction. Single-pair information alone is insufficient.
2. **Shrinking-scale bridge.** Equation (23) supplies only the *fixed* neighborhood condition \(\Psi(Z)+\gamma\subset B(\Psi(x),\epsilon)\). Theorem 3 requires the **time-dependent smaller** condition \(\Psi(\omega)+\gamma\in O_{d+1}(\Psi(x))\) at the same d as a joint cylinder hit. Definition 9 makes the radii of these neighborhoods decay in the contracting places as d increases. For late \(N_k>N_0\), membership in the fixed ball does not imply membership in \(O_{N_k+1}\). The argument for ruling out early returns of (x,y) therefore cannot be promoted to late returns of arbitrary (x,\omega).

**Positive-measure return-exclusion lemma (conditional, elementary).** Suppose \(Z\) is measurable with \(m(Z)>0\) and, as in the paper's selected recurrent fiber, \(m(Z\setminus H_\infty)=0\). Suppose a measurable \(U\subset Z\) has \(m(U)>0\) and for almost every \(\omega\in U\), **every** joint visit at an \(N_k\) satisfies both shrinking-neighborhood membership and nonvanishing polynomial part at that time. Then (F) rules out every such visit for almost every point in U, so \(m(U\cap H_\infty)=0\), while recurrence gives \(m(U\cap H_\infty)=m(U)>0\), a contradiction. The proof uses countability of the visits and the measure-zero exceptional set; it uses no independence. **This is a valid conditional proof template, not a completed construction of U.**

The obligations are therefore explicit: (i) derive a positive-measure, algebraically controlled support set from the assumed nonvanishing *at the selected pair*, and (ii) prove appropriate shrinking-scale control at the **same** joint-return times. Source §§8–10 only show geometric perturbation into a fixed ball and separation conditional on a shrinking neighborhood; they do not establish (i) or (ii) for all later returns. A hypothetical repair must also map an algebraic cancellation obtained on a perturbed pair back to the **fixed realized, occurrence-labelled affine offset** of #139, retaining non-unit finite-place coordinates. An ordinary SFT product pair is not automatically a valid edge/witness in our seed-patch overlap graph.

This separates three checkable steps instead of calling weak mixing a coincidence theorem: positive-measure algebraic support, scale-matched cylinder return, and occurrence-compatible exact projection. Failure of any step blocks the proposed transfer; satisfying the steps would give a genuine new avenue. No universal claim status changes.

## Theorem 3 radius and pointwise address audit (2026-10-14 continuation)

**Decision: redirect.** The printed Theorem 3 cannot be imported as stated without a separate repair to Definition 9. A narrower **exact-diagonal, synchronized-address** implication survives the radius problem and yields an integer prefix relation. It is conditional on the paper's Garsia/tail argument; the step from that relation to the repository's #139 target remains open. This is a targeted primary-source calculation, not a new PSC theorem or complete audit of the preprint.

### Independent source-level radius mismatch

Let \(n\ge2\) be the alphabet size/degree, \(d\ge1\) a joint cylinder-visit time, and
\[
c=(1-\alpha^{-1})/M,\qquad 0<c<1,
\]
with \(M\ge1\) the positive integer-coefficient bound in §10. For a non-dominant Archimedean place \(v\), **Definition 9** (PDF p. 16) assigns to \(O_{d+1}(X)\) the radius
\[
R_v^{\mathrm{def}}(d+1)
=|\alpha_v|^{d+n-1}c^{1/d}.
\tag{R-def}
\]
But **Theorem 3's proof equation (16)** (PDF p. 17), and the subsequent bound on PDF p. 18, require
\[
|X_v-Y_v|<
R_v^{\mathrm{proof}}(d+1)
=|\alpha_v|^{d+n-1}c^{1/(n-1)}.
\tag{R-proof}
\]
When \(d\ge n\), \(1/d<1/(n-1)\), hence
\[
R_v^{\mathrm{proof}}(d+1)<R_v^{\mathrm{def}}(d+1).
\]
Membership in the **larger printed neighborhood** does not imply the stricter inequality (16) used in the proof. When \(d=n-1\), the exponents agree; for \(1\le d<n-1\), the printed Archimedean radius is smaller. At \(d=0\), Theorem 3 invokes \(O_1\), whose printed Definition 9 exponent \(1/(1-1)\) is undefined. Both mismatches are visible in the source's own formulas; they are not consequences of numerical approximations or a choice of norm.

A **candidate repaired statement**, with no claim that all other proof steps have been independently verified, uses \(\widetilde O_{d+1}\) defined by (R-proof) at every non-dominant Archimedean place and the **same finite-place factors** as the source's \(O_{d+1}\). Definition 8's condition on \(L\) also uses exponent \(1/(n-1)\), consistent with that narrower statement. Simply changing the theorem's words without changing the neighborhood is not a repair. The unresolved \(d=0\) case must be handled separately if used.

### Shrinking-target limsup lemma (proved, no ergodic assumption)

Fix \(x\), \(\gamma\), and put \(X=\Psi(x)\). For each \(d\ge1\) define
\[
Q_d(x)=\{\omega:\ (T^d x,T^d\omega)\in\mathcal C^2,\
   \Psi(\omega)+\gamma\in\widetilde O_{d+1}(X)\}.
\]
Every Archimedean radius in \(\widetilde O_{d+1}\) tends to zero because \(0<|\alpha_v|<1\); the source's finite-place radii also tend to zero. (The same holds for the printed \(O_{d+1}\).) Hence
\[
\boxed{\limsup_{d\to\infty}Q_d(x)
  \ \subseteq\
  \{\omega:\Psi(\omega)+\gamma=\Psi(x)\}.}
\tag{ST}
\]
**Proof.** If a fixed \(\omega\) lies in infinitely many \(Q_d\), the *fixed* distance of \(\Psi(\omega)+\gamma\) from \(X\) in each selected local field is smaller than radii tending to zero along unbounded \(d\). All local coordinates therefore agree. The symbolic visit restriction can only shrink the limsup. No independence, weak mixing, Borel–Cantelli estimate or singleton-fibre assumption is needed. ∎

If additionally \(m\{\omega:\Psi(\omega)+\gamma=X\}=0\), then \(m(\limsup Q_d(x))=0\). This zero-atom condition must be proved for the selected \(x\), not presumed from \(m\times m\) recurrence; §8 *asserts* a product-measure-zero exact diagonal, which can imply a zero fibre for almost every first coordinate via Fubini, but not for every preselected \(x\).

**Consequence.** Product weak mixing can give infinitely many joint cylinder visits for almost every pair. It **cannot** thereby give infinitely many joint visits inside the shrinking \(O_{d+1}\) for a positive-measure set of *nonexact* image pairs. The positive-measure repair template above must target a **finite scale-matched visit** under additional algebraic hypotheses, or avoid the measure perturbation and work on an exact diagonal. This is a separate no-go constraint on the proposed method, not a claim that a finite scale-matched visit is impossible.

### Exact-diagonal polynomial cancellation (conditional source salvage)

Let \(\sigma\) be primitive with irreducible incidence characteristic polynomial, \(M_\sigma=M\), Perron root \(\alpha\), and a positive left eigenvector \(v\) satisfying \(M^{\mathsf T}v=\alpha v\). For a legal prefix-suffix path
\[
x=((a_{k+1}:p_k a_k s_k))_{k\ge0},\quad
y=((b_{k+1}:q_k b_k t_k))_{k\ge0},
\]
let \(\pi\) be the integer Parikh vector and fix \(w\in\mathbb Z^n\), with \(\gamma=\Phi'(\langle w,v\rangle)\). Suppose **the fixed pair is exactly coincident in the full adelic representation**
\[
\Psi(x)=\Psi(y)+\gamma
\tag{D}
\]
and at some **finite** \(d\ge1\), \(T^d x,T^d y\in\mathcal C\). Then, provided the Garsia lower bound (Lemma 9) and the synchronized special-cylinder tail estimates (18)–(19) are valid as used in the source, the polynomial part at this \(d\) vanishes:
\[
F_d(\alpha)=
\sum_{k=0}^{d-1}\alpha^k
 \langle\pi(p_k)-\pi(q_k),v\rangle-\langle w,v\rangle=0.
\tag{P}
\]

**Why the radius typo does not affect this conditional statement.** By (D), \(X_v-Y_v=0\) in **every** local component, so the *strict* bound (16) used inside the proof is automatically true, regardless of whether Definition 9 gives an overly large neighborhood. The remaining source estimates and Garsia inequality, if sound, give the same contradiction for nonzero \(F_d\). This does **not** validate Theorem 3 for general \(Y\in O_{d+1}(X)\).

**Spectral injectivity (proved algebraically).** The \(\mathbb Q\)-linear functional \(L:\mathbb Q^n\to\mathbb R,\ z\mapsto\langle z,v\rangle\) is injective. Indeed
\[
L(Mz)=\alpha L(z),
\]
so \(\ker L\) is an \(M\)-invariant rational subspace. Irreducibility of the characteristic polynomial rules out any nonzero proper invariant rational subspace, while \(L\ne0\), so \(\ker L=0\). Applying this to (P) yields the **integer** address certificate
\[
\boxed{\sum_{k=0}^{d-1}M^k\bigl(\pi(p_k)-\pi(q_k)\bigr)=w.}
\tag{I}
\]
No division by eigenvector coordinates and no floating-point recognition of zero occurs.

**Prefix-path interpretation (proved combinatorially).** By \(\sigma(a_{k+1})=p_k a_k s_k\), induction gives
\[
U_d(x)=\sigma^{d-1}(p_{d-1})\cdots\sigma(p_1)\,p_0
\quad\prec\quad \sigma^d(a_d),
\quad
\pi(U_d(x))=\sum_{k<d}M^k\pi(p_k),
\tag{A}
\]
and similarly for \(y\). These are **occurrence-labelled** proper prefixes, even when two labels have the same Parikh vector. Thus (I) witnesses
\[
w\in P_d(a_d)-P_d(b_d).
\tag{U}
\]
For the paper's special cylinder, both depth-\(d\) symbols are \(I=(u_0:\emptyset)\); the source therefore gives \(a_d=b_d=u_0\) at that visit, so (U) is in particular a **same-ancestor-letter** prefix-difference relation.

**Ordered-word calibration.** For the Tribonacci substitution \(\sigma(a)=ab,\ \sigma(b)=ac,\ \sigma(c)=a\), take a legal length-two ancestry \(a_2=a\to a_1=b\to a_0=c\) with \(p_1=a,\ p_0=a\). The actual parent word is \(\sigma^2(a)=abac\), and (A) yields \(U_2=\sigma(a)a=aba\), a proper prefix immediately before the \(c\). Reversing the concatenation to \(p_0\sigma(p_1)=aab\) gives a word that is **not** a prefix of \(abac\), even though its Parikh vector is identical. Thus word order and the occurrence identifier are essential when transporting an algebraic equality into #139's ordered graph. This verifies a nontrivial two-level special case of (A), not a new completeness result.

### Why this is not yet #139 — exact scaling and realization firewall

The repository's strict-zipper acceptance predicate is
\[
\boxed{M^m w_{\mathrm{PSC}}\in P_m(i)-P_m(j)}
\quad\text{with occurrence-compatible replay from a *fixed realized* }(i,j,w_{\mathrm{PSC}}).
\tag{H}
\]
Source (U) has **unscaled** \(w\), ancestor letters \(a_d,b_d\) (both \(u_0\) at a synchronized special-cylinder visit), and no seed-patch realization proof. To infer (H) at \(m=d\) would require an explicit verified bridge fixing at least:
(i) \(w=M^d w_{\mathrm{PSC}}\) in consistent incidence/offset coordinates;
(ii) the target letters and their orientation/collaring; and
(iii) the occurrence-labelled pair as an actual path in the exact overlap graph.
None follows from weak mixing, (D), or polynomial cancellation alone.

Small exact **algebraic** negative control for the common scaling mistake (not a source-Theorem-3 or PSC counterexample): for Fibonacci \(\sigma(a)=ab,\sigma(b)=a\),
\[
M=\begin{pmatrix}1&1\\1&0\end{pmatrix},\quad
P_1(a)-P_1(b)=\{(0,0),(1,0)\}.
\]
The unscaled \(w=(1,0)\) is in that set, whereas \(Mw=(1,1)\) is not. Hence \(w\in D_m\not\Rightarrow M^m w\in D_m\), even in a unimodular primitive irreducible Pisot example. In the actual source's synchronized \(I\)-cylinder, the ancestor-letter restriction is **another** obstruction to equating (U) with a requested cross-letter (H).

### Next precise research obligation

**Diagonal-compatible ancestry recurrence (OPEN, not a new claim in the proof ledger):** starting from a *realized* bad strict-zipper state, find a pair of legal address sequences with (a) exact adelic coincidence, (b) an actual simultaneous special-cylinder visit, and (c) an **explicit commuting diagram** from their labelled length-\(d\) prefixes and source offset \(w\) to the prescribed target \(M^d w_{\mathrm{PSC}}\) and endpoint types. Alternatively, avoid the special \(I\)-cylinder and establish the same exact witness with an occurrence-compatible different-cylinder construction.

This is deliberately narrower and more checkable than claiming ordinary product mixing forces coincidence. First attempt an exact symbolic/algebraic bridge using the already available occurrence-labelled prefix and affine replay contracts in `docs/p1b-adelic-prefix-difference-cylinder-2026-09-21.md`; a test is warranted only after such a bridge is *stated*, with the known determinant-two pump and non-unit finite-place regression as negative controls. Do not turn a failure to find a witness at bounded depth into a mathematical negative verdict. General #84/#138/#139, G1, and PSC remain OPEN.

## Transfer to #139: exact hitting is the gate

The paper's proposed mechanism is geometric overlap → symbolic positive-measure pair set → mixing/recurrence to special cylinders → Garsia/polynomial cancellation → geometric coincidence. Our exact target is
\[
\exists m\ge0:\quad M^m w\in P_m(i)-P_m(j)
\]
for an **occurrence-compatible** prefix-pair witness of a realized strict-zipper overlap (see `docs/p1b-adelic-prefix-difference-cylinder-2026-09-21.md`). For non-units the full adelic internal space includes finite places; approximate closeness, positive measure, and generic recurrence do **not** imply exact membership. Any imported mixing lemma must preserve the *ordered realized overlap* relation and its first-hit conditioning, and supply an exact algebraic witness—never infer a hit from density alone.

### Narrow next obligation (stop/go before new executable work)

1. **Completed as an audit of the invalid inference, not as a PSC theorem:** the disjoint partitions, corrected intersection term, and primitive mixing-SFT countercalibration rule out the printed deficit argument. Any replacement must establish a positive-measure algebraically controlled support set and shrinking-scale membership at actual joint-return times (Theorem 3 transfer audit above).
2. **Partially resolved only under new explicit hypotheses:** synchronized **exact-diagonal** source addresses give an unscaled integral prefix certificate, conditional on the source's Garsia/tail estimates (and subject to the Definition 9 radius mismatch for general neighborhoods). A source-to-#139 scaled-offset, endpoint-type, occurrence-labelled **realization bridge remains OPEN**, especially in the non-unimodular adelic regime.
3. Only if a proof-complete new implication survives, write a precise theorem with a replayable small specimen/counter-calibration before Mojo-first implementation; independently audit imports. Do not promote this note to PSC evidence.

## Source and status caution

The source is arXiv **v1**. Existing repository source audit (`manuscripts/PSC_PROOF_next_source_audit.tex` and `docs/audit-2026-09-27.md`) already lists Nakaishi as an adjacent *claimed* proof, not an imported theorem. This note sharpens that classification with a testable Proposition 5 objection. Treat the objection as a manuscript-level audit finding pending a formal response, not as a published erratum. All authoritative statuses remain unchanged.
