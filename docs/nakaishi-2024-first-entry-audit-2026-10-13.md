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

## Transfer to #139: exact hitting is the gate

The paper's proposed mechanism is geometric overlap → symbolic positive-measure pair set → mixing/recurrence to special cylinders → Garsia/polynomial cancellation → geometric coincidence. Our exact target is
\[
\exists m\ge0:\quad M^m w\in P_m(i)-P_m(j)
\]
for an **occurrence-compatible** prefix-pair witness of a realized strict-zipper overlap (see `docs/p1b-adelic-prefix-difference-cylinder-2026-09-21.md`). For non-units the full adelic internal space includes finite places; approximate closeness, positive measure, and generic recurrence do **not** imply exact membership. Any imported mixing lemma must preserve the *ordered realized overlap* relation and its first-hit conditioning, and supply an exact algebraic witness—never infer a hit from density alone.

### Narrow next obligation (stop/go before new executable work)

1. Completed at the event-accounting level in the October 14 derivation below: the corrected identity removes the proposed contradiction. Seek an additional geometric/algebraic implication rather than repeat the subtraction argument.
2. Separately test whether its special-cylinder polynomial/Garsia separation gives an **exact, occurrence-compatible** witness for the affine replay offsets in #139. Identify every hypothesis, especially non-unimodular finite places and the measure/pair-support assumptions.
3. Only if a proof-complete new implication survives, write a precise theorem with a replayable small specimen/counter-calibration before Mojo-first implementation; independently audit imports. Do not promote this note to PSC evidence.

## October 14 follow-up: exact partition and loss of the contradiction

**Disposition:** proceed with this narrowed source audit; stop the positive-deficit
argument. This is a direct set-theoretic derivation from the paper's definitions,
not a new universal diagnostic or a promotion of a PSC lemma. The prior
October 13 stop/go obligation is resolved only for stopping-time accounting.
No executable research kernel is introduced.

### Hypotheses and conditioning checked against §§11–13

Write \(D_x=(\Psi+\gamma)^{-1}B(\Psi(x),\epsilon)\) and
\(Z=\langle z_0\cdots z_{N_0}\rangle\). All measures below are the
**unnormalized Parry measure** \(m\), restricted to subsets of \(Z\).

- §11 defines \(\tau_2\) over all integer times, with infinity allowed.
  Product ergodicity alone gives recurrence for product-almost every pair,
  **not for every prescribed first coordinate**. Lemma 10 uses Fubini to
  obtain recurrent fibers for almost every first coordinate.
- §12 explicitly selects such a good \(x\), with the additional recurrence
  property (21). Equation (23) gives \(Z\subset D_x\). Thus the fiber-null
  exceptional set remains null in \(Z\), and in every measurable subset of
  \(Z\), including the early-hit event. This uses inclusion, not independence
  of the two coordinates or invariance of a conditioned measure.
- Equation (24) excludes an \(x\)-hit at \(N_0\). The sequence
  \(N_1<N_2<\cdots\) lists **all** subsequent \(x\)-entry times.
- Under Proposition 5's contradiction assumption, the paragraph leading to
  (29) excludes joint hits through \(N_0\) throughout \(Z\).
  We grant that exclusion for this audit; we do not certify its geometric
  derivation or Theorem 3. Together with the preceding items it identifies
  finite joint first hits with the listed later times, almost everywhere.
  The finite partition identities below do not themselves require recurrence.

### Disjoint events

For \(k\geq0\), define raw hit events
\[
 A_k=Z\cap T^{-N_k}\mathcal C,\qquad H_j=\bigcup_{k=1}^j A_k.
\]
Here \(A_k\) means a hit **at** \(N_k\), not a first hit. Define
\[
 F_0=A_0,\qquad
 F_k=A_k\setminus\bigcup_{i=0}^{k-1}A_i\quad(k\geq1),
 \qquad
 G_k=A_k\setminus\bigcup_{i=1}^{k-1}A_i\quad(k\geq1).
\]
These are measurable finite Boolean combinations of cylinders. Each family
is pairwise disjoint. By §12 equation (25) and the definition of \(s_j\),
\[
 \bigsqcup_{k=0}^jF_k=A_0\cup H_j,\qquad
 s_j=m(A_0\cup H_j).
\]
Under the no-earlier-joint-hit condition, \(G_k\) is precisely
\(\{\omega\in Z:\tau_2(x,\omega)=N_k\}\); there is no \(A_0\) exclusion.
Moreover,
\[
 G_k=F_k\sqcup(A_0\cap G_k),\qquad
 \bigsqcup_{k=1}^jG_k=H_j.
\]
Consequently the corrected finite identity is
\[
 \boxed{\sum_{k=1}^j m\{\omega\in Z:\tau_2(x,\omega)=N_k\}
 =m(H_j)=s_j-m(A_0)+m(A_0\cap H_j).}
\]
Equivalently, the expression printed in Proposition 5 is
\(s_j-m(A_0)=m(H_j\setminus A_0)\). Its error is exactly
\(m(A_0\cap H_j)\), with a nonnegative sign.

### Limit and attempted conditioning repair

Let \(H_\infty=\bigcup_{k\geq1}A_k\). Continuity from below for the
finite measure \(m\) gives, even without recurrence,
\[
 \lim_jm(H_j)=m(H_\infty),\quad
 \lim_jm(A_0\cap H_j)=m(A_0\cap H_\infty),\quad
 s_\infty=m(A_0\cup H_\infty).
\]
The selected good fiber and (23), together with the no-earlier-hit
condition, imply \(m(Z\setminus H_\infty)=0\). Hence
\[
 m(H_j)\longrightarrow m(Z),\qquad
 m(A_0\cap H_j)\longrightarrow m(A_0),\qquad
 s_\infty=m(Z).
\]
The last equality agrees with Proposition 4; this argument does not audit
Proposition 4's separate matrix/counting proof. Section 12 gives
\(m(A_0)=\alpha^{-L}m(Z)>0\) (its \(b(N_0)=1\) cylinder computation).
The purported persistent deficit is therefore canceled completely.

Restricting to \(Z'=Z\setminus A_0\) repairs the first-hit equivalence on
that restricted set, but both cumulative masses then converge to
\(m(Z')=m(Z)-m(A_0)\), again with no contradiction. A normalized conditional
measure gives limit one on both sides. Conversely, forcing
\(m(A_0\cap H_\infty)=0\) would conflict with the paper's recurrent-fiber
hypothesis and \(m(A_0)>0\). Recurrence also ensures that the omitted term
is positive at some finite \(j\); it need not be positive for every \(j\).

Thus the accounting can be repaired, but that repair **does not prove
Proposition 5**: its proposed contradiction disappears. A proof of polynomial
cancellation needs a further implication or a different argument. This
does not establish that no such repair or alternative proof is possible.

### Small symbolic negative control and exact checks

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

### Boundary retained

The defect in Proposition 5's event equivalence and its resulting deficit
argument is established by the stated definitions and hypotheses. The
polynomial-cancellation claim, Theorem 6 and downstream universal conclusions
are not thereby verified. No new import, claim status, dependency edge or
independent-human-review label is granted. General PSC and the repository's
open productivity/exact-hitting obligations remain unresolved.

## Source and status caution

The source is arXiv **v1**. Existing repository source audit (`manuscripts/PSC_PROOF_next_source_audit.tex` and `docs/audit-2026-09-27.md`) already lists Nakaishi as an adjacent *claimed* proof, not an imported theorem. This note sharpens that classification with a testable Proposition 5 objection. Treat the objection as a manuscript-level audit finding pending a formal response, not as a published erratum. All authoritative statuses remain unchanged.
