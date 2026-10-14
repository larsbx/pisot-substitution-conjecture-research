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

## Transfer to #139: exact hitting is the gate

The paper's proposed mechanism is geometric overlap → symbolic positive-measure pair set → mixing/recurrence to special cylinders → Garsia/polynomial cancellation → geometric coincidence. Our exact target is
\[
\exists m\ge0:\quad M^m w\in P_m(i)-P_m(j)
\]
for an **occurrence-compatible** prefix-pair witness of a realized strict-zipper overlap (see `docs/p1b-adelic-prefix-difference-cylinder-2026-09-21.md`). For non-units the full adelic internal space includes finite places; approximate closeness, positive measure, and generic recurrence do **not** imply exact membership. Any imported mixing lemma must preserve the *ordered realized overlap* relation and its first-hit conditioning, and supply an exact algebraic witness—never infer a hit from density alone.

### Narrow next obligation (stop/go before new executable work)

1. Write disjoint measurable stopping-time events for the first \(\omega\)-hit along \(N_i\) and first **joint** hit, explicitly conditioning out early \(\omega\)-only hits; either repair Proposition 5 or produce a concrete symbolic negative control.
2. Separately test whether its special-cylinder polynomial/Garsia separation gives an **exact, occurrence-compatible** witness for the affine replay offsets in #139. Identify every hypothesis, especially non-unimodular finite places and the measure/pair-support assumptions.
3. Only if a proof-complete new implication survives, write a precise theorem with a replayable small specimen/counter-calibration before Mojo-first implementation; independently audit imports. Do not promote this note to PSC evidence.

## Source and status caution

The source is arXiv **v1**. Existing repository source audit (`manuscripts/PSC_PROOF_next_source_audit.tex` and `docs/audit-2026-09-27.md`) already lists Nakaishi as an adjacent *claimed* proof, not an imported theorem. This note sharpens that classification with a testable Proposition 5 objection. Treat the objection as a manuscript-level audit finding pending a formal response, not as a published erratum. All authoritative statuses remain unchanged.
