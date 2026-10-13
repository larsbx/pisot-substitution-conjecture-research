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

1. Write disjoint measurable stopping-time events for the first \(\omega\)-hit along \(N_i\) and first **joint** hit, explicitly conditioning out early \(\omega\)-only hits; either repair Proposition 5 or produce a concrete symbolic negative control.
2. Separately test whether its special-cylinder polynomial/Garsia separation gives an **exact, occurrence-compatible** witness for the affine replay offsets in #139. Identify every hypothesis, especially non-unimodular finite places and the measure/pair-support assumptions.
3. Only if a proof-complete new implication survives, write a precise theorem with a replayable small specimen/counter-calibration before Mojo-first implementation; independently audit imports. Do not promote this note to PSC evidence.

## Source and status caution

The source is arXiv **v1**. Existing repository source audit (`manuscripts/PSC_PROOF_next_source_audit.tex` and `docs/audit-2026-09-27.md`) already lists Nakaishi as an adjacent *claimed* proof, not an imported theorem. This note sharpens that classification with a testable Proposition 5 objection. Treat the objection as a manuscript-level audit finding pending a formal response, not as a published erratum. All authoritative statuses remain unchanged.
