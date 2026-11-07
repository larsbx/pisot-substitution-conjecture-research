# R1F — finite-field obstruction for mixed-sign ancestry cycles (2026-11-07)

**Parent:** R1 [PR #507] from exact accepted head `5dca984578ab155bb0e36369a90d21bc097f5704`. **Scope:** independent nested branch, not a replacement for R1's sign-conditional obstruction. **Status:** proposed certificate interface and bounded adversarial model; no strict-PIP closure.

## Work shown

### Assumptions and hypotheses

Let `M` be a primitive irreducible Pisot incidence matrix and consider a **supplied actual ordered occurrence cycle** of length `k`, with a verified correction word `c_0,...,c_(k-1)` extracted from literal child occurrences. Periodicity gives the exact **integral** equation

```
(I - M^k) x_0 = Σ_(j=0)^(k-1) M^(k-1-j) c_j.
```

This identity makes no sign assumption. A prime `p`, a finite-field left-null functional of the reduction of `I-M^k`, and a *nonzero* pairing with the reduced correction sum provide a negative certificate for that **specific** cycle. The occurrence cycle, source labels, correction digits and canonical residue map must be checked separately.

### Derivation / reduction

Over `F_p`, write `A=(I-M^k) mod p`, `b=(Σ M^j c_j) mod p`. If `qA=0` but `q b≠0`, then any solution `Ax=b` would give `0=qAx=qb≠0`, a contradiction. Because every integral solution reduces to a solution modulo `p`, the finite-field obstruction excludes an integral periodic cycle of the certified correction word.

The first Lean layer proves this **dual certificate soundness** over finite fields and a conditional integral-to-modular transport lemma. The exact matrix reduction and admissible cycle-word extraction are *not* yet built. Finite-field checks need no approximation or numerical eigenvalue isolation.

**Hypothesis firewall:** finding a few excluded cycles, or a finite-field obstruction for an unverified synthetic digit word, does not eliminate a universally quantified strict component. Coverage must be complete over all actual recurrent occurrence-indexed strict cycles or established by a separate uniform theorem.

### Evidence and replay

New standalone module `proof/psc_routes/R1Modular.lean`; finite-state negative-control model `proof/quint/PscR1Modular.qnt`; exact-head workflow `.github/workflows/psc-bprime-r1-modular.yml`. A passing Lean check must include every declared theorem in the fail-closed axiom audit, and the Quint command must execute a named deterministic test with a nonzero test count. CI remains pending until a hosted exact-commit receipt is observed.

Parent R1 already provides the exact affine correction identity and checked Tribonacci mixed-sign cycle arithmetic. This side route is an independent attempt to exclude **specific** mixed-sign correction cycles even when the R1 signed-height lemma cannot apply.

### Negative controls

For the toy congruence `0·x = 1 (mod 2)`, there is no residue solution, as a finite-field left-null witness certifies. This is **not** an actual substitution cycle. Conversely, a modulo-`p` solvable equation is *not* evidence that an integral cycle exists; a pass only means this particular modular obstruction did not rule it out. A budget exhausted with no witness must remain **unknown**.

The Tribonacci mixed-sign correction cycle is a required genuine PIP negative control: any proposed universal exclusion should *not* reject its actual literal three-step ancestry just because its scalar corrections change sign.

### Non-claims / remaining gaps

No new universal theorem about the Pisot Substitution Conjecture, C4, BH, A1′, prefix BPA termination, or geometric separation. No canonical Mojo cycle enumerator, complete cycle-domain certificate, occurrence-level refinement, or ledger promotion. Exact arithmetic implementation belongs in the repository's Mojo-first kernel after the formal contract is accepted.

### Targeted literature stop/go (automated research-design gate)

- **Sirvent–Solomyak (2002),** DOI 10.4153/CMB-2002-062-3, §§3–5: prefix BPA and half-coincidence/return mechanisms, not an integral congruence certificate for all ordered SCC corrections.
- **Adamczewski (2003),** *Balances for Fixed Points of Primitive Substitutions*: spectral discrepancy criteria for legal factor words, not complete modular enumeration of strict-source correction words.
- **Martensen (2004),** *A Generalized Balanced Pair Algorithm*, arXiv math/0309194: ordered balanced factors and algorithmic hypothesis boundaries; a generalized/reducible system cannot silently stand in for a PIP strict component.
- **In-repo canonical controls:** `docs/c4-pisot-ancestry-finiteness.md`, `docs/c4-prefix-difference-return-calculus.md` and R1's dedicated 2026-11-07 targeted literature check.

**Decision: PROCEED NARROWED as a certificate-mechanism experiment**, with no novelty claim for reduction modulo primes or the left-null contradiction. Independent human mathematical/originality review remains deferred until PSC closure; this small automated prior-art gate is complete for the scoped mechanism.

## 2026-11-07 adversarial correction: the realizability firewall

An important logical limitation is now made an explicit Lean theorem:
`realized_integer_cycle_cannot_be_modularly_obstructed`.

If an ancestry cycle is already **actually realized** by an integral defect
`x_0`, then the periodicity equation `(I−M^k)x_0=b` has the integral
solution `x_0`. Reduction of this actual solution modulo **every prime**
solves every faithfully reduced modular equation. Therefore there can be
**no valid left-null witness** `qA_p=0, q b_p≠0` for that observed cycle.

The correct research target is narrower: enumerate cycles in an **abstract
finite, decorated occurrence-state superset** that satisfy local transition
conditions but are not yet known to be realizable globally; use modular
inconsistency to reject those **candidate** cycles *before* claiming they
have integral ancestry realizations. If the decorated state already includes
a consistent integral defect and every edge enforces the exact affine
recurrence, an authentic closed cycle necessarily satisfies the equation,
and this particular modular filter gives no additional exclusion. Do not
run repeated mod-p searches against already verified physical cycles expecting
a contradiction; that would be a wasted or misleading research direction.

**Stop/go decision: REDIRECT.** The next independent obligation is to
identify a *necessary but incomplete* abstraction of strict component
occurrence cycles (e.g., permitted correction words with incomplete defect
bindings) and construct complete/sound lifting criteria. Modular certificates
can prune its false positives. This route alone cannot prove C4 unless an
independent theorem shows all hypothetical strict configurations would
generate a *nonrealizable abstract* cycle. Human review remains deferred.

**CI correction:** Quint 0.33.1 discovers tests whose names end in
`Test`. Previous run `42401212421` executed zero named tests because
`zeroResidueRejected` and `oneResidueRejected` lacked that suffix; its
test-count gate correctly failed. Both are now renamed with `Test`,
and the exact-head Lean audit requires four scoped declarations, including
the no-false-rejection theorem.

## 2026-11-07 — concrete Tribonacci parity obstruction and sharp countercontrol

**Formal one-period result.** For the *literal* Tribonacci substitution `0→01, 1→02, 2→0`, the integer incidence matrix is `M=[[1,1,1],[1,0,0],[0,1,0]]`. The exact proper-image-prefix correction alphabet is

`D = {−e₀, 0, +e₀}`.

The Lean route has explicit source-image definitions and incidence-column checking, and now attempts exhaustive Lean proof of every proper local prefix form. If `x = Mx + δe₀`, the 1st and 3rd integer rows imply `−2x₁=δ`. Therefore `δ` must be even. Since `δ∈{−1,0,+1}`, it follows `δ=0`, and invertibility of `I−M` implies `x=0`.

Thus **no nonzero period-one integral ancestry cycle is compatible even with the full local correction alphabet** of this concrete substitution. The exact mod-2 left-null witness corresponds to the sum of rows 0 and 2 of `I−M`; their coefficients cancel modulo 2, while the correction `e₀` does not. Both residue values of the original toy F₂ example and all four pairs of the concrete `x₁,x₂∈F₂` are now covered by deterministic Quint tests. These statements do not assert that any hypothetical strict component has a period-one recurrence or actual complete child words.

**Adversarial sharpness at period three.** The same true integer incidence has a *nonzero* 3-cycle using **locally admissible** proper-prefix corrections:

```
e₀ --(−e₀)--> e₁ --(−e₀)--> e₂ --(0)--> e₀
```

Each equality is an exact integer matrix action. Consequently, neither the entire local digit alphabet nor the Pisot/irreducible spectrum rules out *all* periodic nonzero ancestry. This refutes an overly strong proposal to close C4 using correction alphabets or modular inconsistency alone. The new Lean theorem checks the three vector equalities, while an independent Quint module is constructed to replay the exact 3-stage cycle.

**Consequence for closure research.** The genuinely new target must constrain **admissible concatenations of correction digits by literal ordered parent/child occurrence addresses and strict nonproductivity**, not just the finite set of possible local digits. In particular, whether the period-three arithmetic cycle can be realized by legal or illegal balanced-pair ancestry is **unresolved** by this abstract calculation. It must not be classified as a strict-PIP counterexample.

**Receipts:** New exact-head Lean/Quint checks remain required for the enlarged certificate inventory. The previous passing R1 parent (#507) does not accept these added declarations. No claim-ledger change or merge to main.

## 2026-11-07 — adversarial correction: prime-field certificate incompleteness

**Soundness is not completeness.** The left-null test `qA=0, qb≠0` over `F_p` is a valid *refutation* of a proposed integral cycle. But the absence of such a certificate for **every prime** does **not** mean the integral equation is solvable.

Exact counterexample: `4x=2` has no solution in `ℤ`. Modulo `2`, it becomes `0x=0` and has solutions; modulo any odd prime, `4` is invertible, so it also has solutions. Nevertheless, modulo the **prime power 4**, the equation `0x=2` has no solution. The Lean route separately verifies the integral contradiction, existence of mod-2 and mod-3 solutions, and absence of mod-4 solutions. A universal assertion over all primes is the standard field-invertibility argument, not claimed here as a kernel-checked statement.

**Implication for the automated research programme:** Use finite-field left-null certificates first as fast, independently checkable exclusions, but do **not** mark a correction cycle as integrally feasible merely because all prime-field checks pass. Exact integer Smith-normal-form divisibility or checked prime-power congruences are needed as a completeness fallback. Rational inversion when `I−M^k` is nonsingular can independently determine the unique candidate integral ancestry state, but itself requires exact-integrality validation.

The local Tribonacci k=1 contradiction and k=3 nonzero arithmetic cycle remain consistent with this correction. The k=3 witness is locally admissible, **not** established as an actual strict ordered occurrence. For PSC, a proof must additionally cover all source-compatible recurring cycles, not merely ones with a convenient mod-p obstruction.

**Status:** new adversarial Lean controls awaiting exact-head hosted acceptance; no R1F branch merge, no C4/BH/PSC ledger promotion. Independent human review remains post-closure.
