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

## 2026-11-07 — Lean/Quint-first complete *conditional* integer membership gate

**Exact scope:** `proof/psc_routes/R1Smith.lean` now expresses a mathematically complete iff, not merely a sound modular refutation. For an arbitrary finite-rank integer cycle operator `A`, consider integer coordinate transforms `U,V` with explicit integer left/right inverses and a checked diagonalization `U(A(Vy))_i = d_i y_i`. Then

```
(∃ x ∈ ℤ^d, A x = b)  ↔  (∀ i, d_i divides (U b)_i).
```

The Lean theorem `diagonal_certificate_complete` derives both directions. Zero diagonal entries are allowed and force the transformed right-hand coordinate to vanish. The scope is **conditional on the supplied exact diagonalization and inverse laws**: this module does not compute a Smith normal form or prove a supplied matrix certificate correct. A future independent matrix certificate checker must verify those finite integer matrix equations and match `A=I−M^k` and `b=ΣM^j c_j` to an actual literal ordered occurrence cycle. The exact transform/inverse laws cannot be substituted with a floating approximation or an arbitrary claimed JSON receipt.

**Adversarial model:** `proof/quint/PscR1Smith.qnt` enumerates all four residues modulo 4 for the equation `4x=2`, checking that every residue fails modulo 4 even though each satisfies the reduction modulo 2. A separate module exhibits the valid modulo-3 residue `x=2`. This is the smallest useful negative control against treating “prime-field checks passed” as “integral cycle possible”. It is not a strict Pisot ancestry. CI `.github/workflows/psc-bprime-r1-smith.yml` demands a *separate* exact-head Lean axiom receipt for **five** new declarations and five nonempty deterministic Quint tests. The earlier R1F modular workflow remains independent.

**Decision:** proceed to *certificate generation and checking* only after these two machine-facing modules compile, while keeping R1F draft. Next mathematically significant obligations are (a) a verified finite integer matrix diagonal certificate independent of solver self-report, (b) genuine source-child occurrence indexing and raw orientation binding, and (c) exhaustive or uniformly justified cycle coverage. No PSC/C4/BH/A1′ status change. A targeted research-design prior-art stop/go is already recorded above; independent human mathematical review remains after PSC closure.

## 2026-11-07 — exact matrix diagonalization, full ancestry equivalence and independent Quint controls

The Lean-first development now includes `ancestryOrbit_unroll` and `ancestryOrbit_closed_iff_cycle_equation` over **arbitrary additive groups and homomorphisms**, without excluding mixed-sign correction words. Combining these with exact finite integer matrix transforms yields the conditional iff `ancestry_smith_cycle_criterion`: an integral defect-cycle for a *supplied correction word* exists exactly when every verified Smith diagonal coordinate divides its transformed forced-digit sum, assuming the matrix is proven to equal the cycle operator `I−M^k`.

**Importantly, a concrete unimodular Tribonacci Smith matrix is now supplied.** For the actual incidence `M=[[1,1,1],[1,0,0],[0,1,0]]`, the period-one operator `A=I−M` is represented by

```
A = [[ 0,-1,-1],[-1, 1, 0],[ 0,-1, 1]]
U = [[ 0,-1, 0],[-1, 0, 0],[-1, 0, 1]]
V = [[ 1, 1,-1],[ 0, 1,-1],[ 0, 0, 1]]
Uinv = [[0,-1,0],[-1,0,0],[0,-1,1]]
Vinv = [[1,-1,0],[0,1,1],[0,0,1]]
D = diag(1,1,2).
```

The Lean exact-declaration proofs of `Uinv U = I`, `V Vinv = I`, and `U A V = D` and the resulting **complete iff for arbitrary integer rhs** are staged in `proof/psc_routes/R1Smith.lean`. They explicitly avoid depending on the output of an opaque Smith implementation. For an `e0`-only correction, `U (δ e0)=(0,-δ,-δ)`, so the nontrivial divisibility gate is precisely `2|δ`, reconciling the earlier direct period-one parity exclusion. This statement is about periodic integral ancestry, not yet an occurrence-compatible strict BPA cycle.

`proof/quint/PscR1Smith.qnt` has independent, *named* deterministic tests for all four residues modulo 4, the mod-3 false-acceptance case, and the three signed basis/one negative-vector witnesses for the exact matrix identity, now four matrix tests in total. These checks supplement, but do not replace, the universal Lean matrix equality. The dedicated `.github/workflows/psc-bprime-r1-smith.yml` requires **13** fail-closed Lean axiom receipts and **nine** executed Quint tests across three independently selected modules, with HEAD pinned.

**Gate:** Latest-head hosted acceptance is not yet established. The formal result remains a *complete conditional integer membership criterion*, not a complete enumeration of source-valid strict ancestry cycles or PSC closure. The next task is to verify canonical exact integer matrices for general `I−M^k`, and bind every candidate digit to raw ordered source-prefix addresses.

## 2026-11-07 — exact-source acceptance inventory (corrected)

This R1F branch now has **32 standalone Lean theorem declarations**: 18 in `R1Modular.lean` and 14 in `R1Smith.lean`. Both modules maintain explicit, exhaustive declaration-name axiom inventories; the original Codex finding that only four R1Modular declarations were audited was fixed rather than bypassed. The exact-head workflows reject `sorryAx`, compilation failures, missing named declarations, and receipt-count mismatches.

There are **23 named deterministic Quint tests** in two independently verified model files, split over eight explicitly selected `--main` modules: 11 in `PscR1Modular.qnt` (two toy F₂ residues, four concrete Tribonacci F₂ residues, one period-three nonzero arithmetic cycle, and four literal proper-prefix controls), plus 12 in `PscR1Smith.qnt` (four mod-4 residues, one mod-3 accepting control, four signed Smith-diagonal matrix vectors, and all three period-one local digits). Workflows require the **exact observed passing test count** per module rather than interpreting an empty successful invocation as acceptance.

The **canonical source-prefix control** uses the literal image lengths `|σ(0)|=2, |σ(1)|=2, |σ(2)|=1`, requiring each local offset to be **strictly less** than its source image length. The separate `rejectNonproperPrefixTest` deliberately chooses `σ(2)` with offset one and verifies rejection; this prevents the false generalization that every locally chosen `[0]` prefix is *proper* for every source letter.

The new complete conditional integer certificate includes an explicit integral inverse pair `Uinv U=I`, `V Vinv=I`, the exact matrix equality `U(I−M)V=diag(1,1,2)`, and a universal signed ancestry closed-cycle iff theorem. These are scoped to the linear-algebra and supplied-digit interface. **No occurrence-compatible strict SCC or general Pisot contradiction has been supplied.** Current exact-head hosted CI is pending; no new assertions are promoted before receipt inspection.

## 2026-11-07 — additional Lean/Quint adversarial split: proper-cut germs versus irreducible parents

**New exact local observation.** For actual source prefix words `P_t,P_b` and a following bottom source letter `b`, assume
```
|P_t| = |P_b|+1,   Parikh(P_t)−Parikh(P_b)=e_b.
```
Then `Parikh(P_t)=Parikh(P_b b)` and both prefixes have the **same index**. If the top track still has a next source letter, and the two parent words have equal total length, this produces an **interior aligned balanced cut**. Consequently it is impossible *inside a single irreducible equal-length balanced parent*.

`proof/psc_routes/R1Source.lean` now attempts this universally over arbitrary label maps into additive groups, via `HasAlignedInteriorReturn`, `unit_source_defect_forces_aligned_interior_return`, and `irreducible_parent_excludes_unit_source_germ`. It also proves that actual source-cut prefixes split the literal inflated word and satisfy the full `M·Parikh+proper-prefix-digit` law, rather than assuming free local correction segments. These are new Lean declarations **pending exact-head acceptance**.

**Adversarial correction.** The locally admissible *three-step* Tribonacci cut germ survives even after recording both next source letters and both within-letter offsets:
```
(e0; top0,bottom0) --(0,1)--> (e1; top0,bottom1)
(e1; top0,bottom1) --(0,1)--> (e2; top0,bottom2)
(e2; top0,bottom2) --(0,0)--> (e0; top0,bottom0).
```
These are genuine literal `0→01,1→02,2→0` **local source-image transformations**, checked by the new `TriCutGerm` Lean interface and independently exercised by `PscR1ProperCutGerm` Quint with source-index difference one. But the phase-`e0` germ has the following bottom letter `0`, exactly matching its positive unit source defect. By the previous lemma, this phase **cannot occur inside a single irreducible parent source pair** as a proper cut. A full deeply inflated strict component is a concatenation of irreducible children, however, so this only excludes one proposed *within-parent* realization, not recurrent cross-child ancestry.

**Independent literal-word calibration.** `PscR1Source.qnt` contrasts balanced words `001/010` (unit defect at top-source index 1 and bottom-source index 0, next bottom letter `0`, hence an interior balanced cut and reducibility) with `001/100` (same unit defect but next bottom letter `1`, which does not force a zero cut and permits irreducibility). Both are genuine factors of a Tribonacci iterate; the current Quint tests themselves assert only the literal three-letter word/count facts, not a universal legal-language theorem.

**Research consequence:** a candidate universal C4 elimination must keep the distinction between a *decorated germ*, a *cut inside one irreducible parent*, and a *cut across multiple derived children*. The algebraic cycle and local next-letter closure are not sufficient. Exact order, child boundaries, and recurrence over a strictly closed SCC remain the load-bearing unproved bridge. Work remains concurrent with the separate `R1OrderedAncestry.lean` / canonical Mojo packet replay in this branch, which independently inspects literal depth-six Tribonacci occurrence ancestry.

**Acceptance:** `.github/workflows/psc-bprime-r1-source.yml` requires seven complete Lean axiom receipts and two positive-count Quint literal-word tests at the exact GitHub head. The modular workflow additionally audits the new three-step germ theorem and its Quint witness. No acceptance or PSC promotion until the hosted results complete.

## 2026-11-07 — exact legal-factor controls for the single-parent no-go

The new literal-word source bridge goes beyond an untyped affine digit. Its eleven standalone Lean theorem declarations now include an independent finite **legal-factor** calibration for the actual Tribonacci substitution `0→01,1→02,2→0`. The fourth iterate is exactly

```
σ⁴(0) = 0102010010201.
```

The three control words `001`, `010`, and `100` all occur as contiguous factors of this same literal word, and `001` is Parikh-balanced with both `010` and `100`. The Lean source supplies explicit prefix/suffix witness factorizations, so this is not an empirical observation about an infinite language. The `001/010` pair has an interior aligned zero return at index one: at asynchronous source cuts (top index 1, bottom index 0), the defect is `e₀` and the next bottom letter is `0`, so adding that bottom letter balances the two prefixes at index one. By contrast, for `001/100` the next bottom letter is `1`, and that particular forced-return argument does not apply. Its irreducibility is tested by the bounded Quint literal-word control, not yet claimed as a separately Lean-certified theorem.

**Scope firewall.** This is an adversarial *one-parent* result, not a contradiction to the exact, nonzero source-ancestry cycles already produced by `R1OrderedAncestry` for inflated, reducible word pairs. A strict child-closed derived system may have newborn or inherited cuts between distinct child blocks. The truly missing BH/C4 theorem must show that recurrence and occurrence-address coherence force a forbidden cut *inside an irreducible parent*, or else force synchronization by a separate mechanism.

**Acceptance:** `proof/psc_routes/R1Source.lean` now declares eleven theorems, all named in its axiom audit; `.github/workflows/psc-bprime-r1-source.yml` enforces the exact declaration inventory and eleven kernel receipts. Quint still requires two explicit nonempty literal-word tests. No new exact-head hosted receipt has been observed for the enlarged source module. Keep existing proof and claim statuses unchanged.

## 2026-11-07 — proof-level reducible versus irreducible classification

The legal-word calibrations have been upgraded from a single forced-return witness and Quint assertions to *both sides of the distinction in Lean*. `R1Source.lean` now defines `NoAlignedInteriorReturn` in terms of actual word-prefix `take` and Parikh masses, then proves:

1. `tribonacci_matching_control_is_reducible`: the full balanced source-word pair `001/010` has an aligned interior zero return at index one, arising from the unit defect at asynchronous source indices (1,0) followed by bottom letter 0.
2. `tribonacci_nonmatching_control_is_irreducible`: the full balanced source-word pair `001/100` has **no** aligned zero return at either interior index one or two; the same unit defect but bottom letter 1 does not trigger the source-letter catch-up lemma.

Both word pairs have the same Parikh mass, and all three strings occur in the actual fourth Tribonacci fixed-point iterate `0102010010201`, also formalized by explicit exact finite witnesses. This removes any reliance on illegal-swap source words for this specific calibration.

**Audit inventory correction:** `R1Source.lean` has **13** theorem declarations, not the eleven recorded in the immediately preceding development entry. Its new workflow requires an exact 13-name theorem/axiom match and thirteen successful kernel axiom receipts; no parent-head acceptance is inherited. Across this branch the declared Lean theorem inventory is now 19 modular + 14 Smith + 13 source + 4 ordered ancestry = **50** names. Quint retains **29** explicitly named deterministic tests across the four model files. Their presence in source does **not** establish that the latest-hosted checks have passed.

The result remains a **single-parent** irreducibility obstruction. The exact physical path generated by a strict child-closed component may pass through a concatenation of several irreducible children; the next unproved step is to localize the repeated unit-defect phase to one irreducible child, or derive an independent synchronizing boundary from the intervening child cuts.
