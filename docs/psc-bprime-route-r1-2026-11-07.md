# R1 — Cyclic-vector / ancestry rigidity

**Baseline:** main `05fcf4f0136d1f1801a889f99d9c74a2396766ff` (2026-11-07). **Claim status:** proposal / conditional helper lemmas only; parent route BH (#139), C4 strict-component elimination. Concurrent and independent branch; no edits to `claim_governance.toml`, generated proof bank, or other route modules. Sources: `docs/c4-general-structure-2026-11-06.md`, `docs/c4-bprime-independent-proof-audit-2026-11-07.md`, `docs/c4-pisot-ancestry-finiteness.md`, `docs/c4-prefix-difference-return-calculus.md`, and `docs/conjecture-ledger.md`.

## Work shown

### Assumptions and hypotheses
Use repository-proved Pisot ancestry finiteness: a supplied finite strict child-closed component has integral ancestry defects in a finite set A, satisfying x[k+1] = M x[k] + c[k+1], for a finite correction alphabet. For a **correction-free stretch**, c=0, a positive left Perron eigenfunctional ℓ satisfies ℓ(x[k+n]) = β^n ℓ(x[k]). Irreducible χ_M implies ℓ is nonzero on each rational x≠0. Thus for finite A, m=min_{x∈A\{0}} |ℓ(x)|>0 and B=max_{x∈A}|ℓ(x)|; any nonzero correction-free run has β^n m≤B. The Lean layer proves the last implication **conditionally on m and B**, not the cyclicity or existence of correction-free stretches.

### Derivation / reduction
## Mathematical interface

Use repository-proved Pisot ancestry finiteness: a supplied finite strict child-closed component has integral ancestry defects in a finite set A, satisfying x[k+1] = M x[k] + c[k+1], for a finite correction alphabet. For a **correction-free stretch**, c=0, a positive left Perron eigenfunctional ℓ satisfies ℓ(x[k+n]) = β^n ℓ(x[k]). Irreducible χ_M implies ℓ is nonzero on each rational x≠0. Thus for finite A, m=min_{x∈A\{0}} |ℓ(x)|>0 and B=max_{x∈A}|ℓ(x)|; any nonzero correction-free run has β^n m≤B. The Lean layer proves the last implication **conditionally on m and B**, not the cyclicity or existence of correction-free stretches.

### Adversarial route question

Can a strictly nonsynchronizing recurrent, *occurrence-compatible* zipper force arbitrarily long stretches with c=0, or a stronger cancellation block with a provable net expansion? That is an OPEN dichotomy. Failure must yield a smallest finite counterexample with exact source letters, correction digits, within-image offsets, ordered child indices and orientation signs. A correction c=0 need not imply aligned supertile boundaries; retain both offsets explicitly.

### Required next Lean theorems

1. Irreducible-Q matrix makes every nonzero rational w cyclic; every left Perron eigenfunctional is nonzero on w.
2. Derive positive separation m by exact algebraic-number/root-sign certificates from the *computed* finite A, not floating thresholds.
3. Bind full ancestry x[k+1]=M x[k]+c[k+1] and prove maximum correction-free streak; check no accidental assumptions that all cycles are zero.
4. State the precise ordered strictness-to-long-run candidate and **attempt falsification before proof**.

### Quint semantics

`PscR1.qnt` is a bounded adversarial abstraction x'=2x+c with a **genuine nonzero fixed cycle** x=1, c=-1. It disproves “finite ancestry + positive growth ⇒ zero” when correction forcing is permitted. It does not encode a primitive Pisot substitution or show the existence of such a cycle in a strict PIP SCC.

### Acceptance boundary

Only `height_on_orbit` and `correction_free_run_exclusion` should receive kernel credit if Lean CI passes. No BH/C4/PSC closure, no strictness-to-correction-free theorem, and no automatic claim-ledger promotion. Existing Tribonacci recurrent nonzero ancestry is a required negative control. Human review is deferred until PSC closure.

### Evidence and replay
The first acceptance surface is `proof/psc_routes/R1.lean`, plus `proof/quint/PscR1.qnt`; both run on an exact-head GitHub CI checkout. From the repo root: `./tools/setup_lean.sh`, then `cd proof/PscVerif && lake env lean ../../proof/psc_routes/R1.lean`; Quint: `npx --yes @informalsystems/quint@0.33.1 typecheck proof/quint/PscR1.qnt` and `run --invariant` with the invariant named in the file. Outputs are **pending until exact-head hosted CI finishes**; checking that GitHub launched jobs is not a pass. The separate PSC proof bank is not yet extended with these standalone modules; formal integration and axiom inventory are future gates.

### Negative controls
A nonzero forced cycle x=1, β=2, c=−1 persists forever; Tribonacci has actual recurring nonzero decorated ancestry. Correction-free expansion cannot be applied to forced orbits.

### Non-claims / remaining gaps
Lean sublemma acceptance, if CI passes, is **not** a PSC/C4/A1′/BH/PDS closure. No universal theorem is being promoted; no ledger mutations or `geometry_formalized` promotion. Run exact source/claim governance when integrating into the main proof bank. Human literature and mathematical review are deferred until after PSC closure.
