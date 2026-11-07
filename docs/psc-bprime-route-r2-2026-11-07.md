# R2 — Oriented half-space / B′ averaging contradiction

**Baseline:** main `05fcf4f0136d1f1801a889f99d9c74a2396766ff` (2026-11-07). **Claim status:** proposal / conditional helper lemmas only; parent route A1′ (#138), C4, ordered hub-residual lemma. Concurrent and independent branch; no edits to `claim_governance.toml`, generated proof bank, or other route modules. Sources: `docs/c4-general-structure-2026-11-06.md`, `docs/c4-bprime-independent-proof-audit-2026-11-07.md`, `docs/c4-pisot-ancestry-finiteness.md`, `docs/c4-prefix-difference-return-calculus.md`, and `docs/conjecture-ledger.md`.

## Work shown

### Assumptions and hypotheses
The proposed contradiction requires a *specific* rational functional h with h(D_n(k))≥0 for every relevant **actual oriented** descendant, and a uniform δ>0 and density ρ>0 of indices where h(D_n(k))≥δ, **plus** a source-bound averaging theorem giving mean h(D_n)→0. Then 0<ρδ≤mean h(D_n), contradiction. The present Lean proof establishes the *finite exact counting inequality* over ℚ; it does not produce h, ρ, δ, an invariant distribution, or the average-decay premise.

### Derivation / reduction
## Mathematical interface

The proposed contradiction requires a *specific* rational functional h with h(D_n(k))≥0 for every relevant **actual oriented** descendant, and a uniform δ>0 and density ρ>0 of indices where h(D_n(k))≥δ, **plus** a source-bound averaging theorem giving mean h(D_n)→0. Then 0<ρδ≤mean h(D_n), contradiction. The present Lean proof establishes the *finite exact counting inequality* over ℚ; it does not produce h, ρ, δ, an invariant distribution, or the average-decay premise.

### Adversarial route question

Search first for a global half-space h consistent with all fully ordered child rows, raw top/bottom orientation, hub-side bit and signed return defects. A side swap sends D to -D, so forgetting orientation can manufacture false half-space certificates. Test opposite-side descendants and an adversarial two-cycle with D∈{−1,1} whose average is zero but which never hits D=0.

### Machine-search obligations

1. Extract an exact sign-matrix of all ordered occurrence-indexed descendant defects for supplied strict components or synthetic controls.
2. Use rational linear feasibility (exact Fourier–Motzkin or integer certificates) to find h, or produce a rational Farkas-style infeasibility certificate.
3. Quantify a common lower density of positive h(D) **with explicit recurrence hypothesis**; a single occurrence is insufficient.
4. Bind averaging to the same physical, prefix-seeded displacement process. B′ supplies the shift average for *legal fixed-point prefixes*, not automatically for arbitrary strict SCC pairs.
5. Transport a witness to an actual Sync_± newborn if possible; otherwise report an adversarial countermodel.

### Quint semantics

`PscR2.qnt` cycles between ±1 with bounded cumulative sum. The model explicitly demonstrates that average zero and boundedness do **not** imply a zero return. This rejects a tempting but invalid shortcut, rather than verifying the proposed positivity dichotomy.

### Acceptance boundary

Lean certifies `good_mass_lower_bound` and `positive_density_contradiction` only on exact finite hypotheses. The sought orientation/density theorem and A1′/C4/PSC remain OPEN. Preserve the ordered synthetic template and real recurrent negative controls. Human review is post-PSC.

### Evidence and replay
The first acceptance surface is `proof/psc_routes/R2.lean`, plus `proof/quint/PscR2.qnt`; both run on an exact-head GitHub CI checkout. From the repo root: `./tools/setup_lean.sh`, then `cd proof/PscVerif && lake env lean ../../proof/psc_routes/R2.lean`; Quint: `npx --yes @informalsystems/quint@0.33.1 typecheck proof/quint/PscR2.qnt` and `run --invariant` with the invariant named in the file. Outputs are **pending until exact-head hosted CI finishes**; checking that GitHub launched jobs is not a pass. The separate PSC proof bank is not yet extended with these standalone modules; formal integration and axiom inventory are future gates.

### Negative controls
Alternating defects +1,−1 have mean zero without any zero defect. Oriented side swaps reverse the sign of every candidate functional; a sign-blind quotient invalidates separation.

### Non-claims / remaining gaps
Lean sublemma acceptance, if CI passes, is **not** a PSC/C4/A1′/BH/PDS closure. No universal theorem is being promoted; no ledger mutations or `geometry_formalized` promotion. Run exact source/claim governance when integrating into the main proof bank. Independent human mathematical review and comprehensive originality assessment are deferred; targeted automated literature stop/go is performed now and recorded below.

## Targeted literature stop/go — automated research-design gate

**Exact proposed experiment:** seek a rational half-space functional on fully oriented, occurrence-indexed strict PIP return defects with a *uniform positive-density* inequality, and use B′'s fixed-point averaging to contradict positive mass. No claim that a strict component supplies such a functional.

**Primary sources / attribution:** (1) Adamczewski 2003, *Balances for Fixed Points of Primitive Substitutions*, DOI 10.1016/S0304-3975(03)00092-6: discrepancy/spectral bounds concern fixed-point factors, not an arbitrary signed strict-component process. (2) Sirvent–Solomyak 2002, DOI 10.4153/CMB-2002-062-3, §§3–5: prefix-seeded BPA, aligned returns, and half-coincidences; the shift average cannot be transported to a synthetic or illegal strict word without an explicit source bridge. (3) Barge–Diamond 2002, DOI 10.24033/bsmf.2433: a good edge constrains cut pairs but does not force a globally consistent orientation half-space. (4) The existing `docs/c4-ordered-hub-literature-gate-2026-10-06.md` compares the same ordered-mask issue with Martensen 2004's generalized balanced pairs.

**Hypothesis mismatch / known negative:** track raw top/bottom signs; a side swap negates defects. The alternating sequence `+1,−1,+1,−1,...` has mean 0 but never equals 0, so average convergence alone is insufficient. The current Lean inequality is elementary ordered-field arithmetic, not a new universal theorem.

**Decision: PROCEED NARROWED / ADVERSARIAL.** Automatically search for an *actual ordered* linear separation and prove its occurrence-weighted density (or produce an infeasibility witness), then attempt source-bound averaging; stop if only sign-quotient or illegal seeds support the claim. Human mathematical validation and comprehensive novelty review remain **post-PSC**, not substitutes for this brief research-design check.
