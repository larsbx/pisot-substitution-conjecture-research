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
Lean sublemma acceptance, if CI passes, is **not** a PSC/C4/A1′/BH/PDS closure. No universal theorem is being promoted; no ledger mutations or `geometry_formalized` promotion. Run exact source/claim governance when integrating into the main proof bank. Human literature and mathematical review are deferred until after PSC closure.
