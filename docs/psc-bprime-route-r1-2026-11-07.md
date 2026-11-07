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
Lean sublemma acceptance, if CI passes, is **not** a PSC/C4/A1′/BH/PDS closure. No universal theorem is being promoted; no ledger mutations or `geometry_formalized` promotion. Run exact source/claim governance when integrating into the main proof bank. Independent human mathematical review and comprehensive originality assessment are deferred; targeted automated literature stop/go is required now and recorded below.

## Targeted literature stop/go — automated research-design gate (not human validation)

**Exact proposal:** test whether a finite strict PIP ancestry system forces arbitrarily long correction-free segments in its ordered, occurrence-addressed orbit, and derive a contradiction using cyclic Perron-height rigidity.

**Closest sources and distinctions (publisher descriptions and repository's audited primary-source gates):**
1. Sirvent–Solomyak, *Pure Discrete Spectrum for One-dimensional Substitution Systems of Pisot Type* (2002), DOI 10.4153/CMB-2002-062-3, especially §§3–5: termination, prefix-seeded balanced pairs and half-coincidence return gaps. It does **not** state that a recurrent **arbitrary strict** ancestry necessarily has correction-free segments; prefix legality is an important difference. https://doi.org/10.4153/CMB-2002-062-3
2. Adamczewski, *Balances for Fixed Points of Primitive Substitutions* (2003), DOI 10.1016/S0304-3975(03)00092-6: spectral control of balance/discrepancy for legal fixed-point factors, not a correction-free strict SCC theorem. https://doi.org/10.1016/S0304-3975(03)00092-6
3. Barge–Diamond, *Coincidence for Substitutions of Pisot Type* (2002), DOI 10.24033/bsmf.2433: an eventually coincident pair and hub restriction, not productivity of every ordered bad strict component. https://doi.org/10.24033/bsmf.2433

**Preexisting in-repo proof/negative:** `docs/c4-pisot-ancestry-finiteness.md` proves finiteness of full *forced* ancestry; `docs/c4-recognizable-cut-germs.md` contains a genuine Tribonacci nonzero recurrent ancestry example. `docs/c4-ordered-hub-literature-gate-2026-10-06.md` already scopes literal ordered address requirements. The elementary no-forcing growth lemma is standard linear algebra, with no novelty asserted.

**Hypothesis transfer:** PIP's β>1, rational cyclicity and finite integral ancestry transfer; bounded gaps/forced digits are **not** assumed zero. The repo's illegal swap states cannot be treated as fixed-point prefixes.

**Decision: PROCEED NARROWED.** Formalize the conditional growth lemma and exhibit a forced-cycle countermodel; next prove or refute a **strictness + occurrence-compatible lineage ⇒ long correction-free stretch** statement. Do not promote a result unless the actual ordered-state premise is established. This automated targeted check satisfies research-design provenance while **independent human review remains deferred until after PSC closure**.

## 2026-11-07 — source-word transport and independent Tribonacci adversary

**New formal interface:** `wordMass_append`, `wordMass_substitution`, and `asynchronous_word_mass_transport` operate on literal lists over any alphabet and an additive Parikh-valued map. Under an explicit **per-letter incidence equality** `M (label a)=wordMass (σ a)`, the claimed asynchronous identity follows exactly:
[
\mathrm{mass}(\sigma(U)+U_{local})-\mathrm{mass}(\sigma(V)+V_{local})
=M(\mathrm{mass}(U)-\mathrm{mass}(V))
+\mathrm{mass}(U_{local})-\mathrm{mass}(V_{local}).
]
There is **no** claim yet that the supplied local fragments are canonical proper source-image prefixes or correspond to actual legal occurrence addresses. That is the next refinement obligation.

**Adversarial control:** the real 3×3 Tribonacci incidence action on the existing recorded defects has an exact three-step signed-correction loop `(1,−1,0) → (0,1,−1) → (−1,0,1) → (1,−1,0)`, with first-coordinate corrections `0,−1,+1`. The Lean equality is finite arithmetic; `PscR1TribonacciArithmetic` is a *separate* Quint module whose test now must be invoked with `--main=PscR1TribonacciArithmetic`. This reproduces only the matrix/correction arithmetic; the existing Python ancestry test is still the source locator for literal cut occurrences.

**Important exact-head failure retained:** hosted run `42398141936` at `762cdd7247eb1a30378252645877d2f0fedf86da` failed its Lean axiom check because the proof of digit-negation improperly inducted on `n` while retaining the period and height hypotheses. The resulting dependent induction was incomplete and Lean introduced `sorryAx`; the fail-closed audit rejected the declaration. Fixed by an *independent unconditional induction* `forcedDigitSum_neg` in follow-up commit `a413841d3e3a68ecd2cf81f8726d2471c2041804`. The fix and new source-word bridge require exact-head replay.

**Required closure gate:** demonstrate that every recurrent, **strict** and **occurrence-compatible** PIP ancestry yields a cycle whose actual correction digits violate the periodic rational/algebraic certificate. Neither a mere cycle nor correction-free growth alone proves this. Reversed-orientation cycles must remain legal counter-calibrations. Universal PSC/BH/C4 status unchanged.
