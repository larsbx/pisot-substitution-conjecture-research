# R4 — Geometric return-window / separation

**Baseline:** main `05fcf4f0136d1f1801a889f99d9c74a2396766ff` (2026-11-07). **Claim status:** proposal / conditional helper lemmas only; parent route seed overlap productivity and local subtile separation. Concurrent and independent branch; no edits to `claim_governance.toml`, generated proof bank, or other route modules. Sources: `docs/c4-general-structure-2026-11-06.md`, `docs/c4-bprime-independent-proof-audit-2026-11-07.md`, `docs/c4-pisot-ancestry-finiteness.md`, `docs/c4-prefix-difference-return-calculus.md`, and `docs/conjecture-ledger.md`.

## Work shown

### Assumptions and hypotheses
At a return cut, algebraic/physical displacement must be transported through a **typed** integral lattice address and a trace-dual embedding into ℚ(β), alongside labels and occurrence addresses. Pisot contraction may bound conjugate coordinates, but *small geometric displacement does not force the address to be zero* without a certified lattice separation/finite-address window. Likewise common vertex (offset zero) does not imply common tile (coincidence): require an addressed matching letter.

### Derivation / reduction
## Mathematical interface

At a return cut, algebraic/physical displacement must be transported through a **typed** integral lattice address and a trace-dual embedding into ℚ(β), alongside labels and occurrence addresses. Pisot contraction may bound conjugate coordinates, but *small geometric displacement does not force the address to be zero* without a certified lattice separation/finite-address window. Likewise common vertex (offset zero) does not imply common tile (coincidence): require an addressed matching letter.

### First formal certificates

1. Lean: abstract certified separation theorem; scalar integer offset <1 ⇒ 0 as a **toy** exact arithmetic control. These do not certify Rauzy subtile intersections.
2. Quint: affine bounded overlap x'=2x−1 with permanent nonzero x=1 and no common tile, refuting “bounded overlap recurrence ⇒ zero/coincidence.”
3. Exact polynomial/trace-dual coordinate schema for actual PIP overlaps: minimal polynomial, integral offset vector, tile labels, source-word indices, local digit, conjugate contraction bound, finite-window enclosure.
4. Independently verify “inside certified *separation* radius ⇒ common vertex”, then independently verify ordered-label coincidence. Do not replace either with an analytic approximation.
5. Look for a **localized hub-subtile separation theorem**, strictly weaker than unconditional disjointness, and adversarially replay known overlap packet/source controls.

### Geometry/verification boundary

Mathlib arithmetic lemma and Quint model are only conditional controls. No assumption of subtile measure-disjointness, strong coincidence, a priori overlap-productivity, or numerical plot evidence. Any proposed local separation radius must be bound to actual canonical exact-address packets with independent replay, and `geometry_formalized` must stay false until those premises are kernel checked. Universal PSC remains OPEN; human review post-PSC.

### Evidence and replay
The first acceptance surface is `proof/psc_routes/R4.lean`, plus `proof/quint/PscR4.qnt`; both run on an exact-head GitHub CI checkout. From the repo root: `./tools/setup_lean.sh`, then `cd proof/PscVerif && lake env lean ../../proof/psc_routes/R4.lean`; Quint: `npx --yes @informalsystems/quint@0.33.1 typecheck proof/quint/PscR4.qnt` and `run --invariant` with the invariant named in the file. Outputs are **pending until exact-head hosted CI finishes**; checking that GitHub launched jobs is not a pass. The separate PSC proof bank is not yet extended with these standalone modules; formal integration and axiom inventory are future gates.

### Negative controls
The bounded affine orbit x=1 under x↦2x−1 has no zero offset; zero offset is not a tile coincidence. Integer offset smallness is not a theorem about arbitrary ℚ(β) offsets.

### Non-claims / remaining gaps
Lean sublemma acceptance, if CI passes, is **not** a PSC/C4/A1′/BH/PDS closure. No universal theorem is being promoted; no ledger mutations or `geometry_formalized` promotion. Run exact source/claim governance when integrating into the main proof bank. Human literature and mathematical review are deferred until after PSC closure.
