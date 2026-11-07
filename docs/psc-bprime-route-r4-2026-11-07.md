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
Lean sublemma acceptance, if CI passes, is **not** a PSC/C4/A1′/BH/PDS closure. No universal theorem is being promoted; no ledger mutations or `geometry_formalized` promotion. Run exact source/claim governance when integrating into the main proof bank. Independent human mathematical review and comprehensive originality assessment are deferred; targeted automated literature stop/go is performed now and recorded below.

## Targeted literature stop/go — automated research-design gate

**Exact proposed experiment:** prove a *localized*, hub-related, occurrence-addressed Rauzy subtile separation/window property forcing a common balanced vertex or literal labeled coincidence, without assuming pure discrete spectrum.

**Closest literature:** (1) Arnoux–Ito, *Pisot Substitutions and Rauzy Fractals* (2001), DOI 10.36045/bbms/1102714169, covers Rauzy subtiles and strong coincidence / measure-disjointness, conditional on appropriate coincidence hypotheses, not unconditional hub separation. (2) Akiyama–Lee, *Algorithm for Determining Pure Pointedness of Self-Affine Tilings* (2011), DOI 10.1016/j.aim.2010.07.019, establishes overlap-coincidence algorithms under its tiling assumptions; a finite overlap graph does not itself imply a universal localized separation theorem. (3) Barge–Diamond 2002, DOI 10.24033/bsmf.2433, gives an eventually coincident letter pair rather than all-pairs strong coincidence. (4) The existing `docs/c4-cut-attractor-window-2026-11-05.md` and `docs/c4-cut-pair-productivity-2026-11-04.md` already establish relevant cut-attractor reductions and explicitly preserve geometric gaps.

**Hypothesis mismatch:** a physical translation in ℚ(β) can be tiny even with a nonzero integral trace-dual *address*. Small geometric displacement or a bounded return window cannot force the address to vanish without an exact separation certificate. A shared vertex/zero offset does not imply coincident tile without occurrence-bound label equality. Neither strong coincidence nor disjoint subtiles may be assumed.

**Decision: PROCEED NARROWED / EXACT CERTIFICATE FIRST.** Formalize typed lattice address + trace-dual proof objects and verify a finite localized separation window before any hub-subtile exclusion. The toy scalar integer-offset theorem is not a Rauzy geometry theorem. Independent human review and comprehensive novelty determination remain **post-PSC**, distinct from this automated stop/go.

## 2026-11-07 — exact algebraic-address reconstruction before geometric claims

The R4 Lean layer now has an exact rational matrix certificate `decode * encode = I`. From this *independently checkable* premise, `trace_dual_matrix_injective` proves that zero encoded rational coordinates force a zero rational address. `integral_address_of_trace_dual_zero` specializes this to a full **integral** address vector. This is the genuine linear-algebra-to-address bridge missing from the original scalar `|z| < 1` toy lemma.

**Scope firewall:** the premise applies only to a full rational encoding with a rational left inverse. It does not assert that taking only the Pisot stable physical projection, a single real geometric length, or an arbitrary Rauzy subtile coordinate has such an inverse. Actual trace-dual basis and packet bytes must be generated by the canonical exact arithmetic kernel and checked against their declared polynomial/degree, index lattice, label and occurrence provenance. Only then could the lemma prove a genuine overlap address is zero.

The typed `LabeledOverlapPacket` records the separate **top and bottom labels**. Its Lean negative test constructs zero integral address with unequal labels, establishing that even a certified common boundary does not imply a coincident tile. Any productivity theorem must add a source-bound common-label occurrence witness.

**Reproducibility:** newest `proof/psc_routes/R4.lean` checks the left-inverse identity and address proof in Mathlib, with an exact-declaration axiom audit; Quint retains its recurrent nonzero offset. Hosted acceptance at this exact head remains pending. The original geometric cover, measure and `geometry_formalized` claims remain **OPEN / false respectively**; no universal PSC advancement is asserted.
