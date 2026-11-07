# R3 — Prefix-return / prefix-seeded BPA direct PDS

**Baseline:** main `05fcf4f0136d1f1801a889f99d9c74a2396766ff` (2026-11-07). **Claim status:** proposal / conditional helper lemmas only; parent route alternative PDS without all-seed G1. Concurrent and independent branch; no edits to `claim_governance.toml`, generated proof bank, or other route modules. Sources: `docs/c4-general-structure-2026-11-06.md`, `docs/c4-bprime-independent-proof-audit-2026-11-07.md`, `docs/c4-pisot-ancestry-finiteness.md`, `docs/c4-prefix-difference-return-calculus.md`, and `docs/conjecture-ledger.md`.

## Work shown

### Assumptions and hypotheses
For one-sided fixed point u and **nonempty prefix W**, define t_n=|σⁿ(W)| and P(k)=Parikh(u[0,k)). Exact identity:
D_n(k)=P(k)−[P(t_n+k)−P(t_n)] = P(t_n)−[P(k+t_n)−P(k)].
If the aligned shifted tracks have balanced blocks of length ≤L, the coordinate count differences inside a block are ≤L. The separate **open** problem is to prove those blocks have a bound uniform in n for some suitable prefix, and then prove the resulting finite BPA is productive. Pisot contraction/balance alone does not provide returns.

### Derivation / reduction
## Mathematical interface

For one-sided fixed point u and **nonempty prefix W**, define t_n=|σⁿ(W)| and P(k)=Parikh(u[0,k)). Exact identity:
D_n(k)=P(k)−[P(t_n+k)−P(t_n)] = P(t_n)−[P(k+t_n)−P(k)].
If the aligned shifted tracks have balanced blocks of length ≤L, the coordinate count differences inside a block are ≤L. The separate **open** problem is to prove those blocks have a bound uniform in n for some suitable prefix, and then prove the resulting finite BPA is productive. Pisot contraction/balance alone does not provide returns.

### Machine verification milestones

1. Lean: literal shift identity and integer bounded-block coordinate estimate (initial scaffold).
2. Quint: explicit bounded-return-gap process with nonproductive repeat, disproving “bounded gaps ⇒ coincidence”.
3. Formalize exact Sirvent–Solomyak I_n(W) recurrence, including starting index, full infinite decomposition, coincidences, literal substitution offsets, and fixed-point legality.
4. Attempt a new uniform prefix-return theorem using recognizability + Pisot ancestry, **without assuming overlap productivity** (that would be circular).
5. Only after independent return finiteness, seek termination with coincidences and apply the literature PDS criterion with exact source/theorem applicability.

### Negative controls

Illegal swap seed ≠ prefix seed. The derived substitution of a strict component may have uniformly bounded zero-return gaps while having no coincident children (non-Pisot control). Balanced discrepancy need not imply returns, and termination does not imply termination with coincidence. `PscR3.qnt` encodes a bounded-gap cut/reset cycle with coincidence permanently false.

### Acceptance boundary

Lean proves the identity and coordinate bound; Quint proves bounded local-state invariants, not universal return finiteness. The prefix-return theorem, productivity, and PSC remain OPEN. The full all-seed G1 is not assumed or claimed. Human review remains deferred.

### Evidence and replay
The first acceptance surface is `proof/psc_routes/R3.lean`, plus `proof/quint/PscR3.qnt`; both run on an exact-head GitHub CI checkout. From the repo root: `./tools/setup_lean.sh`, then `cd proof/PscVerif && lake env lean ../../proof/psc_routes/R3.lean`; Quint: `npx --yes @informalsystems/quint@0.33.1 typecheck proof/quint/PscR3.qnt` and `run --invariant` with the invariant named in the file. Outputs are **pending until exact-head hosted CI finishes**; checking that GitHub launched jobs is not a pass. The separate PSC proof bank is not yet extended with these standalone modules; formal integration and axiom inventory are future gates.

### Negative controls
Noncoincident balanced blocks can recur with bounded cut gaps without a single coincident letter. Prefix and illegal swap seeds are not interchangeable; bounded discrepancy is not return existence.

### Non-claims / remaining gaps
Lean sublemma acceptance, if CI passes, is **not** a PSC/C4/A1′/BH/PDS closure. No universal theorem is being promoted; no ledger mutations or `geometry_formalized` promotion. Run exact source/claim governance when integrating into the main proof bank. Human literature and mathematical review are deferred until after PSC closure.
