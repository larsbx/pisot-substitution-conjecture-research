# R3 — Prefix-return / prefix-seeded BPA direct PDS

**Original development baseline:** main `05fcf4f0136d1f1801a889f99d9c74a2396766ff` (2026-11-07). **Claim status:** proposal / conditional helper lemmas only; parent route alternative PDS without all-seed G1. The route remains independent of R1/R2/R4; no governed claim is promoted. Sources: `docs/c4-general-structure-2026-11-06.md`, `docs/c4-bprime-independent-proof-audit-2026-11-07.md`, `docs/c4-pisot-ancestry-finiteness.md`, `docs/c4-prefix-difference-return-calculus.md`, and `docs/conjecture-ledger.md`.

## Integration reconciliation — 2026-11-11

[PR #509](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/509)
is reconciled with main `2848e5f67b605669a550f362a1de4bf1c1529f7c` through
#541, preserving its original history and both routes' append-only side notes.
The seven Lean declarations and the Quint model are unchanged from final
source head `f4fcb930b5fe761fe339fc734cad0671c7de2adf`.
The pinned compiler, Mathlib manifest and setup script are also unchanged.
Its [dedicated final-head run](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42400835654)
completed successfully in both Lean and Quint. This supersedes the original
pending statements below for that historical source revision; it is not a
fresh integrated-head receipt.

The reconciled workflow now follows changes to the actual Lean provisioning
inputs, requires all seven named axiom receipts, refuses a missing Lean log,
and fixes the Quint seed while requiring its deterministic negative witness.
Fresh hosted acceptance must cover this changed workflow on the published
integration revision. The standalone modules retain their separate axiom gate;
they are not registered as complete proofs of a governed PSC claim.

Main's newer finite occurrence and compact matrix-adic interfaces do not
supply R3's missing uniform-in-depth prefix-return gaps or coincidence
premise. Bounded-word-pair finiteness remains conditional on the supplied
length bound, and the original nonempty fixed-point-prefix contract remains
essential. No G1, PDS, C4 or PSC status changes.

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

Lean proves the identity and coordinate bound; Quint checks bounded local-state invariants, not universal return finiteness. The prefix-return theorem, productivity, and PSC remain OPEN. The full all-seed G1 is not assumed or claimed. Human review remains deferred.

### Evidence and replay
The first acceptance surface is `proof/psc_routes/R3.lean`, plus `proof/quint/PscR3.qnt`; both run on an exact-head GitHub CI checkout. From the repo root: `./tools/setup_lean.sh`, then `cd proof/PscVerif && lake env lean ../../proof/psc_routes/R3.lean`; Quint: `npx --yes @informalsystems/quint@0.33.1 typecheck proof/quint/PscR3.qnt` and `run --invariant` with the invariant named in the file. The original final-head hosted acceptance is now recorded in the integration reconciliation above. Fresh acceptance of the reconciled workflow remains revision-specific; checking that GitHub launched jobs is not a pass. The separate PSC proof bank is not yet extended with these standalone modules; formal integration and axiom inventory are future gates.

### Negative controls
Noncoincident balanced blocks can recur with bounded cut gaps without a single coincident letter. Prefix and illegal swap seeds are not interchangeable; bounded discrepancy is not return existence.

### Non-claims / remaining gaps
Lean sublemma acceptance, if CI passes, is **not** a PSC/C4/A1′/BH/PDS closure. No universal theorem is being promoted; no ledger mutations or `geometry_formalized` promotion. Run exact source/claim governance when integrating into the main proof bank. Independent human mathematical review and comprehensive originality assessment are deferred; targeted automated literature stop/go is performed now and recorded below.

## Targeted literature stop/go — automated research-design gate

**Exact proposed experiment:** derive uniform balanced-return gaps for at least one *fixed-point prefix seed* of every PIP substitution **without** assuming overlap productivity, then prove eventual coincidence and use the standard PDS criterion.

**Prior sources:** (1) Sirvent–Solomyak 2002, DOI 10.4153/CMB-2002-062-3, Theorem 5.6: prefix-BPA finiteness is already equivalent to uniformly bounded gaps between geometric half-coincidences under their stated Pisot/length hypotheses. Thus *finite return gaps ⇒ prefix-BPA termination* is **PRIOR**, not a new theorem. (2) Martensen 2004, *Generalized Balanced Pair Algorithm*, Topology Proceedings 28, arXiv math/0309194: distinguishes population balance, generalized/reducible algorithms, and nontermination controls. (3) Akiyama–Barge–Berthé–Lee–Siegel, *On the Pisot Substitution Conjecture* (2015), Theorem 5.3, as cited by `docs/bpa-overlap-depth-literature-gate-2026-10-02.md`: termination **with coincidence** is the extra route to PDS, not bare finiteness. Publisher/abstract provenance: https://doi.org/10.4153/CMB-2002-062-3 and https://arxiv.org/abs/math/0309194.

**Hypothesis transfer:** fixed point, nonempty legal prefix and Perron lengths transfer. A swap seed need not be legal; the all-swap graph is a different object. The repository's `docs/bpa-termination-by-overlap-depth-2026-10-02.md` already proves a bounded-gap implication under *overlap productivity*; using it for this route's independent return theorem would be circular.

**Negative:** a recurrent noncoincident balanced-block system can have uniformly bounded return gaps while remaining nonproductive. `PscR3.qnt` is an intentionally abstract bounded reset-cycle control, not a strict PIP construction.

**Decision: REDIRECT TO THE MISSING CONVERSE.** Do **not** repro­ve Theorem 5.6 as novelty. Seek a novel uniform-gap theorem from Pisot/recognizability **without presupposing overlap productivity**, then a separate coincidence theorem. Human review deferred until post-PSC, but targeted stop/go is satisfied here.

## 2026-11-07 — bounded-length state finiteness formal interface

New Mathlib-backed Lean theorems `finite_bounded_pair_states` and `finite_bounded_balanced_states` state that, for a finite alphabet and fixed length bound `L`, the set of all literal ordered word pairs of lengths ≤ `L` is finite; imposing Parikh balance or irreducibility can only shrink that finite set. The proof relies on standard Mathlib `List.finite_length_le` and `Set.Finite.prod` and is **not a new mathematical finiteness theorem**. It is the conditional state-space bridge needed after a uniform bound on full prefix-shift irreducible block lengths is supplied.

The target remains to prove a *uniform in depth* balanced-cut gap bound for a suitable legal nonempty fixed-point prefix `W`, without using any PDS/overlap-productivity result that would make the argument circular. A finite length bound on an arbitrary unrelated set, bounded Parikh discrepancy, or a single productive occurrence is insufficient.

Earlier exact-head hosted run `42397742333` accepted the integer shift/telescoping lemmas and deterministic bounded-return/no-coincidence Quint test; the subsequent final-head run `42400835654` also accepted all seven named declarations, including the finite-bounded-state lemmas and coordinatewise Parikh identity. That historical receipt is superseded only by a successful receipt for any later changed proof revision. No PDS, G1, C4 or PSC promotion.
