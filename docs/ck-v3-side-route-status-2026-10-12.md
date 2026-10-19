# CK-v3 side-route status — 2026-10-12

**Status:** side-route status note; no claim-status promotion.

## Purpose

This note records the minimum useful residue from the October 2026 finite-BPA / SCC diagnostic thread. It is a non-load-bearing research status note. It does not change the current proof architecture, the conjecture ledger, or the priority of the overlap-productivity route.

The live primary route remains the overlap-first route recorded in `docs/current-proof-architecture-2026-09-14.md` and `docs/conjecture-ledger.md`:

```text
PIP
=> bounded discrepancy
=> finite seed-patch overlap graph
=> seedwise overlap productivity        [OPEN]
=> coincidence density one / dense good set
=> PDS                                 [imported density-to-PDS bridge]
```

The finite-BPA SCC Producer route remains a stronger parallel programme, conditional on the appropriate finite-BPA/G1 extraction hypotheses.

## Corrected finite-BPA target

The useful SCC-side target is:

> **CK-v3 / SCC Producer.** Every closed recurrent noncoincident SCC contains a coincidence-producer state.

Equivalently, there is no finite closed recurrent SCC all of whose states are nonproducers.

This replaces two overstrong formulations that should not be reused:

- universal exclusion of recurrent noncoincident SCCs or cycles;
- per-state immediate productivity.

Recurrent noncoincident SCCs/cycles can exist. The live finite-BPA question is whether a closed recurrent noncoincident SCC can avoid producers altogether.

## Minimal bad object, if this route is pursued

If CK-v3 fails inside a finite BPA, the appropriate counterexample normal form is a minimal closed nonproducer SCC. A useful working normal form records:

- balanced noncoincident states;
- recurrence inside a finite closed component;
- absence of coincidence-producing siblings;
- common-cut / bracket data for actual inflated child factorizations;
- signed child-transfer data and branch class information.

This is a diagnostic normal form only. It is not a proof that such a component exists globally, and it is not a substitute for G1 or for the overlap-first route.

## Useful diagnostics retained

The following structures are worth preserving for future SCC work, but only as diagnostics unless separately proved and promoted.

### Branch signing and transfer

For a closed no-cancellation SCC, the compatible-signing criterion is standard finite signed Perron-Frobenius theory:

```text
Branch B
<=> branch sign is a coboundary modulo period wrap
<=> signed transfer is gauge/period equivalent to the unsigned transfer.
```

This finite-graph criterion is theorem-grade once the exact SCC transfer convention is fixed.

The observed threshold

```text
rho(N_C) = beta * |beta_2|  iff  Branch B
```

is empirical at the current stage. It should not be used as a proof input without a precise operator contract and a proof that the unsigned transfer dominates the relevant exterior-square growth.

### Bracket signatures

Enriched bracket signatures are useful rigidity data for states and return windows. They appear to rule out exact bracket self-copy as an obstruction type in the tested regimes.

Do not use bracket signatures as a descent proof: bracket complexity is not known to be monotone and was observed to grow in some diagnostics.

Also do not derive bracket injectivity from the false implication "letter-injective substitution => word-injective substitution." For legal substituted blocks, preimage recovery must go through recognizability / unique desubstitution in the relevant collared context.

### Residual chase imbalance

The residual chase imbalance gives a real edge diagnostic; in the alphabet-three tests it collapses to a single `F_2` bit and is stable on parallel edges. It does not coincide with the branch-sign cocycle in general and does not close Branch B/C.

### FI boundary regime

Injective first/last boundary maps empirically exclude Branch B in the tested regimes. This is useful as a calibration and boundary diagnostic.

Finite injectivity is not a standing hypothesis of PSC and must not enter a general proof route.

## Non-claims

Do not import any of the following from the diagnostic thread as theorem statements:

- no recurrent noncoincident SCC/cycle exists;
- every Branch B state is immediately productive;
- Branch B diagonal-boundary behavior is proved generally;
- bracket descent closes CK-v3;
- residual chase imbalance equals the branch sign cocycle;
- `rho(N_C) <= beta * |beta_2|` or quantitative Mossé via unsigned `N_C` decay;
- locked one-sided padding alone forces recognizable cut lifting;
- `K2` equality implies full bracket equality;
- a coordinate projection on `Lambda^2` correctly models retained interval self-copy.

## Routing decision

Keep this material as finite-BPA side-route science. The only durable target extracted from the thread is CK-v3 / SCC Producer in the form stated above.

The live proof priority remains seedwise overlap productivity. Any future theorem-facing use of the diagnostics in this note needs its own literature gate, exact object contract, implementation/proof boundary, and counter-calibration under the repository verification policy.

## 2026-10-19 literature follow-up — prefix/suffix and Branch B

See [the Branch-B prefix/suffix literature gate](branch-b-prefix-suffix-literature-gate-2026-10-19.md) for the sourced distinction between endpoint maps and the classical prefix-suffix automaton, Barge's initial-injective/final-constant theorem, and the open bi-injective Branch-B exclusion question. The proposed Boundary-Injection Exclusion and collision-realization statements remain **separate open side-route lemmas**. Neither changes CK-v3, G1, #138/#139, #84, or PSC status; the empirical SCC tallies cited in discussions were not re-certified by this documentation update.
