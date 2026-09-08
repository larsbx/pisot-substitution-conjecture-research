# Automated research protocol

## Agent duties

Agents working in this repository should preserve the proof-state distinction:

- **proved**: has a proof in source or precise citation;
- **conditional**: explicitly names the conjectural dependency;
- **empirical**: backed by scripts and seeds, but not a theorem;
- **retired**: known false or structurally blocked.

## Required checks before proposing a theorem

1. Run core example tests.
2. Add a regression test for the claim.
3. Search the conjecture ledger for matching retired routes.
4. State exact hypotheses, especially whether unimodularity is absent.
5. If using a citation, record theorem number and what it actually proves.

## Required checks before editing a manuscript

1. No stale `N_C = M_sigma` synthetic-countermodel language; it must be `N_C = M_sigma^T, P = I`.
2. Do not claim unconditional PSC unless SCC Producer has been proved.
3. Do not cite BD/BK as proving no recurrent noncoincident cycles.
4. Boundary synchronization is a normal form/reduction layer, not a completed proof of PSC.
