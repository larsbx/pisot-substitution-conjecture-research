# Conjecture ledger

## C1 — SCC Producer Theorem

**Statement.** For every primitive irreducible Pisot substitution, every recurrent noncoincident SCC of `B_sigma` produces a coincidence sibling at some inflation step.

**Status.** Open in general. Settled for two-letter case through Hollander--Solomyak. Known for beta-substitution and special families.

**Equivalent formulations in this program.**

- No closed nonproductive recurrent noncoincident SCC exists.
- No diagonal-free zero-return system exists.
- No nonsynchronizing zero-return trap exists.

## C2 — Nonsynchronizing-core escape

**Statement.** Every recurrent noncoincident SCC eventually has a zero-return boundary whose right adjacent pair lies in `Sync_+` or whose left adjacent pair lies in `Sync_-`.

**Status.** Boundary normal form for C1 when all iterates are allowed. Useful because it localizes the obstruction to finite endpoint-map dynamics.

## C3 — Newborn synchronizing boundary

**Statement.** If all inherited zero-return boundaries remain nonsynchronizing under further inflation, some higher inflation creates a newborn zero-return boundary whose right adjacent pair lies in `Sync_+` or whose left adjacent pair lies in `Sync_-`.

**Status.** Active next target. This is more tactical than C1/C2 because inherited boundaries are controlled by finite maps `sigma_+` and `sigma_-`.

## C4 — finite-pigeon lift

**Statement.** Finite recurrence of boundary types, combined with primitivity, forces newborn boundary escape from the nonsynchronizing cores.

**Status.** Programmatic. The common-cut recurrence notes provide an analogue of the finite-pigeon component, but not this theorem.
