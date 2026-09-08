# Proof ladder

## Stable levels

### Level 2: finiteness of the balanced-pair automaton

Current route:

1. `det M_sigma != 0` gives letter injectivity.
2. Defect theorem gives unique decodability of the image code `{sigma(a)}`.
3. Unique decodability for powers gives unique supertile hierarchy inside supertiles.
4. Phase automaton bounds coincidence padding by `D(sigma) <= |A|^2 |sigma|_max^2`.
5. Pisot growth gives predecessor contraction and hence finite `B_sigma`.

### Local part of Level 3

Unique hierarchy gives local witness injectivity inside a level-`n` supertile. This is local, not global: finite witness data does not determine an entire bi-infinite tiling.

## Open Level 3

The open step is not cycle exclusion. The correct target is:

> **SCC Producer Theorem.** Every recurrent noncoincident SCC of `B_sigma` produces a coincidence sibling at some inflation step.

Equivalent mass-leakage form:

> No recurrent noncoincident SCC is closed nonproductive.

Spectral form:

> For every recurrent noncoincident SCC `C`, `PF(N_C) < beta` unless `C` leaks no mass and has no escape.

Boundary normal form:

> No recurrent noncoincident SCC is a nonsynchronizing zero-return trap.

## Retired routes

- Cycle exclusion via `delta != 0` on noncoincident cycles: false.
- Mossé desubstitution descent: blocked because desubstitution can stay inside the same SCC.
- Pure algebra on `N_C`: insufficient because `(N_C, P) = (M_sigma^T, I)` is a synthetic solution.
