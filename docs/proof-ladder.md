# Proof ladder

## Stable levels

### Level 2: unique decodability

Proved:

1. `det M_sigma != 0` gives letter injectivity.
2. Defect theorem gives unique decodability of the image code `{sigma(a)}`.
3. Unique decodability for powers gives unique supertile hierarchy inside supertiles.

Diagnostic only:

4. Phase automaton bounds coincidence padding by `D(sigma) <= |A|^2 |sigma|_max^2`.
   Only legally-repeatable complete-cutting cycles are excluded; nonzero-offset
   recurrence is uncontrolled (19% empirically).

**Not** proved:

5. ~~Pisot growth gives predecessor contraction and hence finite `B_sigma`.~~
   **Withdrawn.** PSC_PROOF_v5 Theorem 5.1's predecessor-contraction proof is
   false: `beta * L(s') <= L(s) + D` fails, with worst observed ratio 8.0 and
   unbounded excess. See
   `archive/2026-09-08/notes_2026_06/V5_THM51_RETRACTION_VERIFICATION_2026_06_13.md`.
   Finiteness of `B_sigma` is now hypothesis **G1** — see the conjecture ledger.

### Local part of Level 3

Unique hierarchy gives local witness injectivity inside a level-`n` supertile. This is local, not global: finite witness data does not determine an entire bi-infinite tiling.

## Open Level 3

The open step is not cycle exclusion. The correct target is:

> **SCC Producer Theorem.** Every recurrent noncoincident SCC of `B_sigma` produces a coincidence sibling at some inflation step.

Equivalent mass-leakage form in a finite BPA:

> No recurrent noncoincident SCC is closed nonproductive.

Spectral form:

> For every recurrent noncoincident SCC `C`, `PF(N_C) < beta` unless `C` leaks no mass and has no escape.

### Proved graph reduction: only sink nonproductive SCCs matter

Let `NP` be the set of states from which no coincidence state is reachable.
If `v in NP`, every child of `v` is also in `NP`; otherwise a productive child
would make `v` productive. Thus `NP` is forward-closed.

If `B_sigma` is finite and `NP` is nonempty, the condensation DAG of the
induced graph on `NP` has a sink SCC `C`. Because `NP` is forward-closed and
`C` is a sink in its condensation, every child of every state of `C` remains in
`C`. Hence `C` is recurrent, noncoincident, closed, and nonproductive.

Therefore, under G1, proving C1 reduces to ruling out **closed/sink
nonproductive recurrent SCCs**. One does not need boundary synchronization on
every recurrent SCC. See `docs/sink-scc-reduction.md`.

### Boundary route after the reduction

Boundary Synchronization Lemma:

> A synchronizing zero-return boundary produces a coincidence sibling after a
> finite number of further endpoint-map iterates.

Hence a closed nonproductive SCC cannot contain a synchronizing boundary.
Conversely, to kill a hypothetical counterexample it is enough to force one
synchronizing boundary in a sink nonproductive SCC.

`docs/c3-locality-reduction.md` further proves that any higher-inflation newborn
synchronizing cut localizes to a **one-step** newborn synchronizing cut from an
irreducible state of the same closed SCC. Thus the current load-bearing target
is finite and local:

> **C3-local.** Every closed nonproductive recurrent noncoincident PIP SCC
> contains a state `T` such that `sigma(T)` has an interior zero-return cut with
> a synchronizing adjacent endpoint pair.

Exact corpus evidence (`mojo/c3_census.mojo`) over 4554 alphabet-3 PIP
substitutions with image lengths `<= 3`:

- 5022 recurrent noncoincident SCCs, 369486 states;
- 4962 SCCs have one-step newborn synchronization;
- 60 have neither inherited nor newborn synchronization;
- all 60 residual SCCs are singleton SCCs with a noncoincident exit;
- 0 residual SCCs are closed/no-direct-coincidence candidates.

So every local boundary-test failure in the corpus lies outside the sink
counterexample class. This is evidence, not proof.

## Retired routes

- Cycle exclusion via `delta != 0` on noncoincident cycles: false.
- Mossé desubstitution descent: blocked because desubstitution can stay inside the same SCC.
- Pure algebra on `N_C`: insufficient because `(N_C, P) = (M_sigma^T, I)` is a synthetic solution.
- Universal synchronization of every recurrent SCC: unnecessary. Escaping SCCs
  may fail the local boundary test; only closed/sink nonproductive SCCs are
  load-bearing for C1.
