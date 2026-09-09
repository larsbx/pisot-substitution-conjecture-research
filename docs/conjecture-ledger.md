# Conjecture ledger

The machine-checked form of this ledger is `tla/Ledger.tla`; `tla/check.sh`
verifies mechanically which claims are reachable from which hypotheses.

## G1 — finiteness of the balanced-pair automaton

**Statement.** For every primitive irreducible Pisot substitution on a 3-letter
alphabet, `B_sigma` is finite.

**Status.** Open, and it is a *hypothesis*, not a theorem. The
predecessor-contraction proof of PSC_PROOF_v5 Theorem 5.1 is **withdrawn**:
`beta * L(s') <= L(s) + D` is false, worst observed ratio 8.0, excess unbounded.
Finiteness is unconditional only for `|A| = 2` and for verified families.

**Evidence, not proof.** The exhaustive alphabet-3 census over images of length
`<= 3` terminates on 4554/4554 specimens with 0 caps (`mojo/census.mojo`;
reproduces the documented figure). That is elimination over a finite corpus.

**What depends on it.** The v34 Load-Bearing SCC Theorem, and — together with
C1 — the boxed main result. Neither is reachable without it; see
`MCArchitectureOpen` and `MCArchitectureG1Bound` in `tla/`.

## C1 — SCC Producer Theorem

**Statement.** For every primitive irreducible Pisot substitution, every recurrent noncoincident SCC of `B_sigma` produces a coincidence sibling at some inflation step.

**Status.** Open in general. Settled for two-letter case through Hollander--Solomyak. Known for beta-substitution and special families.

**Evidence, not proof.** Every reachable balanced pair reaches a coincidence on
all 4554 alphabet-3 PIP specimens of the census (`mojo/census.mojo`), and the
TLA+ invariant `Productive` holds on Tribonacci, flipped Tribonacci and a
Smith-type substitution. `MCNonProductive` shows the invariant is not vacuous:
it fails for a primitive but non-Pisot substitution.

**Equivalent formulations in the finite-BPA regime.**

- No closed nonproductive recurrent noncoincident SCC exists.
- No sink SCC of the nonproductive subgraph exists.
- No closed diagonal-free zero-return system exists.

The sink-SCC reduction is elementary but important: if any state is
nonproductive, the set of nonproductive states is forward-closed. In a finite
BPA its condensation DAG therefore contains a sink SCC, and that SCC is closed,
recurrent, noncoincident, and nonproductive. Thus C1 only needs a contradiction
on sink/closed nonproductive SCCs; synchronization of every recurrent SCC is
unnecessary. See `docs/sink-scc-reduction.md`.

## C2 — sink-SCC boundary escape

**Statement.** Every closed nonproductive recurrent noncoincident SCC `C` has,
at some inflation step, a zero-return boundary whose right adjacent pair lies
in `Sync_+` or whose left adjacent pair lies in `Sync_-`.

**Status.** Open. This is the boundary normal form needed for C1 in the actual
counterexample regime. It deliberately does **not** require synchronization on
every recurrent SCC: SCCs with noncoincident exits may fail the local boundary
test yet still be productive through the condensation graph.

A synchronizing boundary contradicts nonproductivity by the Boundary
Synchronization Lemma. With G1, the sink-SCC reduction shows that C2 is
sufficient for C1.

## C3 — one-step newborn escape on a closed counterexample SCC

**Statement.** For every closed nonproductive recurrent noncoincident SCC `C`
of a primitive irreducible Pisot substitution, there exists a state `T in C`
such that `sigma(T)` has an interior zero-return cut whose right adjacent pair
lies in `Sync_+` or whose left adjacent pair lies in `Sync_-`.

**Status.** Active next target. `docs/c3-locality-reduction.md` proves that any
higher-inflation newborn synchronizing cut localizes to a one-step newborn cut
inside an irreducible balanced block. Because a closed nonproductive SCC keeps
all such noncoincident blocks inside the SCC, the horizon problem is removed:
C3 is now a one-step existence problem on states of a hypothetical sink SCC.

For an irreducible state, inherited cuts are only the endpoints. In a
nonproductive SCC those endpoint pairs cannot synchronize, since the Boundary
Synchronization Lemma would already give productivity. Thus any synchronizing
interior cut in `sigma(T)` is precisely the needed newborn escape.

**Exact corpus evidence, not proof.** `mojo/c3_census.mojo` scans all 5022
recurrent noncoincident SCCs (369486 states) arising from the exact 4554-member
alphabet-3 PIP corpus with image lengths `<= 3`:

- 4962/5022 SCCs have one-step newborn synchronization;
- 4614 have inherited synchronization;
- 1614 contain a state with newborn synchronization but no inherited hit at
  that state;
- the remaining 60 SCCs have neither lineage synchronizing;
- all 60 residual SCCs are singleton SCCs with a noncoincident exit;
- none has a direct coincidence child, and **0** is closed with no direct
  coincidence.

Therefore every failure of the local boundary test in this exact corpus lies
outside the closed/sink counterexample class. The census is now pinned in CI.
This is finite elimination only; it does not prove C3.

## C4 — finite-pigeon lift on a sink SCC

**Statement.** In a hypothetical closed nonproductive PIP SCC, finite
recurrence of irreducible balanced-pair types together with primitivity/Pisot
structure forces a one-step newborn boundary to leave the nonsynchronizing
endpoint cores.

**Status.** Programmatic. The common-cut recurrence notes provide an analogue
of the finite-pigeon component, but not this theorem. After the sink-SCC and
newborn-locality reductions, this is the main structural route: assume every
interior newborn boundary remains in the finite nonsynchronizing cores and use
recurrence inside one closed SCC to derive a contradiction with the PIP
hypotheses.
