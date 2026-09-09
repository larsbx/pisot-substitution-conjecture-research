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

**Executable diagnostics.** The Python reference kernel now tracks boundary
lineage exactly from one inflation to the next: an inherited cut is the image
of a previous zero-return cut, and every other zero-return cut is classified as
newborn. `newborn_boundary_sync_hits` and `inherited_boundary_sync_hits` test the
two lineages separately. A Smith-type regression witness has nonsynchronizing
inherited endpoints at the first inflation while newborn cuts at positions 3
and 4 synchronize. This is finite evidence for the C3 mechanism, not a proof of
C3. The next computational obligation is to port this lineage classification
to the exact Mojo PIP census rather than rely on named examples or
primitive-like random sweeps.

## C4 — finite-pigeon lift

**Statement.** Finite recurrence of boundary types, combined with primitivity, forces newborn boundary escape from the nonsynchronizing cores.

**Status.** Programmatic. The common-cut recurrence notes provide an analogue of the finite-pigeon component, but not this theorem.
