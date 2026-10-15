# Box-walk reachability: target and realization audit (2026-10-15)

**Status:** research audit / claim-neutral correction to [the October 11 box-walk salvage](audit-2026-10-11-boxwalk-extremal.md). No theorem, claim-governance status, ledger node, or closure result is promoted here.

## Decision

Retain the exact prefix-Parikh decomposition and bounded finite-depth observations, but **do not regard reverse reachability to the zero imbalance vector in a projected graph as a certificate of a coincidence child**. A sound proof instrument must certify the target event and the lift of each asserted path to the actual substitution/occurrence dynamics.

The main PSC completion route remains the G1-free, finite seed-patch **overlap productivity** route of [the proof ladder](proof-ladder.md). Box-walk arguments are a parallel attempt at the real-secondary/permutation-first-letter and block-child regimes; they do not replace Open Problem 5.35, G1b-2, #138, or #139.

## 1. Exact local object: cut *before* a matched letter

Let `U,V` be balanced words of equal letter length `N`, and let `pi` be the integer Parikh vector. Define the **aligned-index** difference

```text
Delta(q) = pi(U[0:q]) - pi(V[0:q]),   0 <= q <= N.
```

A **matched-letter zero-return target** is a cut `q < N` satisfying both

```text
Delta(q) = 0,     U[q] = V[q] = a.
```

Then `Delta(q+1)=0` as well, so `[q,q+1]` is an irreducible single-tile balanced child `(a,a)`. Conversely every `(a,a)` child at a balanced factorization cut has this form. This is a simple local equivalence, not a global productivity theorem.

**Ordinary zero return is weaker:** `Delta(q)=0` alone can mark a noncoincident balanced block boundary, or `q=N` where no next letters exist. For `U=12, V=21`, the imbalance returns to zero at `q=2` but there is no matched-letter target anywhere. Recording a transition to the vector `0` does **not** certify a diagonal child.

The older experimental `box_walk_recurrence.py` constructs an imbalance-vector graph and collects some matched-origin information, but its reverse BFS is seeded at the vector `(0,...,0)`, not at the matched-letter event; that numerical “zero stuck nodes” result is **not** a matched-origin certificate. The edge graph also merges transitions collected from different occurrences: a graph path may splice edges that cannot occur consecutively in any single realized inflated pair.

## 2. Separate three graph claims

1. **Bounded observation:** finitely many imbalance vectors/edges were seen through a declared depth and word-size budget. This gives finite evidence only.
2. **Closed transition system:** the complete occurrence-aware successor relation is defined and proved closed under substitution; a finite plateau in sampled vertex/edge sets is *not* this proof.
3. **Productive realizable reachability:** for each seed/state under the claimed quantifiers, an actual finite chain of valid inflation, child selection and matching boundary events witnesses `(a,a)`. A path in a projection graph is sufficient only if a lifting theorem or a replayed occurrence-address witness establishes that path is realizable.

Existential reachability (`there exists` a valid path to a diagonal child) is sufficient for existence-of-coincidence productivity as defined in the applicable model. It must not be conflated with *unavoidable* hitting on every infinite walk. Off-target cycles can coexist with paths to a target. Conversely a cycle carrying an escape edge does not force arbitrary walks to take the escape edge.

If proving **all-child productivity** or coincidence density, record that stronger quantifier separately; seeing a single diagonal child in one inflation does not, by itself, prove every descendant productive, BPA termination in every sense, or PDS.

### Corrected conditional certificate

For a specified finite target-aware occurrence system `G`, a complete and checked finite successor relation plus (i) a genuine realized starting state/seed and (ii) a **replayable target-reaching occurrence path** provides a finite witness to a coincidence child. To upgrade to a universal statement, prove the state/seed coverage and the semantics-preserving connection to the PSC overlap/BPA object. A mere bound `||Delta|| <= R`, vector-graph saturation claim, or vector-only BFS does not discharge any of those prerequisites.

A graph quotient is useful for early rejection or exploration if it is marked as an overapproximation; accepting a positive witness requires lifting/replay. If finite graph *closure* itself is unproved, “saturated” may not be used as a proof-status word.

## 3. What remains valid from the thread

For `U=sigma(u), V=sigma(v)` at an aligned child cut `q`, decompose each cut into completed parent images (`p_U,p_V` completed letters) and a proper partial current image. Then

```text
Delta_UV(q) =
    M * (pi(u[:p_U]) - pi(v[:p_V]))
    + pi(partial_U(q)) - pi(partial_V(q)).
```

For nonerasing images of maximum length `L`, each partial term is a nonnegative Parikh vector of fewer than `L` letters; each coordinate of their difference has absolute value at most `L-1`. This bound is **not** a bound on the completed term or on the inflated radius. In general `p_U != p_V`, and their off-diagonal completed difference is not an aligned parent imbalance.

Retain the negative-controls and the “observed versus proved” distinction of the October 11 audit: no spectral contraction-to-zero, no `L`-dense common-boundary assumption, no child-box set inclusion, no sampled closed-form maximum, no depth-plateau-as-closure.

### Scope of the radius-ten replay

The canonical [exact replay](../evidence/boxwalk-radius8-depth9.json) for `sigma=(001,22,220)`, seed `01|10`, measures **aligned-prefix** radius through depth 9 and finds 10 at cut 9054, difference `(5,5,-10)`, following a depth 6–8 plateau of 8. It does **not** prove a saturated radius or an extremum over an image family. The exact characteristic polynomial of its incidence matrix is `x^3 - 4x^2 + 4x - 2` with nonreal secondary conjugates (approximately `0.5803566 +/- 0.6062907 i`). Thus it does not, on its own, refute a *real-secondary-only* radius bound. The historical staircase/comp observable also requires its own separate definition and replay.

This is a negative control for premature stopping and cross-observable/régime transfer, not a proof of a global growth law.

## 4. Next executable obligation (Mojo-first; not implemented here)

A future theorem-facing instrument should include:

- **Exact state key:** the imbalance, aligned paired read heads or occurrence-address/cut context, and pending letter pair or equivalent data sufficient to decide valid successors and the matched target. Do not silently merge incompatible histories.
- **Soundness/lifting:** each graph edge replays as an actual inflated, balanced child occurrence; multi-edge paths must compose with compatible addresses. If using a quotient, supply a lifting theorem or a separate witness search.
- **Target fidelity:** `Delta(q)=0 && U[q]==V[q]` at a valid cut. Distinguish it from a zero vector, terminal cut, mismatched balanced return, or ordinary cycle.
- **Completeness/closure:** an explicit finite carrier with a *proved* successor closure, not equality of two sampled depth slices.
- **Quantifier coverage:** state whether the goal is “one seed produces a diagonal,” “every reachable state eventually produces one,” or “all reachable overlaps are productive”; do not interchange them.
- **Fail-closed budgets:** `BUDGET_EXHAUSTED`, `DEPTH_COMPLETE_NO_CLOSURE`, `NO_MATCHED_TARGET_WITHIN_BUDGET`, and `CERTIFIED_LIFTABLE_TARGET_PATH` must be distinguishable.
- **Negative controls:** `12|21` (terminal zero only), the depth-9 radius-ten witness (late new radius), and a two-context projected graph whose mixed edges suggest a spurious path. The latter is a test specification, not an already-verified fixture.

Implement canonical code and tests in `kernel/psc/` and `kernel/tests/` only after the repository's literature/claim gate. Keep Python as an independent oracle. Use existing exact seed-patch overlap graph and target-aware packet infrastructure when possible rather than introducing an unjustified new quotient.

## 5. What this does not establish

No general SSC/PSC, SCC Producer, G1, renewal finiteness, uniform box radius, saturation bound, or overlap productivity is proved. The thread's 0-stuck statistics are retained as vector-graph observations only; they cannot presently support a theorem-facing matched-origin reachability claim. No change to the authoritative proof ladder or generated claim records follows from this audit.
