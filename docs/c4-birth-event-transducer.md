# C4 newborn birth-event transducer

**Status:** exact finite normal form for newborn zero-return creation in a given finite strict component. It does **not** prove C4, C1, G1, or PSC.

## 1. Why birth events, not persistent misalignment

PR #29 proves that an interior zero return born inside the image of an irreducible balanced state is misaligned with at least one level-1 `sigma` source-image grid. But once that same physical balanced boundary is inflated again, it is inherited: it is the image of a whole balanced prefix and is therefore aligned with source-image boundaries on both sides.

So the correct recurrent object is **not one physical cut that stays misaligned forever**. It is the finite type of the many newborn cuts created at successive levels.

PR #32 makes this precise. For a strict component `C`,

```text
tau_C(T) = ordered normalized children of sigma(T)
```

and every depth-`n` newborn boundary is an internal split of one occurrence of `tau_C(S)` for some state `S` appearing in `tau_C^(n-1)(T)`.

## 2. One-step newborn birth event

For each parent `T in C` and each internal split

```text
tau_C(T) = R_1 ... R_j | R_(j+1) ... R_m,
```

there is a canonical physical cut in `(sigma(u_T),sigma(v_T))` after the first `j` child blocks.

`src/psc_research/birth_event.py` records the following finite data for that split:

- parent `T` and split index `j`;
- adjacent normalized child states;
- raw-to-normalized orientation signs of those two child occurrences;
- asynchronous source-prefix defect `E`;
- local correction digit `c_sigma`;
- top/bottom source indices and within-image offsets;
- the letters immediately to the left and right of the balanced boundary on both sides;
- whether the left endpoint pair synchronizes under `sigma_-`;
- whether the right endpoint pair synchronizes under `sigma_+`.

This is the **newborn birth-event type**.

Because `C` is finite and every `tau_C(T)` is finite, there are only finitely many such types.

## 3. Completeness at every depth

Let

```text
W = tau_C^(n-1)(T) = S_1 ... S_k.
```

Then

```text
tau_C^n(T) = tau_C(S_1) ... tau_C(S_k).
```

By the inherited/newborn characterization from PR #32, the newborn boundaries at depth `n` are exactly the internal boundaries inside these displayed words `tau_C(S_i)`.

Therefore every depth-`n` newborn boundary is an occurrence of exactly one one-step key

```text
(S_i, split_index).
```

Conversely every internal split of every displayed `tau_C(S_i)` is a depth-`n` newborn boundary.

Hence the one-step catalog is a **complete alphabet of newborn creation events at all depths**. `newborn_occurrences` checks this against the exact derived newborn boundary indices.

## 4. Endpoint condition forced by strictness

Suppose `C` is genuinely strict and child-closed: no descendant child is a coincidence and every noncoincident child remains in `C`.

Take any newborn event. If its right adjacent letter pair belongs to `Sync_+`, repeated inflation of that boundary eventually makes the right endpoint letters coincide. The Boundary Synchronization Lemma then produces a single-tile coincidence factor. The same holds on the left using `Sync_-`.

Either outcome contradicts strict child closure.

Therefore every newborn event of a hypothetical strict counterexample must satisfy

```text
left endpoint pair  notin Sync_-
right endpoint pair notin Sync_+.
```

This is only a **necessary** condition. It is the local event form of the current C4 obstruction, not a proof that such a strict component cannot exist.

## 5. Calibration

For the repository's primitive non-Pisot strict component

```text
sigma:
1 -> 2
2 -> 123
3 -> 2

A=(12,21)
B=(23,32)

tau_C:
A -> A B
B -> A B,
```

there are exactly two one-step newborn types:

```text
(A, split 1)
(B, split 1).
```

The `A` event has signed neighboring children

```text
A^- | B^+
```

and endpoint pairs

```text
left  (1,2),
right (2,3).
```

The `B` event has

```text
A^+ | B^-
```

with endpoint pairs

```text
left  (2,1),
right (3,2).
```

All four endpoint pairs remain nonsynchronizing under the appropriate endpoint maps. At derived depth three, the newborn boundary indices are

```text
1,3,5,7
```

and their event keys are

```text
(A,1), (B,1), (A,1), (B,1).
```

The regression suite pins this exact periodic countermodel. Thus finite birth-event recurrence plus endpoint nonsynchronization is still possible outside the Pisot regime.

## 6. Relation to dual recognizability

PR #31 supplies legal finite `sigma`-contexts around suitably chosen deep cuts. PR #33 supplies recognizability of the period-decimated derived hierarchy in the PIP regime. The present event catalog sits exactly between them:

```text
derived internal split
      |
      v
newborn birth-event type
(parent, split, orientation, E, offsets, endpoint pairs)
      |
      v
local sigma cut context.
```

A recurrent C4 obstruction therefore reduces to recurrent occurrences of finitely many birth-event types, each with nonsynchronizing endpoints, embedded in two locally recognizable hierarchies.

## 7. Next target

The remaining quantity should be an **address cocycle** attached to a birth-event occurrence: as the occurrence is viewed through higher `tau_C` supertiles, record where its physical cut sits in the top and bottom `sigma` supertile hierarchies.

The next theorem should seek a dichotomy:

```text
recurrent nonsynchronizing birth-event address
    => eventually derived-inherited / sigma-aligned
       or a synchronizing boundary.
```

Any proof must use more than finite recurrence; the non-Pisot calibration above supplies a periodic nonsynchronizing event cycle.
