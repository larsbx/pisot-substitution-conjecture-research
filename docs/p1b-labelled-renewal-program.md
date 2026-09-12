# P1-B — labelled renewal program for G1b-2

**Status:** executable support program for the open renewal-finiteness gate. The labelled-word, level-scaled address, and bounded joint-local layers below do **not** prove G1b-2 or G1.

## 1. Why the cumulative difference walk is insufficient

For an equal-length word pair `(u,v)`, define

```text
d_k = Parikh(u[:k]) - Parikh(v[:k]).
```

A balanced irreducible pair is a first return of this walk to zero: `d_0=d_n=0` and `d_k!=0` for `0<k<n`.

However the sequence `(d_k)` does not determine the pair. A diagonal letter step `(a,a)` has zero increment for every `a`, so the label is invisible in the cumulative walk.

The canonical regression is

```text
A = (001,100)
B = (021,120).
```

Both are irreducible balanced pairs with exactly the same difference path

```text
0 -> (1,-1,0) -> (1,-1,0) -> 0,
```

but the middle transition is `(0,0)` in `A` and `(2,2)` in `B`.

Therefore any G1b-2 proof that quotients realizable states to the unlabelled difference walk loses information required to reconstruct the state.

## 2. Canonical Mojo labelled-return representation

`mojo/psc/renewal.mojo` stores one labelled return word as:

- one packed transition label `3*top+bottom` in `0..8` per aligned position;
- the cumulative difference path as one flat `Int` array of coordinate triples;
- one exact first-return flag.

The constructor streams the word once. It does not allocate Parikh vectors, prefix slices, or per-vertex heap objects.

`LocalRenewalType` records the radius-one datum

```text
(d_k, incoming_label, outgoing_label)
```

for an interior difference vertex. This is the minimal labelled refinement of the local configurations referred to in the current G1b-2 audit.

## 3. Mathematical boundary of the labelled layer

The representation solves only an **information-loss problem**. It does not imply that the set of labelled return words is finite.

The known obstruction remains: a first-return word can revisit a finite set of nonzero difference vertices and local configurations many times before returning to zero.

Thus the next theorem must constrain which long labelled returns are **realizable under substitution renewal**, not merely which local transitions are combinatorially legal.

## 4. Level-scaled symbolic renewal address

`mojo/psc/renewal_address.mojo` adds exact substitution ancestry for an interior zero-return cut of `sigma^d(u), sigma^d(v)` without materializing those inflated words.

The cut is located inside one source supertile on each side and then descended through one substitution child at each level. Each side retains a finite symbolic digit path

```text
(parent_letter, child_index)^d.
```

Absolute source indices and inflated word length are deliberately omitted from the public relative address. What remains is:

- substitution level `d`;
- relative source-index displacement;
- exact source prefix defect `delta`;
- the two source letters;
- the two ordered digit paths;
- the level-scaled defect `M^d delta`;
- the finite partial-image correction `c`.

For an actual zero-return cut the module verifies the exact integer certificate

```text
M^d delta + c = 0.
```

This identity is the current executable meaning of a **level-scaled address**. It uses no inverse of `M` and no choice of Archimedean/non-Archimedean completion.

For census use, the implementation has two reusable preparation layers:

- `RenewalAddressTables` precomputes image lengths and image Parikh columns once for a substitution/depth;
- `RenewalPairCensusState` validates one labelled first return and caches source-supertiling boundaries and prefix Parikh vectors once.

Per-cut queries then use binary source lookup plus the level-linear digit descent rather than re-expanding words or rebuilding labelled paths.

## 5. Explicit non-unimodular regression

The canonical address tests include

```text
0 -> 1
1 -> 021
2 -> 001
```

with incidence matrix

```text
M = [[0,1,2],
     [1,1,1],
     [0,1,0]],
```

so `det M = 2`. Its characteristic polynomial is

```text
x^3 - x^2 - 2x - 2,
```

and the example is primitive irreducible Pisot. For the first-return pair `(001,100)`, the level-one interior renewal cut at position `4` has

```text
delta = (1,-1,0)
M delta = (-1,0,-1)
c       = ( 1,0, 1),
```

hence the certificate closes exactly. The inherited level-two cut is also pinned.

This regression exists specifically to prevent a later implementation from silently introducing `|det M|=1` through division, a Euclidean lattice model, or an inverse-incidence address.

## 6. Address data does not replace labels

The relative address is an auxiliary coordinate, not a state quotient.

For the two labelled collision words

```text
A = (001,100)
B = (021,120),
```

the non-unimodular regression above gives the same relative level-one address at their corresponding inflated renewal cuts, even though their labelled first-return words are different.

Therefore the canonical object for continuing G1b-2 work must retain **both**:

```text
labelled first-return data + relative level-scaled address.
```

Any proposal that discards the labelled word because the address matches is rejected by the tests.

## 7. Non-unimodular firewall

No address introduced by this program may assume:

- `|det M|=1`;
- purely Euclidean internal space;
- discreteness of `pi_s(Z^A)` by itself;
- finite return types merely because the integer certificate is bounded.

If the correct arithmetic completion has a profinite/non-Archimedean factor, it must remain first-class. The symbolic digit paths are intentionally representation-neutral so they can later feed the appropriate product completion rather than prejudging it.

## 8. What remains open

The exact identity

```text
M^d delta + c = 0
```

is necessary structure, not the renewal-finiteness theorem. As `d` varies, digit strings may still grow without bound.

The next mathematical target is now sharper:

```text
bounded discrepancy
+ realizable labelled first returns
+ exact substitution-digit ancestry
=> a uniform-discreteness / finite-local-return statement across all levels.
```

The executable program should census **joint labelled-address local types**, retain counterexamples to proposed identifications, and identify which additional arithmetic coordinate is required in the non-unimodular case. A profinite valuation/residue coordinate is admissible; replacing it by an unjustified Euclidean lattice is not.

## 9. Bounded joint-local falsification layer

`mojo/psc/joint_local_type.mojo` tests candidate finite local projections rather than assuming one is complete. For fixed source radius `r` and digit-window size `w`, it retains:

- relative source-index displacement;
- exact source prefix defect;
- the two selected source letters;
- radius-`r` source-letter context on both sides, with one exterior sentinel;
- the first `w` and last `w` symbolic digit pairs on both sides.

It intentionally omits absolute indices, total inflated length, substitution depth, `M^d delta`, the correction vector, and the middle of a long digit path. For fixed `r,w` the stored context/window size is depth-independent, making this a legitimate candidate finite local type once the already-bounded defect alphabet is supplied.

The canonical tests record two opposite facts.

### 9.1 Full level-one address can still be too coarse

For

```text
A = (001,100), cut 4
B = (021,120), cut 6,
```

under the determinant-2 Pisot substitution above, the **entire** level-one relative address agrees. With source radius `0`, the selected source letters also agree, so the joint projection collides even with `w=1`, which at depth one retains the full digit path.

Radius `1` separates this particular collision because it sees the preceding source letters

```text
A: 0/0
B: 2/2.
```

This proves only that immediate source context repairs this example. It does not prove radius one sufficient in general.

### 9.2 One-level head/tail windows can miss middle ancestry

For the strict pair

```text
(01,10)
```

at substitution depth `4`, the certified zero returns at cuts `35` and `40` have different full symbolic addresses. However:

- the source pair and selected source positions are the same;
- radius `2` already exposes the complete two-letter source words plus sentinels;
- the first one and last one digit pairs on both sides agree.

Thus the `(r=2,w=1)` joint projection still collides even though the full addresses differ. A two-level head/tail window separates this particular pair of cuts.

Again, this is a falsification/calibration result, not a universal bound. The required window could grow, or a different arithmetic coordinate could be necessary.

## 10. Acceptance criteria for the current support layers

- exact labels survive collisions of the cumulative difference path;
- strict first-return input validation fails closed, including the empty word;
- local labelled types are reproducible in canonical Mojo tests;
- inflated zero-return addresses are computed without materializing inflated words;
- the integer certificate `M^d delta + c = 0` is verified exactly;
- a determinant-2 Pisot substitution is a canonical regression;
- relative-address collisions do not erase labelled distinctions;
- bounded joint-local projections retain explicit collision counterexamples;
- positive refinements are recorded only as example-level separations, never as completeness claims;
- no current module makes a finiteness claim;
- further work must prove a uniform finite-local-return/discreteness statement or identify the missing non-Archimedean coordinate rather than infer finiteness from a bounded empirical window.
