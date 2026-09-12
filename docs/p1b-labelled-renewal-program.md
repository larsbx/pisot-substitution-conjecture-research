# P1-B — labelled renewal program for G1b-2

**Status:** first executable support layer for the open renewal-finiteness gate. This note and its Mojo kernel do **not** prove G1b-2 or G1.

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

## 2. Canonical Mojo representation

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

## 3. Mathematical boundary

The representation solves only an **information-loss problem**. It does not imply that the set of labelled return words is finite.

The known obstruction remains: a first-return word can revisit a finite set of nonzero difference vertices and local configurations many times before returning to zero.

Thus the next theorem must constrain which long labelled returns are **realizable under substitution renewal**, not merely which local transitions are combinatorially legal.

## 4. Next executable layer

The next Mojo module should add level/substitution ancestry to a labelled return without expanding the state into a Python-style object graph. Candidate data are:

- current packed transition label;
- exact difference vertex;
- substitution level / local image address;
- finite source-letter prefix/suffix address;
- renewal-cut ancestry needed to distinguish repeated visits to the same local type.

The goal is to expose a level-scaled address on realizable first returns, then test finite-return / uniform-discreteness conjectures against exact counterexamples.

## 5. Non-unimodular firewall

No address introduced by this program may assume:

- `|det M|=1`;
- purely Euclidean internal space;
- discreteness of `pi_s(Z^A)` by itself.

If the correct arithmetic completion has a profinite/non-Archimedean factor, it must remain first-class.

## 6. Acceptance criteria for this support layer

- exact labels survive collisions of the cumulative difference path;
- strict first-return input validation fails closed;
- local labelled types are reproducible in canonical Mojo tests;
- the module makes no finiteness claim;
- further work extends this representation rather than falling back to an unlabelled difference graph.
