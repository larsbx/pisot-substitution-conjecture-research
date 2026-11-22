# The zero-fibre anchor theorem as an origin-tile recurrence

Base: `codex/psc-zero-fibre-witnesses-20261121` at
`7258dccf1265243c67c62c3979272507c8957c25`, for the literal
`σₖ = (1, 0 1^k 2, 001)`, `k ≥ 2`. The obligation left by the
[zero-fibre witness increment](c4-zero-fibre-witness-review-2026-11-21.md)
is the anchor theorem:

> every legal inflation-periodic `U` whose origin-tile start lies in
> `−ℓ(ℤ³)` shares a labelled tile with one fixed zero-fibre anchor `V`.

This note records the 21 November reduction from the anchor theorem to a
classification of periodic integer vectors. The 22 November follow-up
proves C(k) in Lean for every `k ≥ 2` and derives the anchor theorem and
all-pairs witnesses. [Convex-window proof](c4-zero-fibre-anchor-proof-2026-11-22.md)

## Source decision

### Proposed claim

Notation: `β` is the real root of `x³ − kx² − 2x − 2`, `α = 1/β`,
`ℓ = (β, β², β+2)`, `M` is the incidence matrix with `ℓM = βℓ`. A *placed
tile* is `(a; v)`, `v ∈ ℤ³`: type `a`, start `−ℓ·v`. It is *interior* when
`0 < ℓ·v < ℓ_a`. The *origin child* of `(a; v)` is the child of `σₖ(a)`
whose support contains the origin, `(b; Mv − P(p))` with `p` the prefix of
`σₖ(a)` before that child and `P` the letter count.

**Premise C(k).** The only interior placed tiles that are periodic under
the origin-child map are `(1; 1,0,0)`, `(1; −1,1,0)`, `(1; 0,0,1)`.

**Claim.** For `k ≥ 2`, C(k) implies the anchor theorem, hence the
all-pairs witness statement of the previous increment.

### Prior art and terminology

- The origin-child map is a *shift radix system* in disguise. Write
  `w_i` for the middle coordinate of the `i`-th tile of an orbit. Then
  the third coordinate is `w_{i−1}`, the first is
  `w_{i−1} + 2w_{i−2} − d_i` with `d_i ∈ {0,1,2}` the number of `0`s in
  the prefix, and the start satisfies

  ```text
  ℓ·v_i / β² = w_i + θ w_{i−1} + 2α w_{i−2} − α d_i,   θ = β − k = 2α + 2α²,
  ```

  because `x³ − kx² − 2x − 2 = (x − β)(x² + θx + 2α)`. Interior means this
  number lies in `(0, ℓ_a/β²)`, an interval of length at most one, so
  `w_i` is a floor of a linear form in `(w_{i−1}, w_{i−2})` with a shift.
  On type-`1` tiles the real dynamics is `s ↦ βs + 1 − α (mod 1)`.
- Shift radix systems `τ_r(z) = (z₂,…,z_d, −⌊r·z⌋)` and their finiteness
  property are the subject of Akiyama, Borbély, Brunotte, Pethő and
  Thuswaldner, *Generalized radix representations and dynamical systems
  I*, Acta Math. Hungar. 108 (2005)
  ([author copy](https://www.math.tsukuba.ac.jp/~akiyama/papers/srs05.pdf)),
  and the survey of Kirschenhofer and Thuswaldner
  ([arXiv:1312.0386](https://arxiv.org/pdf/1312.0386)). Variants with a
  shifted floor are Surer's ε-shift radix systems, Publ. Math. Debrecen
  74 (2009), 19–43
  ([paper](https://publi.math.unideb.hu/paper/1349/download/10_5486_PMD_2009_4194.pdf)).
- The strongest relevant theorem is Frougny and Solomyak, *Finite
  beta-expansions*, Ergodic Theory Dynam. Systems 12 (1992), 713–723
  ([journal page](https://core-prod.cambridgecore.org/core/journals/ergodic-theory-and-dynamical-systems/article/finite-betaexpansions/E300693B74A59CA5E92E1A1A5F87A667)):
  when the β-expansion of 1 is finite with non-increasing digits, every
  non-negative element of `ℤ[1/β]` has a finite greedy expansion
  (property (F)). For `k ≥ 2` the expansion of 1 here is `k,2,2`.

Read for this decision: the abstract of Frougny–Solomyak, the statement
of their criterion as quoted by later authors, the definitions in the
survey and in Surer's abstract. The full text of the three papers was
not read, and no statement below depends on a theorem from them.

### What transfers and what does not

- Transfers: the conjugate contraction. The quadratic factor has
  monotone coefficients `1 ≥ θ ≥ 2α > 0` exactly when `k ≥ 2`
  (`θ < 1` fails at `k = 1`), which is the Frougny–Solomyak regime and
  the regime where C(k) is observed.
- Does not transfer: property (F) is a statement about the greedy map
  `t ↦ βt (mod 1)` and orbits ending at `0`. The origin-child map is the
  shifted map above, with excursions through tile types `0` and `2`, and
  its lattice orbits end in a three-cycle or at a vertex. No reduction of
  C(k) to (F) was found; the tile cut at the three cycle points is not a
  concatenation of β-numeration tiles (the middle piece has length
  `(k−2)β + 2α`).
- An argument through the maximal equicontinuous factor (Veech,
  Barge–Kellendonk) would give the anchor theorem without C(k); it was
  judged out of reach for this increment and is not attempted.

### Negative controls known before coding

- `k = 1`: `(1; 0,0,1)` inflates to a type-`2` tile, the three-cycle does
  not exist, and an eight-cycle of interior tiles replaces it.
- The premise needs strictness: `(1; 0,0,0)` is periodic and is not one
  of the three tiles.
- An interior tile can inflate to a vertex: `ℓ·(−1,0,1) = 2` and `2β` is
  the start of the third child of `σₖ(2)`. A first draft of this note
  assumed the contrary; the exact census refuted it.

### Decision

Proceed, narrowed. Formalize the reduction of the anchor theorem to
C(k) and the vertex case outright; state C(k) as a named proposition,
never as an axiom; confirm C(k) by an exact box census; leave the proof
of C(k) for all `k ≥ 2` open and say so.

## Work shown

### Assumptions and hypotheses

- `k ≥ 2` throughout the anchor statements; the origin-child lemmas hold
  for every `LengthSubst`.
- Everything is derived from the theorems already on the base revision:
  the zero-fibre characterization, `common_tile_trans` (its middle
  tiling is arbitrary), the seam anchor, the interior cycle and its
  coincidence with the anchor, and the seam pair's common tile.
- C(k) (`PeriodicLatticeOriginsClassified k hk`) is a hypothesis of the
  three conditional theorems and of nothing else.

### Derivation / reduction

1. *The origin tile of an inflation is a function of the origin tile.*
   `tileAt_inflate` puts the origin tile of `ΦU` among the children of
   the origin tile of `U`; `place_unique` identifies it. So
   `origin(ΦⁿU) = originChildⁿ(origin U)`, and `ΦⁿU = U` makes the origin
   tile periodic (`origin_inflateH`, `originChild_periodic_of_periodic`).
2. *Vertex case, no premise.* Let `g(U) = 0` and `(a, 0) ∈ U`. The first
   child of a tile starts where its inflation starts and is never of
   type `2`, so a tile at the origin of an inflation-periodic tiling has
   type `0` or `1` (`origin_vertex_ne_two`). If `a = 1` the tile `(1,0)`
   is shared with the anchor `V`. If `a = 0` it is shared with `ΦV`,
   since `σₖ(1)` begins with `0`; `V` and `ΦV` share `(1, ℓ₀+ℓ₁)`
   (`seam_pair_common_tile`); `common_tile_trans` gives a tile shared by
   `V` and `U` (`anchor_common_tile_of_origin_vertex`).
3. *Interior case.* If the origin tile of `U` is one of the three
   phases, `U` shares that tile with the corresponding phase of the
   interior cycle, which shares a tile with `V`; transitivity again
   (`anchor_common_tile_of_interior_phase`).
4. *Assembly.* If the origin start of `U` is `0`, use step 2. Otherwise
   it is negative, the origin tile is periodic by step 1 and has a
   lattice start by the characterization, C(k) puts it among the three
   phases, and step 3 applies (`anchor_common_tile_of_classified`). Two
   anchor coincidences and transitivity give the all-pairs statement
   (`all_pair_witnesses_of_classified`,
   `zero_fibre_exactProximal_of_classified`).

So for `k ≥ 2`, on the base revision's definitions,

```text
C(k)  ⟹  ∀ T U, g(T) = g(U) = 0 → WindowWitnesses 1 T U.
```

The converse is not claimed.

### Evidence and replay

Lean, module `PscVerif.C4ParameterFamilyZeroFibreAnchor` (16
declarations, no `sorry`; every `#print axioms` closure is
`propext, Classical.choice, Quot.sound`):

```sh
cd proof/PscVerif
lake build PscVerif.C4ParameterFamilyZeroFibreAnchor
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true \
  ../../evidence/c4-zero-fibre-anchor-2026-11-21/AnchorAxioms.lean
```

Mojo, exact census of the origin-child map. Every comparison is a
Sturm–Tarski sign query for `2w₂ + (w₀+w₂)x + w₁x²` at `β` on the
isolating bracket `(k, k+2)`; no floating value is used.

```sh
cd kernel
mojo run -I . -I tests tests/test_origin_cycle.mojo
mojo run -I . c4_family_origin_cycles.mojo
```

Finite object: for each `k = 1..12`, all interior tiles `(a; v)` with
`|v_i| ≤ 8` (551 tiles at `k = 2`, 341 at `k = 12`), each followed to its
cycle with step cap 4096. Result: for `k = 2..12` the cycles reached are
the vertex cycle `(0;0,0,0) → (1;0,0,0)` and the three-phase cycle, and
no other. The corrected maxima for `k = 1..12` are `44, 18, 11, 8, 7,
6, 5, 6, 5, 5, 5, 5`. Each counts the steps to the first cycle tile.
At `k = 2`, `(1;8,2,-8)` first reaches `(1;-1,1,0)` on step 18.
[Corrected census and digests](../evidence/c4-zero-fibre-anchor-proof-2026-11-22/README.md)

Fail-closed behaviour (refuse to conclude): an orbit past the step cap,
a coordinate outside the packed range, a parameter outside `1..64`, a
bracket that does not isolate `β`, and a tile with no child or two
children at the origin all raise. For a step-cap failure, the driver
exits before printing a row for that parameter.

### Negative controls

- Lean `vertex_tile_periodic`: `(1, 0)` is periodic of period two, so
  the strict inequality in C(k) cannot be dropped.
- Lean `interior_phase_periodic`: the first phase satisfies every
  hypothesis of C(k); the premise is not vacuous.
- Mojo, `k = 1`: the box reaches one interior cycle, of length eight,
  and `(1;0,0,1)` inflates to `(2;1,0,0)`.
- Mojo: `(2;−1,0,1)` is interior and inflates to the vertex `(1;0,0,0)`.
  "Inflation keeps the origin interior" is false.
- Scratch, not evidence: a floating-point search at 40 digits found the
  same cycles for `k = 1..6` on `|v_i| ≤ 7` before the exact census
  existed. It is superseded by the Mojo census and is not in the
  repository.
- A sup-norm bound from the conjugate recurrence, `|w_i| ≤
  (θ+2α)·max|w| + 1 + 2α`, contracts only for `k ≥ 4`. The follow-up
  uses nested integer windows and covers `k = 2` and `k = 3` as well.

### Non-claims / remaining gaps

- The census certifies starting tiles in `|v_i| ≤ 8` for `1 ≤ k ≤ 12`.
  Lean's `periodicLatticeOriginsClassified` supplies the classification for
  all integer coordinates and all `k ≥ 2`. [Convex-window proof](c4-zero-fibre-anchor-proof-2026-11-22.md)
- Merged #650 proves the measured real translation theorem for `k ≥ 2`
  via the finite-automaton witnesses. The recurrence proof supplies a second
  derivation of the zero-fibre witnesses. [PR #650](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/650)
- Independent human review of the recurrence reduction and proof is pending.
