# The zero-fibre anchor theorem: proof by a convex window

Base: `ccr-8ce028bb-9bcfrn` at `eb95c7f`, which reduced the anchor
theorem for the literal `σₖ = (1, 0 1^k 2, 001)`, `k ≥ 2`, to the
premise C(k) of the
[reduction note](c4-zero-fibre-anchor-stop-go-2026-11-21.md):

> the only periodic interior lattice tiles of the origin-tile map are
> `(1; 1,0,0)`, `(1; −1,1,0)`, `(1; 0,0,1)`.

**C(k) is now proved in Lean for every `k ≥ 2`**, and with it the anchor
theorem and the all-pairs witness statement, with no premise. Status:
mechanically certified at this scope; independent human review pending.

## Source decision

### Proposed claim

For `k ≥ 2`, any two tilings of the ordinary legal hull over the zero
solenoid history share a labelled tile; equivalently they have the three
exact radius-one agreements with one common translation.

### Prior art and terminology

The [reduction note](c4-zero-fibre-anchor-stop-go-2026-11-21.md)
identified the origin-tile map as a shifted shift radix system for
`x² + θx + 2α`, `θ = β − k = 2α + 2α²`, `α = 1/β`, and named
Frougny–Solomyak's finiteness theorem for non-increasing digits and the
monotone-coefficient results for shift radix systems (Akiyama, Borbély,
Brunotte, Pethő, Thuswaldner) as the closest prior art. Nothing further
was read for this increment.

The argument below is the natural one for monotone coefficients:
`1 ≥ θ ≥ 2α > 0` makes `(1−θ, θ−2α, 2α)` a convex weight vector on tail
sums. I expect the unshifted form of this window argument to be the
published proof of finiteness in the monotone region, but I have not
checked it against the full text, so no novelty is claimed for the
window step. What is specific here is the detrending by `i/3`, which
turns the three-cycle into a constant, and the digit bookkeeping for the
substitution.

### What transfers and what does not

- Transfers: convexity. It needs `θ < 1`, which is `k ≥ 2`.
- Does not transfer: convexity alone. The real inequality admits the
  sequence `1, 1, −1` at `α = 1/3` (Lean control). The child relation of
  the substitution is needed to exclude it.

### Decision

Proceed: prove an abstract theorem about integer sequences, then bind
the tiling to it.

## Work shown

### Assumptions and hypotheses

- `k ≥ 2`. The step lemma and the orbit coordinates hold for `k ≥ 1`.
- The base revision's theorems, including the reduction
  `anchor_common_tile_of_classified`.
- No periodicity is used in the abstract theorem; it describes every
  orbit that stays interior.

### Derivation / reduction

**Coordinates.** Along an orbit of interior lattice tiles `(aᵢ; vᵢ)` put
`wᵢ = (vᵢ)₁`. Then `(vᵢ)₂ = wᵢ₋₁` and `(vᵢ)₀ = wᵢ₋₁ + 2wᵢ₋₂ − dᵢ`, where
`dᵢ`, `eᵢ` count the `0`s and `1`s before the child (`origin_step`,
`orbit_data`). Two facts follow.

1. *Real inequality.* `0 < ℓ·vᵢ < ℓ_{aᵢ} ≤ β²` and `0 ≤ dᵢ ≤ 2` give
   `0 < Eᵢ < 1 + 2α` for `Eᵢ = wᵢ + θwᵢ₋₁ + 2αwᵢ₋₂`.
2. *Digit identity.* `dᵢ + eᵢ₊₁ = k wᵢ + 2wᵢ₋₁ + 2wᵢ₋₂ − wᵢ₊₁`.

**Window (`window`, `R_window`).** Let `R₀ = 0`, `Rᵢ₊₁ = Rᵢ + 3wᵢ − 1`.
With `z, y, x` three consecutive values, newest first,

```text
E = (1−θ)·z + 2α²·(y+z) + 2α·(x+y+z),
```

a combination with positive weights summing to one. If `Rᵢ₊₃` exceeded
`Rᵢ, Rᵢ₊₁, Rᵢ₊₂` then `z ≥ 1`, `y+z ≥ 1`, `x+y+z ≥ 2`, so
`E ≥ 1 + 2α`; if it were below all three then all three sums are `≤ 0`
and `E ≤ 0`. Hence

```text
min(Rᵢ, Rᵢ₊₁, Rᵢ₊₂) ≤ Rᵢ₊₃ ≤ max(Rᵢ, Rᵢ₊₁, Rᵢ₊₂).
```

**Freezing (`eventually_constant`, `frozen`).** The windows are nested
integer intervals, so from some index on their minimum `m` and maximum
`M` are constant. Consecutive values of `R` differ by `3w − 1 ≠ 0` and
values two apart by `3(w+w') − 2 ≠ 0`, so the index carrying `m` in one
window is not in the next two, and the value `m` must recur exactly
three steps later; likewise `M`. Two of the three residue classes of the
index are therefore frozen at `m` and `M`. In terms of `w`, with `b`
running over one class, either

- (I) `w_b = g ≥ 1`, `w_{b+1} ≤ 0`, `w_{b+2} ≤ 0`, sum one; or
- (II) `w_b ≥ 1`, `w_{b+1} ≥ 1`, `w_{b+2} = γ ≤ −1`, sum one.

**Digits (`patternII_false`, `patternI_one`, `patternI_types`).** The
digit identity with `0 ≤ d ≤ 2`, `0 ≤ e ≤ k` bounds the patterns:

- (II) forces `(k−2)(−γ) ≤ 1`, so `k ≤ 3`; the child relation then
  contradicts the forced digits (`k = 3`: `d = 4`; `k = 2`: a type-`2`
  tile would need both `e = 0` and `e = 2`, or a negative digit).
- (I) forces `g ≤ 2`; `g = 2` forces `k ≤ 4` and is excluded the same way.
- (I) with `g = 1` is `w = 1, 0, 0`, and then `d + e` runs through
  `k, 2, 1`, which the child relation satisfies only with every type and
  digit equal to one.

So every interior orbit eventually has `w = 1, 0, 0`, types `1`, digits
`1` (`eventually_cycle`), that is, tiles `(1;−1,1,0)`, `(1;0,0,1)`,
`(1;1,0,0)`.

**Binding (`periodicLatticeOriginsClassified`).** A periodic interior
tile never reaches a vertex, since a vertex persists
(`originChild_vertex_iterate`). Its orbit is therefore interior, and at
a large multiple of the period the tile is one of the three. With the
reduction of the previous increment:

```text
k ≥ 2,  g(T) = g(U) = 0   ⟹   T ∩ U ≠ ∅.
```

### Evidence and replay

Lean modules `PscVerif.ShiftedRadixCycle` (abstract theorem, no hull)
and `PscVerif.C4ParameterFamilyOriginCycle` (binding and endpoints). No
`sorry`; all fourteen audited closures are
`propext, Classical.choice, Quot.sound`.

```sh
cd proof/PscVerif
lake build PscVerif.C4ParameterFamilyOriginCycle
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true \
  ../../evidence/c4-zero-fibre-anchor-proof-2026-11-22/OriginCycleAxioms.lean
```

Endpoints: `anchor_common_tile`, `zero_fibre_common_tile`,
`all_pair_witnesses`, `zero_fibre_exactProximal`, `zero_fibre_origin`.

Mojo, exact and independent of the Lean proof: the box census of the
previous increment is unchanged, and `window_increases` checks that no
origin child in the box has a larger window range.

```sh
cd kernel
mojo run -I . -I tests tests/test_origin_cycle.mojo
```

Receipts: [evidence](../evidence/c4-zero-fibre-anchor-proof-2026-11-22/README.md).

### Negative controls

- Lean `bounded_alone_insufficient`: `1, 1, −1` satisfies the real
  inequality at `α = 1/3` and is never zero. The digit relations are
  needed.
- Mojo, `k = 1`: the window range rises from 2 to 4 at
  `(0;−2,1,0) → (1;1,−1,1)`, and an eight-cycle exists. The hypothesis
  `θ < 1` cannot be dropped.
- Lean `vertex_tile_periodic` (previous increment): strictness of the
  interior condition is needed.
- A first attempt bounded the range only up to exceptional steps and
  planned a multi-step strict-decrease analysis; exact search found
  stalls of eight steps at `k = 2`, so that route was dropped in favour
  of the nested-window statement, which has no exceptional steps.

### Non-claims / remaining gaps

- This is coincidence at the **zero fibre** only. Propagation to every
  fibre, ordinary proximality, the almost-everywhere one-to-one
  statement and the `L²` conclusion are not formalized; they are the
  interfaces 2–4 of the
  [spectral-interface note](c4-zero-fibre-spectral-interface-2026-11-21.md).
- `k = 1` is not covered and the statement is false there in this form.
- Nothing is claimed for substitutions outside the family, and no
  ledger claim changes status.
- Local build and tests only; hosted CI has not run on this revision.
  Independent human review is pending.
