# Unique partners at coincidence rank two, under the vertex-asymptote condition

**Status:** Written proof of a conditional exclusion, with its finite core
machine-checked in Lean (`PscVerif.UniquePartnerLetters`). The exclusion
assumes the vertex-asymptote condition (NM_V) of the
[round-4 note](c4-round4-2026-11-17.md#31-setting), §3.1. Independent
review is pending. This note does not exclude strict systems at rank two,
and it does not settle C4 or PSC. No governed claim changes.

## Targeted literature stop/go check

The target is the case left open by (W4) of
[Theorem W](c4-rank-two-wall-2026-11-16.md#62-statement). There, every
tiling may have exactly one strict partner: that is the unit case with
first-defect degree `r = 3m`, which is the neutral-weight case of the
[seam-ceiling note](c4-neutral-rank-seam-ceiling-2026-11-18.md).

This note imports no new external result. It uses the following:

| Source | Used for | Gate |
| --- | --- | --- |
| Theorem W, (W1) and (Z1)–(Z4) | the unique strict component `Z`: compact, invariant under the flow, `Φ × Φ` and the swap; no tile shared at any level; a `Φ`-periodic pair with a common vertex at the origin (Z3) | [rank-two wall stop/go](c4-rank-two-wall-stop-go-2026-11-16.md) |
| Lemma 7 (1)–(3) of the (F)-class note | the Barge–Diamond eventual-range graph `ER` is connected, and `dim H¹ = 3 + β₁(ER)` | [(F)-class literature](c4-geometric-f-class-literature-2026-11-16.md) (BD08 Theorem 4) |
| B15 Theorem 22 | odd norm and `cr = 2` force `dim H¹ ≥ 2d − 1 = 5` | the same two gates |
| Round-4 note §3, (NM_V) and Lemma A | where periodic asymptotic tilings must branch at the origin: always when `g_R` (resp. `g_L`) is injective; not in general (Fibonacci control, §3.5) | [round-4 stop/go](c4-round4-2026-11-17.md#1-targeted-stopgo) |

The sources were not re-read for this note. **Decision: proceed.**

## Work shown

### Assumptions and hypotheses

- `σ ∈ PIP3` with `cr(σ) = 2` and a strict system.
- `Z` is the strict component of Theorem W. A *partner* of `T` is any `T′`
  with `(T, T′) ∈ Z`.
- `ER` is the Barge–Diamond graph on vertices `x⁺` (the right end of a tile
  `x`) and `y⁻` (the left end of `y`), with one edge `x⁺ — y⁻` for each
  legal bigram `xy` whose letters are periodic under the last- and
  first-letter maps `g_R` and `g_L` (Lemma 7(1)).
- `L` and `R` are its sets of left and right letters.
- For an edge `e = xy`, `T_e` is the `Φ`-periodic tiling with a vertex at the
  origin, `x` ending there and `y` starting there.
- **(NM_V)** (round-4 §3.1): a member of the zero fibre that is
  right-asymptotic (resp. left-asymptotic) to a vertex-type member is itself
  vertex-type, with the same right (resp. left) letter. Round-4 Lemma A
  gives (NM_V) on the left when `g_L` is injective and on the right when
  `g_R` is injective. It fails in general when an endpoint map is not
  injective, because distinct periodic rays can then branch away from the
  origin.

Two edges that share a vertex give vertex tilings that agree on a closed
half-line at the origin, and so share a tile.

### Theorem UP (unique partners)

Assume (NM_V). If every `T ∈ Ω_σ` has exactly one partner, then
`|L| = |R| = 2`. Consequently `β₁(ER) ≤ 1` and `dim H¹(Ω_σ; ℚ) ≤ 4`. For
odd `det M` this contradicts B15 Theorem 22, so **some tiling has two
different partners**.

**Corollary.** Let `σ ∈ PIP3` satisfy (NM_V) and have odd determinant,
`cr(σ) = 2` and a strict system. Then the first projection
`π₁ : Z → Ω_σ` is not injective. (W4) already gives this unless `σ` is unit
and `3 | r`, and Theorem UP covers that case.

If `g_L` and `g_R` are both bijective, (NM_V) holds by round-4 Lemma A, and
`L` and `R` are the whole alphabet. Three letters carry no fixed-point-free
involution, so unique partners are impossible **at every determinant**,
without B15 Theorem 22.

### Proof

1. **The involution.** `Z` is compact and `π₁(Z) = Ω_σ` by minimality. If
   `π₁` is injective, it is a homeomorphism, and `ι = π₂ ∘ π₁⁻¹` is
   continuous. `ι` commutes with the flow and with `Φ`, because `Z` is
   invariant under both. It is an involution because `Z` is
   swap-invariant. `T` and `ι(T)` share no tile at any level, by (Z2).
2. **A periodic vertex pair.** By (Z3), `Z` contains a `Φ^p`-fixed pair with
   a common vertex at the origin. Its two tilings have periodic germs
   there, so the pair is `(T_e, T_{e′})` with `e, e′ ∈ ER`. Thus
   `ι(T_e) = T_{e′}` is a vertex tiling.
3. **Propagation along `ER`.** Let `f` share a vertex with `e`, say its left
   letter.
   - `T_e` and `T_f` agree on `(−∞, 0]`. By uniform continuity of `ι` and
     its commutation with the flow, `ι(T_e) − t` and `ι(T_f) − t` agree on
     growing balls as `t → −∞`, up to shifts that tend to `0`.
   - Both tilings are partners of fibre-mates, so by (Z4) they are
     fibre-mates. Vertices of fibre-mates within `δ₀` of each other are
     equal (Lemma 1(1), as in the proof of (W4)). So the shifts are `0`,
     and the two tilings agree on a half-line `(−∞, −R]`.
   - So `ι(T_f)` is a zero-fibre tiling that is left-asymptotic to the
     vertex-type `ι(T_e) = T_{e′}`. By **(NM_V)** it is vertex-type, with
     the same left letter. It is `Φ^p`-fixed, since `ι` commutes with `Φ`,
     so its bigram at `0` lies in `ER`.
   - Without (NM_V) this step fails. Desubstitution shrinks the agreement
     radius `R` only towards `c/(β − 1)`, where `c` is the recognizability
     radius. Asymptotic periodic tilings may then branch at a common vertex
     away from `0`, as in the round-4 Fibonacci control.
   The right-letter case is symmetric. `ER` is connected (Lemma 7(2)), so
   `ι` maps every `T_g`, `g ∈ ER`, to a vertex tiling `T_{g′}` with
   `g′ ∈ ER`.
4. **The letter involutions.** The same asymptotic argument, with (NM_V)
   again, shows that the left letter of `ι(T_g)` depends only on the left
   letter of `g`, and likewise on the right. This defines `λ : L → L` and `ρ : R → R`.
   - `ι² = id` gives `λ² = id` and `ρ² = id`.
   - If `λ(x) = x`, then `T_g` and `ι(T_g)` share the tile `x` ending at
     the origin. That contradicts step 1. So `λ` has no fixed point, and
     likewise `ρ`.
5. **Counting.** A set of at most three letters that carries a
   fixed-point-free involution has exactly two elements, so
   `|L| = |R| = 2`. Hence `ER ⊆ L × R` has at most four edges, and
   `β₁ = |ER| − |L| − |R| + 1 ≤ 1`. Lemma 7(3) gives
   `dim H¹ = 3 + β₁ ≤ 4`, and B15 Theorem 22 needs `dim H¹ ≥ 5` for odd
   norm. ∎

For even determinant the theorem still forces `ER = K_{2,2}`, with
`dim H¹ = 4` exactly. The rank-two wall note's corollary
`dim H¹ ≥ 4` does not exclude that.

**Relation to round 4.** Theorem NC′ of the round-4 note says that a
covering `π₁` forces a fixed-vertex-free, side-preserving endomorphism of
the zero-fibre class graph. Theorem UP is its degree-one case on `ER`, under
(NM_V). The added content is the involution, and hence the parity count.
Round 4's Thue–Morse control (`01/10`, not PIP3) has `π₁` a homeomorphism
and `ER = K_{2,2}`, which is exactly the residue left here, so the count
cannot be sharpened without more input.

### Lean

[`proof/PscVerif/PscVerif/UniquePartnerLetters.lean`](../proof/PscVerif/PscVerif/UniquePartnerLetters.lean)
checks steps 4 and 5 over the three-letter alphabet, with no `sorry`:

- `card_eq_two_of_involution`: a nonempty `L ⊆ Fin 3` that a map sends
  into itself as a fixed-point-free involution has `L.card = 2`.
- `beta1_le_one`: an edge set `E ⊆ Fin 3 × Fin 3` whose left and right
  letter sets each carry such an involution has
  `|E| − |L| − |R| + 1 ≤ 1`.

Steps 1–3 are tiling-space arguments and are written proofs here.

### Consequence for the neutral obligation

In the unit, `(m, m, m)` case of the
[seam-ceiling note](c4-neutral-rank-seam-ceiling-2026-11-18.md), a strict
carrier of a substitution satisfying (NM_V) must have multi-partner
tilings. By (W4), any two partners of one
tiling are `≈_s`-equivalent, so Barge's stack relation is nontrivial on
`Ω_σ`. The remaining object is therefore always a non-injective joining.

### Non-claims / remaining gaps

- No strict system at rank two is excluded. Theorem UP only removes the
  injective configuration, and only under (NM_V).
- Without (NM_V) the injective configuration stays open. Whether (NM_V)
  holds for every PIP3 substitution whose endpoint maps are not injective
  is the round-4 open question in another form. The corpus specimen
  `1/012/21` already violates (NM_V) (round-4 §3.6).
- The even-determinant case keeps `ER = K_{2,2}` as a residue.
- The argument does not pass to Barge's stack quotient `Ω_s`. There the twin
  involution exists for every rank-two `σ` (B15 Lemma 13). The alphabet is
  the stack alphabet of a proper substitution, so the three-letter count in
  step 5 does not apply.
- **Next statement to try:** run steps 1–4 with the multi-valued partner
  relation in place of `ι`. In that relation the partners of one tiling
  are pairwise coincident by (W4). The aim is a set-valued letter
  correspondence whose parity or size contradicts `β₁(ER) ≥ 2`.
