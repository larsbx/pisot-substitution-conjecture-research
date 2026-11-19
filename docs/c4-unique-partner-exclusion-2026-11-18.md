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

### Theorem UP′ (coverings)

Round-4 Lemma C splits the general case in two. Either `π₁` is a covering of
constant degree `k`, or `π₁` is locally injective at no point of `Z`, which
means some tiling has two partners that agree on a half-line. The covering
case reduces to a regular letter graph.

**Theorem UP′.** Assume (NM_V), and that `π₁` is a covering. Let
`n_v ≥ 1` be the number of vertex-type partners of a vertex tiling `T_g`,
`g ∈ ER`; it does not depend on `g`. Then:

1. Either `n_v = 1` and `|L| = |R| = 2`, so `β₁(ER) ≤ 1` and
   `dim H¹ ≤ 4`. This is excluded for odd determinant by B15 Theorem 22.
2. Or `n_v = 2` and `|L| = |R| = 3`. This case is **impossible at every
   determinant**: the two vertex partners of a vertex tiling are partners
   of each other, which gives three pairwise non-coincident tilings in one
   fibre, against `cr(σ) = 2`.

So under (NM_V), `π₁` is not a covering when `det M` is odd. When `det M`
is even, a covering forces `n_v = 1` and `ER = K_{2,2}`. Degree one is the
unique-partner case, so Theorem UP is the special case `k = 1`.

*Proof.* Let `T, S` be vertex tilings that agree on a half-line.

- **Lemma L** (round 4) matches the partners of `T` bijectively with those
  of `S`, each with one asymptotic to it on the same side.
- **(NM_V)** makes a partner asymptotic to a vertex-type partner itself
  vertex-type, with the same letter on that side.
- Applying the same argument to the inverse matching shows that vertex type
  is preserved in both directions.

Hence the multiset of left letters of the vertex-type partners of `T_{xy}`
depends only on `x`, and the multiset of right letters only on `y`.

- **Lemma C(b)** (round 4): under a covering, no two partners of one tiling
  are asymptotic. So these letters are distinct, and the multisets are sets
  `Λ(x) ⊆ L` and `P(y) ⊆ R`.
- `x ∉ Λ(x)`, because a partner with the same left letter would share the
  tile ending at the origin, against (Z2).
- `y ∈ Λ(x)` iff `x ∈ Λ(y)`, because `Z` is swap-invariant.
- `ER` is connected, so `n_v = |Λ(x)|` is the same for every `x`, and
  likewise `|P(y)|`. The common value is at least 1 by (Z3).

So `Λ` is an `n_v`-regular simple graph on `L` with `n_v ≥ 1`, and so is
`P` on `R`. On at most three vertices this forces either `n_v = 1` on two
vertices or `n_v = 2` on the triangle.

*Case 2 closes a triangle.* Let `e = xy` have the vertex partners `f` and
`g`. Their left letters are the two letters other than `x`, and their right
letters the two other than `y`.
- `f`'s vertex partners have the left letters other than `f`'s and the
  right letters other than `f`'s.
- One of them is `e`, by swap-invariance.
- The other therefore has the third left letter and the third right letter,
  so it is `g`.

Then `e`, `f`, `g` are pairwise partners. By (Z2) they share no tile at any
level, so they are three pairwise non-coincident tilings in the zero fibre.
BBK Remark 4.3 then gives `cr(σ) ≥ 3`, a contradiction. ∎

**Correction to the earlier sharpness remark.** Round 4's singular control
`012/120/201` (§3.6) has `ER = K_{3,3}` and `Z = {(T, ρT)}`, with `ρ` the
cyclic relabelling. Its swap-closure is a degree-two covering with
`n_v = 2`, but its partner graph is a union of triangles, so it has
coincidence rank at least 3. It is not a rank-two example of case 2.

**What remains under (NM_V).** For odd determinant, a rank-two strict
component has `π₁` locally injective nowhere (round-4 Lemma C): some tiling
has two partners that agree on a half-line. For even determinant, the
covering case is limited to `n_v = 1` with `ER = K_{2,2}`.

### Scope on the corpus: where (NM_V) holds

Theorems UP and UP′ assume (NM_V). This section decides (NM_V) exactly on the
corpus, with a new decision procedure for asymptotes in the zero fibre.

#### Targeted literature stop/go for the asymptote decision

*Claim.* For two `Φ^Q`-fixed members `T`, `S` of `F₀`, `T ∼_L S` holds iff no
non-coincident overlap state reachable from a left branch of the central
overlap chain lies on a cycle of the overlap graph. The mirror statement
holds for `∼_R`. The criterion is a finite, exact computation.

| Source | Statement used | Gate |
| --- | --- | --- |
| Sirvent–Solomyak, *Pure discrete spectrum for one-dimensional substitution systems of Pisot type*, Canad. Math. Bull. 45 (2002), Thm 5.6 and §§3–5 | The overlap algorithm: cells of two tilings as overlap states `(top, bottom, offset)` closed under inflation. Its finiteness for the Perron lengths of an irreducible Pisot substitution, and the persistence of coincidences. | [overlap-depth gate](bpa-overlap-depth-literature-gate-2026-10-02.md) §2 |
| Barge–Diamond, Proc. AMS 136 (2008), Thm 4 and the eventual range | The vertex-type members of `F₀` are the seams of `ER`. | [round-4 note](c4-round4-2026-11-17.md), §1.2 |
| Baker–Barge–Kwapisz, Ann. Inst. Fourier 56 (2006), Thm 4.2 | Finite fibres, so `F₀` is finite and its members are `Φ`-periodic. | [(F)-class literature](c4-geometric-f-class-literature-2026-11-16.md) |
| Barge, Bull. SMF 143 (2015), the asymptotic cycles before Cor. 25 | The notion of asymptotic members of the identity fibre being decided here. | [round-4 note](c4-round4-2026-11-17.md), §1.2 |
| Round-4 note §3.3 (Lemma A, (R3), (R4)) and §3.7 | Branch points of `Φ^Q`-fixed asymptotic pairs, and the earlier scratch method: bounded merge certificates, with interior members enumerated in floating point. | internal |

*Transfers.*
- Sirvent–Solomyak's overlap states and their exact children: fibre-mates
  have integral offsets, so the closure is finite on the screened
  irreducible Pisot tables. A cap raises.
- Coincidences persist under inflation.
- Every member of `F₀` is fixed by `Φ^Q` (BBK Thm 4.2 with (R4)).
- The complete list of interior members comes from the certified box of the
  (F)-class note (Lemmas B and W) through `decide_geometric_f`.

*Does not transfer.*
- Sirvent–Solomyak decide whether translates `T` and `T − β^n x` coincide
  with bounded gaps. The criterion here instead concerns one side of a
  pair of periodic fibre-mates. Only their overlap kernel is reused, not
  their theorem.
- The criterion needs both tilings `Φ^Q`-fixed and in one fibre. For
  non-periodic tilings, or tilings in different fibres, the central chain is
  not eventually periodic and the reduction does not apply.
- Round 4's scratch merge certificates were one-sided ("none found under
  caps does not prove absence"). The criterion here is two-sided.

*Controls.*
- Round 4's exact certificate on `1/012/21`, with an interior member
  merged on the right, is reproduced.
- Every reported asymptote is confirmed by literal word rays from an
  independent oracle.
- Round 4's Lemma A is asserted throughout the census.

*Decision.* **Proceed.** Novelty is claimed only for the exact two-sided
criterion, measured against round 4's scratch method and the sources above.

**Exact decision of `∼_L` and `∼_R` on `F₀`.** The procedure is
`kernel/psc/zero_fibre_asymptotes.mojo`.
- Every member is fixed by `Φ^Q` for a common `Q`.
- Every cell of a pair to the left of the origin descends from a left
  branch of the central chain of cells containing `0⁻`.
- A descendant of a left branch at depth `k` lies in `β^k` times a fixed
  negative interval.

Hence two members are left-asymptotic iff no non-coincident overlap state
reachable from a left branch lies on a cycle of the overlap graph. The right
side is the mirror. Interior members are the certified `f`-cycle states of
`decide_geometric_f`. All arithmetic is exact, and every cap raises.

**Census** (`kernel/nmv_census.mojo`, 23 s). It covers the unit corpus
members with at least two periodic letters for both endpoint maps, which is
necessary for a strict root pair.

| Count | Value |
| --- | --- |
| members of the domain | 936 |
| (NM_V) holds | 888 |
| fails on the left | 24 |
| fails on the right | 24 |
| `β₁(ER) ≥ 2` | 492 |
| `β₁(ER) ≥ 2` with (NM_V) | **492** |

Checks run alongside the census:
- **Lemma A consistency.** A right failure needs `g_R` non-injective and a
  left failure needs `g_L` non-injective. The census asserts this and it
  holds throughout.
- **Literal oracle.** `oracles/python/nmv_literal_rays.py` shares no code
  with the Mojo module. It rebuilds both rays from the substitution words,
  using literal interior addresses, and confirms all 96 failing pairs as
  aligned agreements (`tests/test_nmv_literal_rays_oracle.py`).
- **Pinned specimens.** The Mojo regression pins three failures: `1/012/21`
  (right; round 4's certificate), `01/12/021` (right) and `220/01/021`
  (left). It also pins two passes, `01/122/201` and Tribonacci, and one
  decided non-asymptote that literal rays also separate.

**Consequence on the corpus.** Take a unit corpus member with odd
determinant. If it had coincidence rank 2, B15 Theorem 22 would give
`β₁(ER) ≥ 2`, so (NM_V) holds for it. Theorems UP and UP′ then apply
without hypothesis: a strict component at rank two could be neither
unique-partner nor a covering, so `π₁` would be locally injective nowhere.
The corpus has no strict system, so this maps where the theorems apply and
excludes nothing new. Every failure of (NM_V) on the corpus has
`β₁(ER) ≤ 1`.

### Lean

[`proof/PscVerif/PscVerif/UniquePartnerLetters.lean`](../proof/PscVerif/PscVerif/UniquePartnerLetters.lean)
checks steps 4 and 5 over the three-letter alphabet, and the letter count
of Theorem UP′, with no `sorry`:

- `card_eq_two_of_involution`: a nonempty `L ⊆ Fin 3` that a map sends
  into itself as a fixed-point-free involution has `L.card = 2`.
- `beta1_le_one`: an edge set `E ⊆ Fin 3 × Fin 3` whose left and right
  letter sets each carry such an involution has
  `|E| − |L| − |R| + 1 ≤ 1`.
- `regular_cases` and `no_matching_on_three`: an `n`-regular simple graph,
  with `n ≥ 1`, on at most three letters has either `n = 1` and two letters
  or `n = 2` and three.
- `partner_triangle`: in two-partner data on bigrams of `Fin 3 × Fin 3`
  (symmetric, letters differing from the bigram's own and from each other),
  the two partners of a bigram are partners of each other.

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
- Theorem UP′ removes the covering case under (NM_V) and odd determinant.
  What remains is the joining that is locally injective nowhere.
- **Next statement to try:** take the two partners that agree on a
  half-line, supplied by round-4 Lemma C(c). Show they can be chosen
  `Φ`-periodic in the zero fibre, and that with (NM_V) and (W4) they force
  a third pairwise non-coincident tiling or a letter parity contradiction.
