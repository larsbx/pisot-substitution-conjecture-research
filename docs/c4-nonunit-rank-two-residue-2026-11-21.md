# The nonunit rank-two residue is `K₂,₂` with nilpotent incidence modulo two

**Status:** Written proof, single prover, no independent verifier, not machine-checked.
Exact corpus replay in Mojo (`psc.twin_fixed_points`). It continues the
[twin-endpoint note](c4-nonunit-twin-endpoint-2026-11-21.md) and corrects its residue
list. No strict system is assumed. No governed claim changes. Starting revision:
`origin/main@287ae87`. [Source decision](c4-nonunit-rank-two-residue-stop-go-2026-11-21.md).

## Statement

Let `σ` be a primitive substitution on three letters with irreducible Pisot incidence `M`,
`|det M| ≠ 1` and coincidence rank two. Write `g`, `g_R` for the first- and last-letter
maps and `ER` for the eventual-range graph, with left vertex set `L` and right vertex set
`R`.

**Lemma N (fixed tilings).** For a primitive aperiodic substitution and `n ≥ 1`,

```text
#Fix(Φⁿ) = tr(Mⁿ) − #Fix(gⁿ) − #Fix(g_Rⁿ) + #{legal ba : g_Rⁿ(b) = b, gⁿ(a) = a}.
```

**Proposition P (parity).** Under the standing hypotheses `#Fix(Φⁿ)` is even for every
`n ≥ 1`.

**Theorem R (residue).** Under the standing hypotheses:

1. `g` and `g_R` are both non-injective, each with exactly two periodic letters;
2. `ER = K₂,₂`: `|L| = |R| = 2` and all four words `ba` with `b ∈ L`, `a ∈ R` are legal.
   So `dim H¹(Ω; ℚ) = 4`;
3. `tr M` and `det M` are even. Equivalently `χ_M ≡ t³` or `t(t + 1)²` modulo two;
4. `χ_M ≡ t³` modulo two. So `tr M`, `e₂(M)` and `det M` are even and `M³ ≡ 0`.

Items 1–3 use Theorem E, Theorem H3 and the fixed-tiling count. Item 4 also uses Lemma S+
and the covering argument of the [even-residue note](c4-even-stack-residue-2026-11-19.md),
which that note ran under a strict system. Here they run without one.

## Work shown

### Assumptions and hypotheses

- **(T1)** The twin map `ι` is a continuous involution of `Ω` commuting with translation
  and with `Φ`, and `Φˡ(T) ∩ Φˡ(ι(T)) = ∅` for all `l`
  ([Corollary T2](c4-nonunit-trivial-stack-2026-11-21.md)). Only `ι(T) ≠ T` is used.
- **Theorem E** of the twin-endpoint note.
- **Theorem H3** of the [rank-two wall note](c4-rank-two-wall-2026-11-16.md):
  `dim H¹(Ω; ℚ) = 3` excludes rank two, for every determinant. It is a written theorem
  conditional on its listed imports.
- For item 4: Lemma S+ of the rank-two wall note (§7) with its imports, and two sections
  of the even-residue note, "The cover requires four classes on its base" and "The signed
  parity identity forces nilpotence". Both use only the two-sheet cover `p : X → Y`, the
  ordered-pair presentation and the bound `dim H¹(X; ℚ) ≤ 4`.
- Lemma 7 of the [(F)-class note](c4-geometric-f-class-2026-11-16.md): `ER` is connected,
  its edges are the legal `ba` with `b` periodic under `g_R` and `a` periodic under `g`,
  and `dim H¹(Ω; ℚ) = 3 + β₁(ER)`.

### Derivation / reduction

**Proof of Lemma N.** Let `T` be fixed by `Φⁿ`.

- *Origin inside a tile `a`,* at distance `x ∈ (0, ℓ(a))` from its left end. `Φⁿ` replaces
  the tile by the patch of `σⁿ(a)` starting at `−βⁿx`. The tile of `T` at the origin is
  one of its tiles, say the occurrence of `a` after a prefix `p`, and
  `−βⁿx + ℓ(p) = −x`. So `x = ℓ(p)/(βⁿ − 1)`.
  - `x > 0` iff `p` is nonempty.
  - `x < ℓ(a)` iff `ℓ(p) < ℓ(σⁿ(a)) − ℓ(a)`, iff the suffix after the occurrence is
    nonempty.
  - Conversely each occurrence of `a` strictly inside `σⁿ(a)` gives one fixed tiling, the
    nested union of the patches `σ^{kn}(a)` placed by the occurrence. It lies in the hull
    by primitivity.

  The occurrences of `a` in `σⁿ(a)` number `(Mⁿ)_{aa}`. The first position is one of them
  iff `gⁿ(a) = a`, and the last iff `g_Rⁿ(a) = a`. For `|σⁿ(a)| ≥ 2` these are different
  positions. If `|σⁿ(a)| = 1` for a fixed `a`, then `σⁿ(a) = a` and the hull would be
  periodic. Summing over `a` gives `tr(Mⁿ) − #Fix(gⁿ) − #Fix(g_Rⁿ)`.
- *Origin at a vertex,* with tiles `b` on the left and `a` on the right. Then `ba` is
  legal, `σⁿ(b)` ends with `b` and `σⁿ(a)` starts with `a`. Conversely such a word gives
  the fixed tiling `lim σ^{kn}(b).σ^{kn}(a)`. ∎

**Proof of Proposition P.** By (T1), `ι` maps `Fix(Φⁿ)` to itself and has no fixed point.
A finite set with a free involution has even cardinality. ∎

**Proof of Theorem R.**

1. *A cycle.* By Theorem H3, `dim H¹ ≠ 3`, so `β₁(ER) ≥ 1`. A cycle in a bipartite graph
   has two vertices on each side, so `|L| ≥ 2` and `|R| ≥ 2`.
2. *Non-injective maps.* If `g` were injective, Theorem E(1) would give `|R| ≤ 1`. If
   `g_R` were injective, Theorem E(2) would give `|L| ≤ 1`. So neither is.
3. *`K₂,₂`.* A non-injective map of three letters has an image of at most two letters, so
   at most two periodic letters. `L` consists of periodic letters of `g_R` and `R` of
   periodic letters of `g`. So `|L| = |R| = 2`, both maps have exactly two periodic
   letters, and `ER ⊆ K₂,₂`. A subgraph of `K₂,₂` with a cycle is `K₂,₂`.
4. *Parity.* `gⁿ` permutes its two periodic letters and fixes no other letter, so
   `#Fix(gⁿ) ∈ {0, 2}`. Likewise for `g_Rⁿ`. All four words of `L × R` are legal, so the
   fixed legal words number `#Fix(g_Rⁿ) · #Fix(gⁿ) ∈ {0, 4}`. By Lemma N and Proposition P,
   `tr(Mⁿ)` is even for every `n ≥ 1`.
5. *Trace and determinant.* With `p_n = tr(Mⁿ)` and `e₁, e₂, e₃` the coefficients of
   `χ_M`, Newton's identities give `p₁ = e₁` and `p₃ = e₁³ − 3e₁e₂ + 3e₃`. So `p₁` and
   `p₃` even force `e₁ = tr M` and `e₃ = det M` even. Conversely, if both are even then
   `p₂ = e₁² − 2e₂` is even and `p_n ≡ e₂ p_{n−2}` modulo two for `n ≥ 4`, so every `p_n`
   is even. Modulo two, `χ_M = t³ + e₂ t`, which is `t³` or `t(t + 1)²`. ∎

6. *Nilpotence (item 4).* The stack relation is trivial, so the stack quotient is `X = Ω`
   and `p : Ω → Y = Ω_p` is the two-sheet cover of Corollary T2.
   - By step 3, `dim H¹(Ω; ℚ) = 3 + β₁(K₂,₂) = 4`. This replaces the even-residue note's
     upper bound, the only place where that note used a strict system in these two
     sections.
   - The odd sheet function `z` and the eigenfunction theorem of
     Barge–Kellendonk–Schmieding give `dim H¹(Y; ℚ) ≥ 4`. The norm map makes `p*`
     injective over `ℚ`. So `dim H¹(Y; ℚ) = 4`, and the part of `H¹(Ω; ℚ)` on which `ι*`
     is `−1` vanishes.
   - In Lemma S+ the invariant part has dimension `3 + deg r` and the anti-invariant part
     `deg q₁`. So `deg r = 1` and `deg q₁ = 0`. The degrees in `h_n r̄ = (t + 1) q̄₁` give
     `d₂ + 1 = 1`, so `d₂ = 0` and `χ_M ≡ t³`. ∎

Step 6 removes the class `t(t + 1)²` that steps 4–5 leave. In the notation of Lemma S+ it
is `(r, q₁) = (1, c_n)`, an anti-invariant seam class. The count cannot see it, because
`tr(Mⁿ)` is even for every `n` in both classes.

**What the residue looks like.** Both endpoint maps collapse one pair and exchange or fix
two periodic letters. Every pair of seams sharing a ray has twins branching on the
collapsed pair, strictly off the origin (case (B) of
[Theorem S](c4-witness-selection-2026-11-19.md#results)). `M` is nilpotent modulo two, the setting of the
[even-incidence tails](c4-even-tails-2026-11-20.md). The eight periodic tilings in play
are the four seams `T_(b,a)` and their twins. Seams pair up on each tail and so do twins,
but no two of the eight agree on both tails. The even-tail theorem needs such a pair, so
it does not apply as it stands.

**Consistency with Theorem P+.** With `Ω_ψ ≅ Ω`, the embedding in Lemma S+(4) is onto, so
`r · q₁ = c_n`. For `c_n` of degree one this leaves `d₂ = 0` with `(r, q₁) = (c_n, 1)` and
`d₂ = 2` with `(1, c_n)` and `h_n = (t + 1)²`. Those are the two classes of step 5, found
there from the count alone.

### Evidence and replay

Finite object: the 1,926 nonunit members of the 4,554-member PIP corpus. For each, the
literal count of Lemma N for `n = 1, …, 8` and the three exclusions.

```sh
cd kernel
pixi run mojo run -I . -I tests tests/test_twin_fixed_points.mojo
pixi run mojo run -I . nonunit_residue_census.mojo
```

| Count | Value |
| --- | --- |
| nonunit members | 1,926 |
| Theorem E applies | 840 |
| `ER` is a tree (Theorem H3) | 1,362 |
| Theorem E or Theorem H3 | 1,794 |
| some `#Fix(Φⁿ)` odd, `n ≤ 8` | 1,338 |
| past Theorems E and H3 | 132, all with `ER = K₂,₂` |
| survivors of all three (items 1–3) | 72 |
| of those, `χ_M ≡ t³` (item 4) | **24** |

The regression asserts, on every nonunit member:

- the literal count equals `tr(Mⁿ) − #Fix(gⁿ) − #Fix(g_Rⁿ) + #{fixed edges of ER}` for
  `n ≤ 6`, with the trace from `Mat3` powers and the fixed edges from the cycle type of
  `psc.rank_two_parity.er_graph_map`. Neither is used by the literal count;
- past Theorems E and H3, `ER = K₂,₂`, the determinant is even, and all counts are even
  iff `tr M` is even, decided at `n = 1`.

Every corpus determinant other than `±1` is even, so step 5's `n = 3` case does not occur
there. Word lengths are capped at `2·10⁶` and the cap raises. A scratch Python enumeration
written before the Mojo module gave the same seven counts. It is not in the repository.

### Negative controls

- **Thue–Morse.** The letter exchange is a free involution of `Fix(Φⁿ)`. The count is `2ⁿ`
  for even `n` and `2ⁿ − 2` for odd `n` (pinned for `n ≤ 8`). Proposition P holds there
  and excludes nothing.
- **Tribonacci** has pure discrete spectrum and counts `0, 2, 6`. An even count is
  necessary at nonunit rank two, not a sign of it.
- **The survivors.** All 24 have pure discrete spectrum by the standing corpus results. So
  the conditions of Theorem R cannot by themselves exclude rank two. The 24 are the
  `K₂,₂` row of the [even-residue shape table](c4-even-rank-two-investigation-2026-11-19.md#complete-ranges-and-the-finite-controls),
  computed there by a different module.
- **Unit determinant.** `ι` is defined on the stack quotient, whose fixed tilings are not
  counted by Lemma N for `σ`. Proposition P and Theorem R are not claimed.

### Non-claims / remaining gaps

1. Nonunit rank two remains open on the class of Theorem R. Excluding it needs an argument
   for twins branching on the collapsed pair in `K₂,₂`.
2. Theorem R inherits the written inputs of #633, of the trivial-stack note, of Theorem E
   and of Theorem H3 with its imports. Item 4 also inherits Lemma S+ and the covering
   argument of the even-residue note. None is machine-checked end to end. The transfer of
   that covering argument to the setting without a strict system is checked here only by
   reading which hypotheses its two sections use.
3. The corpus figures are class counts under these conditional theorems. No coincidence
   rank is computed.
4. Unit determinant and coincidence rank three or more are not covered. Universal C4 and
   PSC remain open.
