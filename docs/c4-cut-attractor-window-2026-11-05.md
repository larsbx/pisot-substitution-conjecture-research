# C4: the cut attractor, its window, and where the lever is not — 2026-11-05

**Status:** Lemma F is prior art (Sirvent–Solomyak 2002) restated for this
repository. Lemma N and Lemma G are repository-proved at the status of
[#480 §8](c4-cut-pair-productivity-2026-11-04.md#8-fixed-lattice-regular-box-density-a-self-contained-sublemma)
(human review pending). Proposition R is conditional on named imports.
Propositions 1–3 are finite combinatorics and reductions. No change to C4, BH
(#139), A1′ (#138), G1, PSC, SC_all or subtile disjointness.
[Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
Baseline `main@6053627`.

This note answers one question: is there a mechanism that excludes strict
systems for primitive irreducible Pisot `σ` *without* passing through pure
discrete spectrum (covering degree one) or all-pairs strong coincidence? Six
independent routes were run and adversarially checked on 2026-11-05. The
answer is **no, not at this altitude**, and §7 records exactly where each
route ends. The positive content is the structure that forces that answer.

Notation as in the [cut-pair note](c4-cut-pair-productivity-2026-11-04.md):
`M`, `β`, `ℓ`, `E^s`, `π`, `M_s`, the positive-prefix subtiles `R_c`, a strict
system `C`, its cut-pair set `A(C)`, child matrix `N`, Parikh matrix `P`,
`L_S = ℓ·p(u_S)`, `L_max`. The *hub* `h` is the letter outside the left
Barge–Diamond good edge `{a,b}`, so `A(C) ⊆ {{h,a},{h,b}}` by Theorem A(4).

## 1. Lemma F (common vertices are balanced cuts)

Let `σ` be primitive on `{0,1,2}` with `χ_M` irreducible over `ℚ`, and `ℓ` a
positive left Perron row. The entries of `ℓ` are ℚ-linearly independent: a
rational relation `ℓ·m = 0` would give `ℓ·M^k m = β^k ℓ·m = 0` for `k = 0,1,2`,
and `m, Mm, M²m` span `ℚ³` because every nonzero vector is cyclic for an
irreducible cubic.

**Lemma F.**
(a) Let `T, T′` be two bi-infinite `ℓ`-tilings (words over `{0,1,2}`;
legality is not assumed) sharing the vertex `0`. At every further common
vertex `x`, `p(T[0,x]) = p(T′[0,x])`. Hence common vertices are balanced
cuts, the patches between consecutive common vertices are irreducible
balanced pairs, and a common tile is a coincident factor.
(b) If `T, T′` are fixed by `Φ^k` (the `k`-fold inflation), share no tile at
any level `n ≥ 0`, and their common-vertex gaps are at most `G` uniformly in
`n`, then the patches between consecutive common vertices form a finite
strict system for `σ^k`, hence one for `σ`.
(c) Conversely a strict system `C` yields, on a sink SCC of its child graph
and for `τ = σ^p` with `p ≤ 3` (`p ≤ 2` under PIP, Proposition 1), two
one-sided `τ`-fixed words `W_h, W_x` (`h ≠ x`) that share no tile and whose
common vertices have gaps at most `L_max`; a two-sided pair exists whenever a
state has an interior self-occurrence, which a sink SCC always provides. The
states of `C` need not be legal words.

*Proof of (a).* Both `y = p(T[0,x])` and `y′ = p(T′[0,x])` lie in `ℤ³` and
satisfy `ℓ·y = x = ℓ·y′`, so `ℓ·(y − y′) = 0` forces `y = y′`. The rest is the
definition of the complete factorisation. ∎ Parts (b) and (c) are the
inflation-closure argument of Theorem A(2) read in both directions; (c) uses
that the ordered first-pair orbit under `g×g` is eventually periodic with
period `p ≤ 3`, with `p = 3` only for a 3-cycle `g` (Proposition 1).

*Hypotheses.* (a) and (b) use only irreducibility of `χ_M`; (c) uses
primitivity; Pisot is not used.

*Prior art.* (a) is Sirvent–Solomyak 2002, Lemma 5.5 ("immediate from the
rational independence"), and (b) is their Theorem 5.6 (i′)⇔(iii′) with the
uniform-bound clause (both read in the published text in the 2026-11-05 audit
workflow). It is restated here because the cut-pair program had been using
"strict system" and "fibre-mate pair" as if they were different objects.

*Controls (exact; `tests/test_c4_cut_attractor_oracle.py`).* Unit PIP
`01/12/021` with `ℓ = (1, β−1, β²−2β+1)` verified exactly in `ℚ(β)`: for
`σⁿ(01,10)`, `n = 1..5`, the common physical vertices are exactly the balanced
cuts (counts 2, 3, 6, 14, 39), and likewise for `σⁿ(02,20)` (4, 9, 18, 44, 104).
Uniform control `012/120/201`, `ℓ = (1,1,1)`: `σ²(012,120)` has 28 common
vertices and 10 balanced cuts, so the conclusion fails without ℚ-independence.
Reducible strict control `10/102/211`, `ℓ = (1, √3, 2)`, `ℓ·(2,0,−1) = 0`
exactly: the hypothesis fails, yet across the four strict states to depth 5
no common vertex that is not a balanced cut was found (1,324 common vertices).
That is an exhausted budget; the audit's prediction of a failure there was
refuted and is recorded.

## 2. Lemma N (all-position nesting) and Lemma G (the cut attractor)

Let `σ` be primitive with irreducible Pisot `χ_M`, `C` a strict system, `C′` a
sink SCC of its child graph (so `N|C′` is irreducible and every state has an
incoming edge). For a child edge `(F, j) → S` let `d_{F,j} ∈ ℤ³` be the
Parikh prefix of `σ(u_F)` at the `j`-th cut (the same on both tracks, by the
definition of a balanced cut). Define the **cut attractor**

```text
K_S = { Σ_{k≥1} M_s^{k−1} π d_k : (d_k) the translations along an infinite
        backward path S ← F_1 ← F_2 ← ⋯ in C′ },      K = ⋃_{S∈C′} K_S.
```

`K_S` is compact and satisfies `K_S = ⋃_{(F,j)→S} (M_s K_F + π d_{F,j})`. The
start cuts of type `S` in `σⁿ(root)` project within `Σ_{i≥n} ‖M_s^i‖·max|πd|`
of `K_{S}` (extend the backward path beyond the root); they are **not** in `K`
exactly, which an earlier draft assumed.

**Lemma N (all-position nesting; no determinant hypothesis).** For every
`F = (u,v) ∈ C′`, every top position `0 ≤ i < |u|` and bottom position
`0 ≤ i′ < |v|`:

```text
K_F + π p(u[:i]) ⊆ R_{u[i]},        K_F + π p(v[:i′]) ⊆ R_{v[i′]}.
```

In particular `K_S ⊆ R_{c_S} ∩ R_{c′_S}` for the first pair `(c_S, c′_S)` of
`S`, and `K ⊆ R_h ∩ (R_a ∪ R_b)`.

*Proof.* A point of `K_F + πp(u[:i])` is the limit of projections of lattice
points `x_n = p(σⁿ(F-prefix)) + p(σⁿ(u[:i]))`, each of which is the prefix of
an occurrence of `σⁿ(u[i])` inside an inflation; Theorem B Step 1 applied to
that prefix (as Theorem C already does) puts `π x_n` within `ε_n → 0` of
`R_{u[i]}`, and `R_{u[i]}` is closed. Step 1 is stated for the fixed point of
`σ^q`; it applies at every level because `R_c` is the unique compact solution
of its set equation, independent of the fixed point chosen. ∎

The K-piece of the edge `(F,j)` lies in the `R`-piece whose source letter is
`u_F[i]`, the letter whose image contains the cut, **not** `u_F[0]`: on
`10/102/211` eight of the twelve interior cuts and on `012/120/201` all six
have `u_F[i] ≠ u_F[0]` (`kernel/tests/test_c4_cut_attractor.mojo`). So the
nesting is piecewise, by translates, and not a vertex map of the two GIFS
graphs; "sub-GIFS" was the wrong word.

**Lemma G (window form).**
1. For every `t ≥ 0` and `S ∈ C′` there is `y ∈ ℤ³` with `ℓ·y ∈ [t, t + L_S]`
   and `πy ∈ K_S`, where `L_S = 2β^{m_0}L_max` and `m_0` is a multiple of the
   period of `N` with `(N^{m_0})_{S,F} > 0` for every `F` in the cyclic class
   of `S`.
2. `int K_S ≠ ∅` for every `S ∈ C′`. Hence `int(R_c ∩ R_c′) ≠ ∅` for every
   first pair represented in `C′`, each of which is `{h,a}` or `{h,b}`.
3. (unit case) The pieces `M_s K_F + π d_{F,j}` of each `K_S` are pairwise
   measure-disjoint and `λ(K_S) = t·z_S` with `z` the right Perron vector of
   `N|C′`. Nothing is asserted about `λ(K_S ∩ K_T)` for `S ≠ T`.

*Proof.* (1) At `σ`-levels `n` in the cyclic class of `S`, every closed window
of physical length `L_S` inside `[0, βⁿL_root]` contains the start of a
level-`n` factor of type `S` (gaps between consecutive cuts are at most
`L_max`, and every state of the class is reached within `m_0` steps). Fix `t`;
for each such `n` choose a start cut `x_n` in `[t, t+L_S]`. The candidates are
finitely many lattice points (bounded physical coordinate, bounded internal
coordinate by Step 1), so some `y` is a start cut of type `S` at infinitely
many levels, and `dist(πy, K_S) → 0` along them, so `πy ∈ K_S`.
(2) Consider the condition on `ξ ∈ ℝ×E^s`: "there is `λ ∈ Φ(ℤ³)` with
`(λ+ξ)_phys ∈ [0, L_S]` and `(λ+ξ)_int ∈ K_S`". It is `Φ(ℤ³)`-periodic and
closed (finitely many candidate `λ` in a bounded region), so it defines a
closed subset of the torus `T = (ℝ×E^s)/Φ(ℤ³)`. By (1) it holds on the
backward half-orbit `{[−t e_t] : t ≥ 0}` of the origin under the physical
flow, which is dense because the flow is totally irrational (§8
nonresonance). So it holds everywhere on `T`. Take `ξ = (0, s)` with `s` in a
unit ball `S_0`: the finite patch `Q = {πy : ℓ·y ∈ [0, L_S], πy ∈ K_S − S_0}`
satisfies `S_0 ⊆ ⋃_{q∈Q}(K_S − q)`. A finite union of translates of a closed
set with empty interior has empty interior, so `int K_S ≠ ∅`. With Lemma N,
`int(R_{c_S} ∩ R_{c′_S}) ≠ ∅`.
(3) `|det M| = 1` gives `λ(M_s A) = λ(A)/β`, so `k := (λ(K_S))` satisfies
`β k ≤ N k`. From `PN = MP`, `L := ℓP > 0` is a left Perron row of `N`
(`Lᵀ N = β Lᵀ`); pairing forces equality, so the pieces are measure-disjoint,
and irreducibility of `N|C′` makes `k` a multiple of `z`. ∎

*Hypotheses, step by step.* (1)–(2) use irreducible Pisot `χ_M` (Step 1 and
§8), strong connectivity of `C′`, and strictness only through `K ⊆ Z`; they
hold verbatim for any finite complete child-closed sink SCC. (3) uses
`|det M| = 1` for disjointness and irreducibility of `N|C′` for `k ∝ z`.

*The recursion.* The finite part of Lemma G is pinned on the strict controls:
the cut lattice obeys `X_{n+1}(S) = ⊔ (M X_n(F) + d_{F,j})` with multiplicity
one for `n ≤ 3` from every root, the two-track identity
`d = M p(u_F[:i]) + p(Q) = M p(v_F[:i′]) + p(Q′)` holds at every interior
cut with the letters after the cut equal to the child's first letters and
`p(u_F[:i]) ≠ p(v_F[:i′])`, and `P N = M P`
(`kernel/psc/c4_cut_attractor.mojo`). On `10/102/211` from `(102,210)`:
four states, `N = [[0,3,0,5],[1,1,0,1],[0,1,0,3],[0,0,1,0]]`, and
`Lᵀ N = β Lᵀ` exactly in `ℚ(√3)` (oracle).

## 3. Consequences, labelled

- **Strict ⇒ `int(R_h ∩ R_a) ≠ ∅` or `int(R_h ∩ R_b) ≠ ∅`, for every
  irreducible Pisot `σ`, with no determinant hypothesis.** This is Lemma G(2).
  In the unit case the subtiles have null boundary (Barge–Kwapisz 2006
  Prop. 18.1, unimodular; Sirvent–Wang 2002 Thm 4.1 gives `R_c = cl int R_c`;
  both read in the downloaded texts during the audit workflow), so
  `int(R_c ∩ R_c′) ≠ ∅ ⇔ λ(R_c ∩ R_c′) > 0`, and the statement is exactly
  Corollary B′ of the cut-pair note. It is not quantitative and does not
  replace Theorem B. For `|det M| ≥ 2` the Euclidean subtiles are expected,
  heuristically, to overlap in interior anyway; nothing adelic follows.
- **The topological content of Lemma G(3) and Lemma N adds no constraint
  beyond the retired GIFS measure comparison** (ledger 2026-11-04). Every
  identity derived from the two-way nesting — fibre arcs, hub rule,
  measure-disjoint `K`-pieces, `k ∝ z` — is satisfiable for every covering
  degree `≥ 2` (fibre-arc route, §7).

## 4. Proposition R (coincidence rank two; conditional)

Unit PIP. Imports: (I1) Baker–Barge–Kwapisz Thm 4.2 / Barge 2015 Thm 4(1),(2):
there is a full-measure set, invariant under inflation and the flow, over
which the fibre of the maximal equicontinuous factor map has exactly `cr`
tilings, pairwise non-coincident at every inflation level (read in the audit
workflow); (I2) the maximal equicontinuous factor is `(ℝ×E^s)/Φ(ℤ³)` with a
continuous equivariant realisation covering the toral automorphism
(Barge–Kwapisz 2006; repository literature gate, not re-read here).

**Proposition R.** If `cr(σ) = 2` and `int(R_c ∩ R_c′) ≠ ∅` for some `c ≠ c′`,
then `σ` has a strict system of legal patches: the common-vertex patches, at
all levels, of a generic fibre pair.

*Sketch.* Over a generic torus point the fibre is `{T, T′}`, non-coincident at
every level; by Lemma F their common vertices are balanced cuts. Every lattice
point over an open subset of `R_c ∩ R_c′` is a `c`-vertex of one of the two
and a `c′`-vertex of the other (a lattice point over `R_c` is a `c`-vertex of
some tiling in the fibre, and the two tilings share no tile), hence a common
vertex; a model set with a window of nonempty interior is relatively dense
with a gap constant uniform over translates, and inflation preserves the
generic set, so the gaps are bounded uniformly in the level. Lemma F(b)
finishes. ∎

With Lemma G: **at `cr = 2`, a strict system exists iff two subtiles have
intersecting interiors**, and by Lemma P and Barge–Diamond the pair is
`{h,a}` or `{h,b}`. By Barge 2015 Thm 22 (read; norm `±1`, `d = 3`), `cr = 2`
forces `dim H¹(Ω_σ) ≥ 5`. For `cr ≥ 3` only Lemma G's direction is available:
the fibre pair carrying the window may vary with the point.

## 5. Strict systems are A1′ plus bounded gaps

Write `g` for the first-letter map and `A1′(τ)` for: every pair of distinct
letters fixed pointwise by `τ₊` is left strongly coincident for `τ`
([A1′ note](p1a-a1-prime-2026-10-05.md) with the hub names dropped).

**Proposition 1 (finite).** Exactly 54 triples `(g, good edge, A)` satisfy
Theorem A(3) with `A` a nonempty set of pairs through the hub that `g×g`
preserves without collapsing: the `(|A|, recurrent cycle length)` distribution
is `{(1,1): 36, (2,1): 15, (2,2): 3}`; in every triple `g²` fixes both letters
of some pair of `A` pointwise; of the 36 single-pair triples, `g` fixes the
pair pointwise in 18 and swaps it in 18. The swap case `g(h) = x, g(x) = h` is
consistent with every constraint (it is template (ii) of the
[template-collapse note](p1a-template-collapse-2026-10-05.md)); the earlier
casework "either `g` fixes `h` or `g(a) = g(b) = h`" was incomplete. Over the
27 maps, 42 ordered `(g, pair)` instances are non-merged, with
`(transient, period)` distribution `{(0,1): 9, (1,1): 6, (0,2): 15, (1,2): 6,
(0,3): 6}`; period 3 occurs only for a 3-cycle `g` (type G), which
Barge–Diamond excludes under PIP.

**Proposition 2.** For primitive `σ`: `SC_all(σ) ⇔ A1′(σ) ∧ A1′(σ²) ∧ A1′(σ³)`;
under PIP the cube is not needed. Hence *A1′ for every PIP substitution* is
equivalent to *SC_all for every PIP substitution*. (⇐: a pair either merges,
giving a trivial witness, or enters a `g×g`-cycle of length `m ≤ 3` after `t`
steps; `A1′(σ^m)` gives a witness for the cycle pair, which the prefix
transfer along `σ^t` carries back.)

**Proposition 3.** For primitive `σ` the following are equivalent: (i) `σ` has
a strict system; (ii) for some `m ≥ 1` and letters `h ≠ x` fixed by `τ₊`,
`τ = σ^m`, the `τ`-fixed words `W_h, W_x` anchored at a common origin share no
tile and have common vertices with bounded gaps. Consequently
`C4(σ) ⇔ bounded-gap A1′ for every power of σ`: **a strict system is exactly
an A1′ configuration plus the bounded-gap (G1-type) condition.**

*Control.* The reducible strict control `10/102/211` satisfies every
combinatorial constraint of Propositions 1–3 with decoupled hubs (left hub 2,
right hub 0).

*Corpus.* The prefix map is eventually constant (types A, B) on 1,896 of the
4,554 specimens, the suffix map on 1,896, either on 3,012; on these, every
letter pair has a trivial witness and Theorem A(3) alone excludes a strict
system. On the remaining 1,542 the numbers of unordered non-merged pairs of
the two maps are distributed `{(2,2): 534, (2,3): 408, (3,2): 408, (3,3): 192}`.
This is the trivial-witness stratum of the existing two-sided
strong-coincidence census, not a new exclusion. The 12-member relabelling ×
reversal class of `1/2/01` (Perron root the plastic number) is the only
corpus class whose left witnesses need levels beyond 12: `{0,1}` at level 13
(prefix 17, letter 1), `{0,2}` at 14, and for the reversal `{0,1}` at level 15
(prefix 47); every member is witnessed by level 15. Any statement "strong
coincidence within level 12 on the corpus" must name this class.

## 6. Literature settlement

| Question | Answer | Source and how it was checked |
| --- | --- | --- |
| Is each unit subtile the closure of its interior with null boundary, unconditionally? | Yes. | Sirvent–Wang 2002 Thm 4.1 (closure of interior); Barge–Kwapisz 2006 Prop. 18.1 (null boundary, unimodular). Both read in downloaded texts by the audit workflow. |
| Is "subtiles pairwise measure-disjoint ⇔ strong coincidence on all pairs" a theorem? | Only ⇐ is found. | Arnoux–Ito 2001 Thm 2 (read); Siegel–Thuswaldner 2009 Thm 2.10 (SC ⇒ disjoint interiors) and their table listing disjoint interiors as conjectural (reported, not re-read). Sirvent–Wang p. 481 says "equivalent", which misreports Arnoux–Ito §6 ("unknown in the general case … a sufficient combinatorial condition"). Ito–Rao 2006 was read by no one. |
| Do fibre-mates share vertices? | Lemma F is Sirvent–Solomyak 2002 Lemma 5.5 / Thm 5.6 (iii′). | Read. No source asserts relatively dense common vertices for non-coincident fibre-mates without further hypotheses. |
| Does an overlap with nonempty interior force overlap coincidence or a self-overlap? | A restricted open overlap forces covering degree `≥ 2` (Siegel–Thuswaldner Thm 3.20, read), i.e. PDS strength; unrestricted open self-overlaps exist for every unit PIP (Tribonacci: `|π e_n|² = 1/(βⁿ(2−β))` exactly). | Open-overlap route, §7. |

Correction to a claim made during the audit: the Barge–Kwapisz fibre over the
origin is the set of all `Φ`-periodic integer strands, not only the strands
through `0`; a `Φ^k`-fixed strand with the origin inside an edge exists iff
`σ^k(a) = PaS`, `P, S ≠ ε`, with `(I − M^k)^{-1} p(P) ∈ ℤ³` (`01/12/021`,
`V = (1,0,−1)`, `(I−M)V = e_0`). The corpus counts of first such `k`
(`{1: 816, 2: 252, 3: 744}` through `k = 3`) are scratch-only and not pinned.

## 7. Retired routes (do not re-propose)

| Route | Surviving statement | Where it collapses |
| --- | --- | --- |
| Fibre-arc measure identities from the two-way nesting | exact intertwiners `D N′ = W D` without flatness; hub rule; at `d_cov = 2` the orderings, `K = Z` a.e. and `Γ_P = ℤ³` | all identities satisfiable for every `d_cov ≥ 3`; at `d_cov = 2` the chain reaches Barge 2015 Thm 22, a theorem about `σ` alone |
| Open-overlap graph | Lemma N; every same-letter position pair gives an open self-overlap `(d,d,e)`, `e ≠ 0` | unrestricted: vacuous (Tribonacci); restricted: PDS strength |
| Strong coincidence on the hub pairs | Propositions 1–3 | excluding the surviving class is `A1′(σ²)` on one pair, i.e. SC_all strength; the route sees only the letter level and discards the bounded gaps |
| Window sharpening | Lemma G(1)–(2) per state; the dichotomy "compact window has interior ⇔ its model set is relatively dense" | at `cr = 2` the output is *equivalent* to a strict system (Proposition R); the volume constraint `|det M_s| = 1/β` against `int K` fails because `K` is GIFS-invariant, not `M_s`-invariant |
| Derived-substitution rigidity | `τ` well defined, `φ_top` finite-to-one, the lattice constraint `m·Λ_1 ⊆ Λ_P` | needs a unique partner everywhere, which is Barge 2015 Cor. 25 at `cr = 2`; gauge-trivial orientation forces `m ≥ 2` |
| Literature | the settlement of §6 | no unconditional disjointness result exists in any source read |

The structural reason (Proposition 3): a strict system is an A1′ configuration
plus bounded common-vertex gaps. The casework consumes the first- and
last-letter data; Lemma F and Lemma G consume the bounded gaps and return an
open subtile overlap on a hub pair; and the only known contradiction to an
open overlap is strong coincidence on that pair. The sharpest chain proved
(unit PIP unless marked):

```text
PDS ⟹ SC_all ⟹ left SC on A(C) ⟹ λ(R_c∩R_c′) = 0 on A(C) ⟺ int(R_c∩R_c′) = ∅ on A(C) ⟹ no strict system ⟺ C4(σ)
C4(σ) ⟺ bounded-gap A1′ for every power of σ            [Proposition 3; any primitive σ]
∀σ A1′(σ) ⟺ ∀σ SC_all(σ)                                 [Proposition 2]
cr(σ) = 2:  C4(σ) ⟺ int(R_h∩R_a) = int(R_h∩R_b) = ∅       [Proposition R; conditional]
cr(σ) = 2 ⟹ dim H¹(Ω_σ) ≥ 5                              [Barge 2015 Thm 22]
```

**The next open quantifier**, sharpened from the cut-pair note §6: for every
unit PIP `σ` with `cr(σ) = 2` and every pair `{c,c′}` without a left
strong-coincidence witness, `int(R_c ∩ R_c′) = ∅`. On that class it is
equivalent to C4. Its hypothesis class is empty on every computed domain
(SC_all on the corpus) and constrained by `dim H¹ ≥ 5`. The concrete finite
step that would narrow it is a `dim H¹(Ω_σ)` census over the 2,628 unimodular
specimens. That census is done ([`dim H¹` census note](c4-h1-census-2026-11-05.md)):
2,136 unimodular specimens have `dim H¹ ≤ 4`, where Barge 2015 Thm 22 is
incompatible with `cr = 2`, and the `cr = 2` wall can live only among the
remaining 492 (408 at rank 5, 84 at rank 7). For `cr ≥ 3` the open sub-questions are cross-state disjointness
`λ(K_S ∩ K_T) = 0` and whether a PIP strict pair must have a branching over a
cut pair (which would force `cr ≥ 3` and iterate).

## 8. Non-claims

C4, BH, A1′, G1, PSC, SC_all; unconditional subtile disjointness (unit or
not); the non-unit adelic form; `cr = d_cov` before the Siegel–Thuswaldner
window-convention check; a second strongly coincident pair for ternary PIP
(not in Barge–Diamond, and it would not close the single-pair class);
measure-disjointness of `K_S` across states; that a strict pair is a generic
fibre; that the states of a strict system are legal; "no determinant
hypothesis" as leverage; "a cleaner proof of Theorem B". Nakaishi
arXiv:1610.03146 may not be cited.

## 9. Replay

```sh
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_cut_attractor.mojo)
python3 -m pytest -q tests/test_c4_cut_attractor_oracle.py
```

The native test pins the strict-control bookkeeping (ordered closure, `N`,
`P N = M P`, two-track nesting at every interior cut, multiplicity-one cut
recursion to depth 3, cut pairs inside `A(C)`, hub on one track), the 54
configurations and their statistics, the endpoint-collapse census over
`pip_corpus()`, and the deep class `1/2/01`. The oracle re-derives all of it
independently and adds the exact number-field checks (`Lᵀ N = β Lᵀ` in
`ℚ(√3)`, `ℓ` of `01/12/021` in `ℚ(β)`, the Lemma F controls). Lemmas F, N, G
and Proposition R are written proofs; no executable certifies a Lebesgue or
interior statement.
