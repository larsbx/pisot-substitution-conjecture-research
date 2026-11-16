# The coincidence-rank-two wall for C4: fixed-point counts, the unique strict component, and rank two excluded at `dim H¹ = 3` for every determinant — 2026-11-16

**Status:** recorded proofs with an exact replay of their finite parts.
Universal C4 is **not** proved and remains open: nothing here excludes a
strict system at coincidence rank two when `dim H¹ ≥ 4`. Label for every
statement of this note: recorded proof, conditional on the listed imports,
single prover plus independent adversarial re-derivation within the session
of 2026-11-16 (two verifiers; re-derived once more while this note was
written), not machine-checked, independent human review pending. Theorem FP,
Lemma K and Lemma U are elementary and use no import. Nothing here changes a
governed claim status (C4, #138, #139, #84, G1 and PSC are unchanged), and no
ledger claim is registered.
[Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).

Literature gate:
[`c4-rank-two-wall-stop-go-2026-11-16.md`](c4-rank-two-wall-stop-go-2026-11-16.md).
Parents: the (F)-class note
[`c4-geometric-f-class-2026-11-16.md`](c4-geometric-f-class-2026-11-16.md)
(Lemmas 1–10, Theorems FC1, FC2, P, FC3, N, Fork; its notation is used
throughout) and the record of round 1,
[`c4-closure-attempt-2026-11-16.md`](c4-closure-attempt-2026-11-16.md)
(Theorem FL; open statements, §10). Canonical implementations:
`kernel/psc/fixed_point_count.mojo` with
`kernel/tests/test_fixed_point_count.mojo` (Theorem FP) and
`kernel/psc/c4_geometric_f.mojo` with `kernel/tests/test_c4_geometric_f.mojo`
(the class counts of §12).

Round 1 ended at a wall. On the geometric property (F) class a hypothetical
strict system has coincidence rank exactly two (Corollary E), and coincidence
rank two was excluded only for odd determinant under an arithmetic condition
(Theorem P, Barge 2015 Thm 22). This note records what the second round
established about coincidence rank two, in three parts.

- **Rigidity (§§2–6).** An exact count of the tilings fixed by `Φⁿ`
  (Theorem FP) turns injectivity of the top-track map of a bigon system into
  a spectral condition (Theorem TT). With the first-defect intertwiner on
  main it shows that the top-track map of a swap-symmetric strict component
  is injective only for unit `σ` with first defect degree divisible by 3
  (Theorem NI). At coincidence rank two the strict component is unique, is
  carried by a primitive swap-symmetric strict system for `σ` itself, and
  its top-track map is injective almost everywhere (Theorem W).
- **Arithmetic (§§7–8).** Barge's ordered-pair substitution at coincidence
  rank two has an eventual range of two disjoint fixed edges (Lemma S+).
  This gives a parity bound for every determinant (Theorem P+) and, with the
  fact that at `dim H¹ = 3` every integral class is an eigenfunction class
  (Lemma 9′; Barge–Kellendonk–Schmieding 2012), excludes coincidence rank
  two at `dim H¹ = 3` for every determinant (Theorem H3). Corollaries FC3+
  and N+ extend clause (b) of Theorem FC3 and Theorem N(2) to even
  determinant.
- **An obstruction (§9).** The first-defect class of a strict component is
  not pulled back from `Ω_σ` unless its eigenvalue is a root of unity, so it
  cannot be transported to Barge's quotient and Lemma S says nothing about
  it (Obstruction T). The route "defect eigenvalue against Lemma S" fails at
  its first premise.

§10 states what is still open at coincidence rank two; §11 separates what is
new from what is on main or in the literature; §12 has the five "work shown"
headings with replay, controls and non-claims.

*A name.* "Theorem W" in this note is the rank-two **w**all theorem of §6.
It is not the ledger alias "Theorem W" of `ClassDWedgeBoundaryHitting`, with
which it has nothing in common.

## 1. Standing class, notation, imports

**PIP3** and the notation of the (F)-class note, §1: `σ` is a primitive
substitution on `{0,1,2}` with incidence matrix `M` (`M[a][b] = |σ(b)|_a`),
`χ_M(t) = t³ − (tr M) t² + e₂(M) t − det M` is irreducible over `ℚ` with
roots `β > 1 > |α₂|, |α₃|` (the (F)-class note writes `λ₂, λ₃`), and
`|det M| = 1` is not assumed. `ℓ > 0` is the left Perron row (tile lengths),
`r > 0` the right Perron column with `ℓ·r = 1`, `p(w)` the Parikh vector,
`g` and `g_R` the first- and last-letter maps. A word is *legal* if it is a
factor of some `σ^k(c)`. `Ω_σ` is the tiling space, `Φ` the inflation,
`T ↦ T − t` the flow, `dim H¹ = dim H¹(Ω_σ; ℚ) = 3 + l` (Lemma 7), and `c_n`
is the characteristic polynomial of `Φⁿ*` on the asymptotic-cycle part, so
that `Φⁿ*` has characteristic polynomial `χ_{Mⁿ} c_n` on `H¹(Ω_σ; ℚ)`
(Lemma 7(3)); the roots of `c_n` are roots of unity. `n ≥ 1` is *admissible*
if some legal word `ba` has `g_Rⁿ(b) = b` and `gⁿ(a) = a`.

*Geometric realization.* `h_φ: Ω_σ → 𝕋_A` is the geometric realization of
BBK Def. 3.1, restricted to `Ω_σ`. By Lemma 6 its lattice is `ℤ³`, so
`𝕋_A = lim←(ℝ³/ℤ³, M)` (the torus for unit `σ`, a solenoid otherwise), and
`h_φ(T) = (p_k)_{k∈ℤ}` with `p_k` the class of any vertex of the strand of
`Φ^k(T)`. It intertwines `Φ` with the shift automorphism of `𝕋_A` and the
flow with a minimal translation flow (BBK (3.10)–(3.12)), so
`h_φ(Ω_σ) = 𝕋_A`. `cr(σ) := cr_φ` is the coincidence rank of BBK Def. 4.1;
by BBK Thm 4.2 it is the least cardinality of a fibre of their `h_φ`,
attained on a set of full Haar measure (their strand space may contain
finitely many non-recurrent flow orbits besides `Ω_σ`; the proof of (W1)
allows for them). Two tilings of one fibre are *fibre-mates*.

*Bigon systems.* Let `P ≥ 1` and `τ = σ^P`. The *children* of an ordered
balanced pair `(u, v)` under `τ` are the irreducible factors of
`(τ(u), τ(v))`, in order. A **bigon system** for `τ` is a finite nonempty
set `B` of ordered irreducible balanced pairs of legal words that contains
the `τ`-children of each of its members. Its *child substitution* `Σ` is the
substitution on the alphabet `B` that sends `S` to the list of its
children; `N` is the incidence matrix of `Σ` (column `S` counts the children
of `S`). `B` is **primitive** if `Σ` is primitive, **strict** if no member
is coincident (it is then a strict system for `τ` with legal words). A
primitive bigon system is strict or consists of coincidences `(a, a)` only,
because the children of a coincidence are coincidences. For a bigon system:

- `Pk: ℚ^B → ℚ³`, `Pk(e_S) = p(u_S) = p(v_S)` for `S = (u_S, v_S)`, satisfies
  `Pk N = M^P Pk`, and `L(S) := ℓ·p(u_S) > 0` satisfies `L N = β^P L`
  (manuscript `thm:parikh`; R0 of the
  [general-structure note](c4-general-structure-2026-11-06.md));
- `K_r(S) = N_r(u_S) − N_r(v_S)` is the degree-`r` scattered-subword defect,
  `D_r: ℚ^B → (ℚ³)^{⊗r}` the matrix of the `K_r(S)`, and `r(B)` the least
  `r` with `D_r ≠ 0` (finite and at least 2 when `B` is strict). At
  `r = r(B)`:

  ```text
  (L0)        D_r N  =  (M^P)^{⊗r} D_r .
  ```

  This is Lemma 0 of the general-structure note, i.e. manuscript
  `thm:defect-intertwiner` read on ordered pairs, applied to the
  substitution `τ`. Its signed form on normalised states is machine-checked
  on main for `r ≤ 5` (`Psc.StrictSystem.StrictSystem.deg2_sector`,
  `StrictSystem.deg23_iii`, `StrictSystem.sieve4`,
  `Psc.Degree5Transport.intertwine`, `Psc.Degree5Sieve`; statements read,
  proofs not) and it is a written proof for general `r`;
- if `B = swap(B)`, where `swap(u, v) = (v, u)`, then `J` is the
  permutation matrix of the swap, `E_± = ker(J ∓ 1)`, and `N_± = N|E_±`
  (`N` commutes with `J`: the children of `swap(S)` are the swaps of the
  children of `S`, in the same order).

*Pair spaces.* `Ω_Σ` is the tiling space of `Σ` with tile lengths `L`, and
`R: Ω_Σ → Ω_σ × Ω_σ` reads every tile `S` as the pair of patches
`(u_S, v_S)` (both entries are in `Ω_σ` because the words are legal).
`Z = R(Ω_Σ)` is the **pair space** of `B`, `π₁: Z → Ω_σ` the first
projection (the *top track*), `p₁ = π₁ ∘ R`. `R` commutes with the flow and
`R ∘ Φ_Σ = (Φ^P × Φ^P) ∘ R`. A tiling `T′` with `(T, T′) ∈ Z` is a
**partner** of `T`.

A polynomial is **neutral** if it is a product of powers of `t` and
cyclotomic polynomials.

**Imports.** Each is used only where the table says. "Read" names who read
what; texts are the copies downloaded during the two rounds, and for BKS the
arXiv source fetched while this note was written.

| Tag | Source and statement | Hypotheses | Read | Used in |
| --- | --- | --- | --- | --- |
| BBK | Baker–Barge–Kwapisz, Ann. Inst. Fourier 56 (2006) 2213–2248: Def. 2.2, Prop. 2.3 (strand space and tiling space; their space may contain finitely many non-recurrent orbits besides `Ω_σ`, footnote 5); (3.8)–(3.12) and Def. 3.1 (`h_φ` into `𝕋_A`); Def. 4.1; Thm 4.2 (`h_φ` uniformly finite-to-one; a full-measure set of points whose fibre has exactly `cr_φ` elements, the minimum); (5.1)–(5.3) with the first step of the proof of Thm 5.1 (for `u` in the dual of `𝕋_A`, `χ_u ∘ h_φ` is a continuous eigenfunction with eigenvalue `u·r`); Cor. 5.2 | primitive, translation-aperiodic, Pisot; reducible and non-unimodular allowed | the prover and the logic verifier (passages); the passages listed re-read in the on-disk text while writing | W1, W2, W4; Lemma 9′; H3; FC3+ |
| B15 | Barge, Bull. Soc. Math. France 143 (2015), arXiv:1301.7094, numbering of the arXiv text: §2 (maximality of the factor map `g`; the equicontinuous structure relation is regional proximality); Thm 4(1)–(5); §3 (the relation `≈_s`); Thm 12; Lemma 13 with its proof; Lemma 14; Lemma 15 (`Ω_{Ψ_p} ≅ Ω_Ψ/∼_rpd`); Thm 17 (the 2-to-1 covering); the proper version (§4); Prop. 19; Lemma 20; sequence (4.1), Lemma 21; Thm 22 with the count of periodic words in its proof | primitive, non-periodic, Pisot dilation; Thm 12: border forcing and no pure discrete spectrum; Lemmas 13–15, Thm 17: `cr = 2` and `≈_s` trivial (Lemma 15, Thm 17 also border forcing); Prop. 19: proper; Thm 22: odd norm | TeX source of §§2–4 line by line (prover); statements and the proofs of Lemma 13, Thm 17, Thm 22 by both verifiers and again, in the PDF text, while writing. The proofs of Thm 4 are deferred there to other papers and were not followed; the rewriting references (Durand; Barge–Diamond 2001) were not read | S+, P+, Lemma 9′(b), H3; W4 (wording only); T |
| BD08 | Barge–Diamond, Proc. Amer. Math. Soc. 136 (2008) 2183–2191, arXiv:math/0702669: the complex `K ⊇ S`, the map `g` and `ER`; Theorem 4 with its proof (the elements `v_C`, fixed by a power; the exact sequence `0 → G_0 → G_1 → G_2 → G_3 → 0`, over `ℤ`); Theorem 4′ (the vectors `w_i`: the coboundary of the dual generator of a component of `S`) | primitive, aperiodic | TeX source (prover, logic verifier); §3 re-read while writing | S+, Lemma 9′ (second proof), T |
| BKS | Barge–Kellendonk–Schmieding, Fund. Math. 218 (2012) 243–267, arXiv:1204.1432, numbering of the arXiv source: §3.2 (`[X, S¹] ≅ H¹(X)`; `H¹` of the maximal equicontinuous factor is the group `E` of eigenvalues; the Schwartzman winding number `τ`); Lemma 2 (`τ ∘ θ` is the inclusion); Corollary 3 (`π*` is injective in degree one); Lemma 4; Theorem 5 (the cokernel of `π*: H¹(Ê) → H¹(Ω)` is torsion free) | a tiling space of finite local complexity with minimal `ℝⁿ`-action and an ergodic invariant measure; their substitutions are primitive, non-periodic, FLC | the prior-art verifier, in a fetched HTML rendering (statements; proofs paraphrased). **Read in the arXiv TeX source while this note was written**: statements and proofs of Theorem 1, Lemma 2, Corollary 3, Lemma 4, Theorem 5, Corollary 6 | Lemma 9′ (first proof), H3 |
| Repo | Lemma 0 / `thm:defect-intertwiner` (identity (L0)); `thm:parikh` and R0; R1(b) (`rank D₂ = 3`); Proposition Q of the general-structure note; the shape list of manuscript `thm:sieve` ([multidegree sieve](c4-multidegree-spectral-sieve.md) §§2–5); Proposition 1 and §3 of the [orientation-spectrum note](c4-orientation-spectrum.md) | nonerasing `σ`; `χ_M` irreducible for R1 and the sieve; primitive for Proposition Q | on main; Lean through `r = 5` as listed above, prose beyond | TT (general form), NI, W3, T |
| RepoF | (F)-class note: Lemma 1, Lemma 6, Lemma 7, Lemma 8, Lemma 10, Lemma S, Theorem FC2, Theorem N(1); Theorem A(4) of the [cut-pair note](c4-cut-pair-productivity-2026-11-04.md); Theorem FL of the closure-attempt note | as stated there; recorded proofs, not machine-checked (Theorem A is in Lean) | in full | W, S+, P+, H3, FC3+, N+ |
| Kron | Kronecker's theorem: a monic integer polynomial all of whose roots lie in the closed unit disc is neutral | — | **not read**; used on main in Proposition Q(b) | TT, NI |
| Std | Standard facts with no locator on disk: `Ȟ¹(X; ℤ) = [X, S¹]` for compact metric `X`, and a null-homotopic map to `S¹` has a continuous logarithm; a one-dimensional substitution tiling space has covering dimension one; a complex line bundle over a compact space of covering dimension at most one is trivial; the identification of the two coincidence ranks ((F)-class note, §1). For the second proof of Lemma 9′ only: the winding number of a circle-valued map along a uniquely ergodic flow; Gottschalk–Hedlund | — | **not read; marked where used** | H3, S+, P+; W4 (wording in Barge's terms only) |

Attributions only, used in no proof: Anderson–Putnam, Ergodic Theory Dynam.
Systems 18 (1998) 509–537 (**not read**; its Thm 9.1 was read as quoted in
Baake–Gähler–Grimm, arXiv:1211.5466 and arXiv:1201.1423 §6); Mignotte,
C. R. Acad. Sci. Paris Sér. I 298 (1984) 21 (**not read**; read as quoted in
Dubickas–Hare–Jankauskas, arXiv:1410.1600, Lemma 1.1);
Barge–Bruin–Jones–Sadun, Israel J. Math. 188 (2012), arXiv:1001.2027, the
theorem labelled `not2` in the arXiv source, with its proof (read in the TeX
source by the prover and the logic verifier, and again while writing).

*The two coincidence ranks.* `cr` is the rank of BBK Def. 4.1. Theorem W,
parts (1)–(3), uses only BBK and needs no identification. Lemma S+,
Theorems P+ and H3 and their corollaries run through B15, whose rank is the
least fibre cardinality of the maximal equicontinuous factor map `g_max`;
they use the identification `g_max = h_φ` on `Ω_σ` of the (F)-class note,
§1, which rests on one **[Std]** fact.

## 2. Fixed points of the inflation: Theorem FP

**Theorem FP (exact count).** Let `s` be a primitive substitution on an
alphabet with at least two letters, `A` its incidence matrix, `L > 0` a left
Perron row with eigenvalue `λ > 1`, `Ω_s` the space of tilings of the line
by half-open tiles `[y, y + L_a)` of type `a` all of whose finite patches
are legal, and `Φ` the inflation. Then for every `n ≥ 1`

```text
|Fix(Φⁿ)|  =  tr(Aⁿ)  −  #Fix(gⁿ)  −  #Fix(g_Rⁿ)
              +  #{ legal two-letter words ba :  g_Rⁿ(b) = b,  gⁿ(a) = a }.
```

Only primitivity is used. There is no irreducibility and no Pisot
hypothesis, and periodic primitive substitutions are included.

*Proof.* Let `Φⁿ(T) = T`. Either the origin is in the interior of a tile of
`T` or it is a vertex; the two cases are counted separately.

*Interior type.* Let `0` be in the interior of the tile `t` of `T`, of type
`a`, at `[−x, L_a − x)` with `0 < x < L_a`. The patch `Φⁿ(t)` is `sⁿ(a)`
placed at `−λⁿ x`; its support `[−λⁿ x, λⁿ(L_a − x))` contains `0` in its
interior, and the tile of `Φⁿ(T) = T` that contains `0` is `t`. So `t` is a
tile of `Φⁿ(t)`: there is a factorisation `sⁿ(a) = P a S` with
`−λⁿ x + L(P) = −x`, i.e. `x = L(P)/(λⁿ − 1)`, writing `L(w)` for the length
of a word. Since `L(P) + L_a + L(S) = λⁿ L_a`, the conditions `0 < x` and
`x < L_a` say that `P` and `S` are nonempty. Conversely, let `sⁿ(a) = P a S`
with `P`, `S` nonempty, put `x = L(P)/(λⁿ − 1) ∈ (0, L_a)` and let `t` be
the tile of type `a` at `[−x, L_a − x)`. Then `t` is a tile of `Φⁿ(t)`, the
patches `Φ^{nk}(t)` increase, and their supports
`[−λ^{nk} x, λ^{nk}(L_a − x))` exhaust the line. The union is a tiling whose
patches lie in the legal words `s^{nk}(a)`; it is fixed by `Φⁿ`, and it is
the only fixed tiling that contains `t`. Different pairs `(a, P)` give
different pairs `(a, x)`. So the fixed tilings of interior type correspond
to the occurrences of `a` in `sⁿ(a)` that are neither first nor last, `a`
running over the letters. Their number is
`Σ_a (|sⁿ(a)|_a − [sⁿ(a) begins with a] − [sⁿ(a) ends with a])`: the first
and the last occurrence are different occurrences because `sⁿ(a) ≠ a` (a
primitive substitution on at least two letters has no letter that is its
own image under a power).

*Vertex type.* Let `0` be a vertex of `T`, with a tile of type `b` on its
left and of type `a` on its right. Then `ba` is legal, and in
`Φⁿ(T) = T` the tiles at the origin are the last tile of `sⁿ(b)` and the
first tile of `sⁿ(a)`: `g_Rⁿ(b) = b` and `gⁿ(a) = a`. Conversely, for such
a legal word the patch `b.a` (seam at the origin) is contained in
`Φⁿ(b.a)`; the increasing union of the `Φ^{nk}(b.a)` is a tiling with legal
patches, fixed by `Φⁿ`, and the only fixed tiling with that seam at the
origin.

With half-open tiles the two types are disjoint and exhaust the fixed
tilings, and `Σ_a |sⁿ(a)|_a = tr(Aⁿ)`. ∎

*Attribution.* This is the count behind the dynamical zeta function of
Anderson–Putnam, restated on the uncollared alphabet; it is standard and no
novelty is claimed. Their text was not read: Baake–Gähler–Grimm
(arXiv:1211.5466, the formula cited there as "[7, Thm. 9.1]";
arXiv:1201.1423 §6: in one dimension `ζ(z) = det(1 − zA₀)/det(1 − zA₁)` for
the action on the cohomology of the Anderson–Putnam complex) were read for
the statement. For `σ ∈ PIP3` the formula agrees with that Lefschetz form:
the map `g_K` of Lemma 7 permutes the cells of the connected graph `ER`,
whose vertices are the periodic last and first letters and whose edges are
the periodic legal seams, so `v_n − a_n − b_n = tr(g_Kⁿ* | H¹(ER)) − 1` for
the three terms of the formula, and
`|Fix(Φⁿ)| = tr(Φⁿ* | H¹(Ω_σ; ℚ)) − 1` by Lemma 7(3).

*Replay.* `kernel/tests/test_fixed_point_count.mojo` compares the formula
with a literal count of reproduced pointed windows (Lemma L of the module
docstring), part by part, for `n = 1, …, 6` on eleven substitutions; the
values are in §12.

## 3. Two elementary lemmas

**Lemma K (power sums bounded above).** Let `f` be a monic complex
polynomial whose power sums `p_n(f) = Σ_i z_iⁿ` over its roots are real, and
let `ρ` be the largest modulus of a root. If `ρ > 1`, there are `c > 0` and
infinitely many `n` with `p_n(f) ≥ c ρⁿ`. In particular, if the `p_n(f)`
are bounded above, every root lies in the closed unit disc; if moreover `f`
has integer coefficients, `f` is neutral.

*Proof.* Let `z_i = ρ e^{2πi θ_i}`, `i ∈ I`, be the roots of modulus `ρ`
(with multiplicity), `k = |I|`. For every `m ≥ 1`, two of the `6^k + 1`
points `(j m θ_i)_{i ∈ I}`, `0 ≤ j ≤ 6^k`, of the torus `(ℝ/ℤ)^k` lie in
one of the `6^k` boxes of side `1/6`; their difference gives `n ≥ m`, a
multiple of `m`, with `n θ_i` within `1/6` of an integer for all `i ∈ I`.
For such `n`, `Re z_iⁿ ≥ ρⁿ cos(π/3) = ρⁿ/2`, the other roots contribute at
least `−(deg f) ρ′ⁿ` with `ρ′ < ρ`, and `p_n(f)` is real, so
`p_n(f) ≥ k ρⁿ/2 − (deg f) ρ′ⁿ`. The last sentence is Kronecker's theorem
(**[Kron]**). ∎

**Lemma U (monomials that are roots of unity).** Let `χ ∈ ℤ[t]` be a monic
irreducible cubic with roots `β > 1 > |α₂|, |α₃|` and constant term
`−det`. For integers `a, b, c` with `a + b + c ≠ 0`, the number
`β^a α₂^b α₃^c` is a root of unity if and only if `a = b = c` and
`|det| = 1`.

*Proof.* Put `x = log β`, `y = −log|α₂|`, `z = −log|α₃|`; all are positive,
and `x − y − z = log|det| ≥ 0`. Let `μ = β^a α₂^b α₃^c` be a root of unity.
The Galois group of an irreducible cubic is transitive on the three roots,
so it contains a 3-cycle, and the conjugates `β^c α₂^a α₃^b` and
`β^b α₂^c α₃^a` of `μ` are roots of unity too. The product of the three is
`det^{a+b+c}`, a rational root of unity; so `|det| = 1` and `x = y + z`.
The moduli of the first and the third give
`(a − b) y + (a − c) z = 0` and `(b − c) y + (b − a) z = 0`. With
`u = a − b`, `v = a − c` these read `u y + v z = 0` and
`(v − u) y − u z = 0`; substituting `u = −v z/y` into the second gives
`v (y + z + z²/y) = 0`. So `v = 0`, then `u = 0`. Conversely, if
`a = b = c` and `|det| = 1`, then `μ = det^a = ±1`. ∎

Irreducibility enters through the 3-cycle, the Pisot property through
`y, z > 0`. *Attribution.* Lemma U is the cubic case of a theorem of
Mignotte (1984): a relation `α₁^{k₁} ⋯ α_d^{k_d} = 1` between the conjugates
of a Pisot number of degree `d` forces `k₁ = ⋯ = k_d` (read as quoted in
Dubickas–Hare–Jankauskas, Lemma 1.1; the original was not read). The
self-contained proof is kept because the source was not.

## 4. The top track: Theorem TT

**Theorem TT.** Let `σ ∈ PIP3`, `P ≥ 1`, `τ = σ^P`, and let `B` be a
primitive bigon system for `τ`, with matrix `N` and pair space `Z`. If
`π₁: Z → Ω_σ` is injective on the points of `Z` that are periodic under
`Φ^P × Φ^P`, then `χ_N / χ_{M^P}` is neutral. If `π₁` is injective, it is a
homeomorphism of `Z` onto `Ω_σ` that conjugates `Φ^P × Φ^P` with `Φ^P`.

*General form.* Let `σ` be any primitive substitution (no irreducibility,
no Pisot hypothesis) and `B` a primitive bigon system for `τ = σ^P` with at
least two members. If `p₁ = π₁ ∘ R` is injective on the `Φ_Σ`-periodic
points of `Ω_Σ`, then the characteristic polynomial of `N` on `ker Pk` is
neutral.

The converse is false (§12, controls `1/012/101` and C-D2).

*Proof.* (a) For `σ ∈ PIP3`, `R` is a homeomorphism of `Ω_Σ` onto `Z`. The
tile boundaries of a tiling of `Ω_Σ` are common vertices of the two entries
of its image, and no common vertex lies inside a tile: for a coincidence
`(a, a)` there is no vertex inside, and for an irreducible noncoincident
pair a common vertex inside would be an equal-Parikh cut by Lemma 1(1). So
the tiles are recovered from the pair as the blocks between consecutive
common vertices, and `R` is a continuous injection of a compact space.

(b) `Pk` is onto and `χ_{M^P}` divides `χ_N`. The image of `Pk` is a
nonzero rational subspace invariant under `M^P` (from `Pk N = M^P Pk`), and
`χ_{M^P}` is irreducible: it is the minimal polynomial of `β^P`, which has
degree 3 (proof of Lemma S). So `Pk` is onto, and
`χ_N = χ_{M^P} · f` with `f` the characteristic polynomial of `N` on
`ker Pk`, monic in `ℤ[t]`.

(c) Counting. `B` has at least three members by (b), `Σ` is primitive, and
`L` is its left Perron row, so Theorem FP applies to `Σ` and gives
`|Fix(Φ_Σⁿ)| ≥ tr(Nⁿ) − 2|B|`. Applied to `σ` with the power `Pn` it gives
`|Fix(Φ^{Pn})| ≤ tr(M^{Pn}) + 9`. By (a) the points of `Z` fixed by
`(Φ^P × Φ^P)ⁿ` are the images of `Fix(Φ_Σⁿ)`, and `π₁` maps them into
`Fix(Φ^{Pn})`. If `π₁` is injective on them for every `n`, then

```text
p_n(f)  =  tr(Nⁿ) − tr(M^{Pn})  ≤  2|B| + 9        for all n ≥ 1,
```

and `f` is neutral by Lemma K.

(d) If `π₁` is injective, its image is closed, flow-invariant and nonempty,
hence all of `Ω_σ` (minimality), and a continuous bijection of compact
Hausdorff spaces is a homeomorphism; `π₁ ∘ (Φ^P × Φ^P) = Φ^P ∘ π₁`.

(e) General form. `p₁` is continuous, commutes with the flow and satisfies
`p₁ ∘ Φ_Σ = Φ^P ∘ p₁`. Let `V` be the image of `Pk`, an `M^P`-invariant
rational subspace. Then `χ_N` is the product of the characteristic
polynomials of `M^P` on `V` and of `N` on `ker Pk`, and by Proposition Q(b),
applied to the substitution `τ`, the characteristic polynomial of `M^P` on
`ℚ^d/V` is neutral, so its power sums are at most `d` in absolute value.
The counting of (c), with `d²` in place of 9, bounds the power sums of the
characteristic polynomial of `N` on `ker Pk` by `2|B| + d² + d`. Lemma K
applies. ∎

*Where the hypotheses enter.* Irreducibility: `R` is injective (`ℓ` is
injective on `ℤ³`) and `Pk` has rank 3. The Pisot property is not used in
the counting. The general form is the one that applies to the reducible
controls; there `R` need not be injective, which is why its hypothesis is
stated for `p₁` on `Ω_Σ`.

## 5. Non-injectivity of the top track: Theorem NI

**Theorem NI.** Let `σ ∈ PIP3`, `τ = σ^P`, and let `B` be a strict
primitive bigon system for `τ` with `B = swap(B)`, with matrix `N`, pair
space `Z` and first defect degree `r = r(B)`.

1. Every eigenvalue of `(M^P)^{⊗r}` on `im D_r` is an eigenvalue of `N_−`.
   Each is `μ^P` for a monomial `μ = β^a α₂^b α₃^c` with `a, b, c ≥ 0`,
   `a + b + c = r`; none is zero; with `μ^P` the `P`-th power of every
   Galois conjugate of `μ` occurs. Moreover `χ_{M^P}` divides `χ_{N_+}`, so
   `χ_{N_−}` divides `χ_N / χ_{M^P}`.
2. If `π₁` is injective on the periodic points of `Z`, then `|det M| = 1`,
   `3 | r`, and every such monomial is `(β α₂ α₃)^{r/3} = (det M)^{r/3}`:
   the only weight on `im D_r` is `(r/3, r/3, r/3)`.
3. For `n ≥ 1` let `F_n = Fix(Φ^{Pn})` and, for `T ∈ F_n`, let `m_n(T)` be
   the number of partners of `T` fixed by `Φ^{Pn}`. Then

   ```text
   Σ_{T ∈ F_n, m_n(T) ≥ 2} (m_n(T) − 1)  ≥  tr(Nⁿ) − tr(M^{Pn}) − 2|B| − 9 .
   ```

   If some eigenvalue of item 1 is not a root of unity (by Lemma U: if `σ`
   is nonunit, or `3 ∤ r`, or some weight is not `(r/3, r/3, r/3)`), then
   the largest modulus `ρ` of a root of `χ_N / χ_{M^P}` exceeds 1, and the
   right-hand side is at least `c ρⁿ` for some `c > 0` and infinitely many
   `n`. Always `ρ ≥ max |μ|^P` over the monomials of item 1, and at `r = 2`,
   `ρ ≥ (β |det M|)^{P/2}`.
4. (Flat variant.) Let instead `B ∩ swap(B) = ∅`. If `π₁` is injective on
   the periodic points of `Z`, then `|det M| = 1` and every weight on
   `im D_r` is `(m, m, m)` or a permutation of `(m + 1, m, m)`.

*Proof.* (1) By (L0), `N` acts on `ℚ^B/ker D_r ≅ im D_r` as
`(M^P)^{⊗r}`. `M` is diagonalisable over `ℂ` with eigenvalues
`β, α₂, α₃`, so the eigenvalues of `(M^P)^{⊗r}` on an invariant subspace
are `P`-th powers of monomials of degree `r`, nonzero because `det M ≠ 0`;
`im D_r` is a rational subspace, so the characteristic polynomial there is
rational and its roots are permuted by the Galois group. Since
`K_r(v, u) = −K_r(u, v)`, `D_r J = −D_r`: `D_r` vanishes on `E_+`, and
`im D_r = D_r(E_−)` is a quotient of `E_−` as an `N`-module. Both
orientations of a pair have the same Parikh vector, so `Pk J = Pk`, `Pk`
vanishes on `E_−` and maps `E_+` onto `ℚ³` (step (b) of the proof of
Theorem TT); hence `χ_{M^P} | χ_{N_+}`, and `χ_N = χ_{N_+} χ_{N_−}`.

(2) By Theorem TT, `χ_N/χ_{M^P}` is neutral, hence so is `χ_{N_−}`; every
`μ^P` of (1) is a nonzero root of it, hence a root of unity, hence so is
`μ`. Lemma U gives `a = b = c` and `|det M| = 1`.

(3) Every point of `Z` fixed by `(Φ^P × Φ^P)ⁿ` lies over a point of `F_n`,
so `Σ_{T ∈ F_n} m_n(T)` is the number of such points, which is
`|Fix(Φ_Σⁿ)| ≥ tr(Nⁿ) − 2|B|` (steps (a), (c) of the proof of Theorem TT),
and `|F_n| ≤ tr(M^{Pn}) + 9`. Subtract, and drop the terms with
`m_n(T) ≤ 1`, which are not positive. The right-hand side is
`p_n(f) − 2|B| − 9` for `f = χ_N/χ_{M^P}`. If some `μ^P` is not a root of
unity, the monic integer polynomial `χ_{N_−}` is not neutral, so by
**[Kron]** it has a root of modulus greater than 1, and so does `f`; apply
Lemma K. The roots of `f` include those of `χ_{N_−}`. At `r = 2`,
`im D₂ = Λ²ℚ³` (R1(b), for `τ`), with eigenvalues `(β α₂)^P`, `(β α₃)^P`,
`(α₂ α₃)^P`; the product of the first two moduli is `(β |det M|)^P`.

(4) Now `N` has the eigenvalues `μ^P` of `(M^P)^{⊗r}` on `im D_r` by (L0),
and `χ_N/χ_{M^P}` is neutral by Theorem TT. Each `μ^P` is a root of
`χ_N/χ_{M^P}` or of `χ_{M^P}`. In the first case `μ` is a root of unity and
Lemma U gives the weight `(m, m, m)` and `|det M| = 1`. In the second,
`μ^P` is `β^P`, `α₂^P` or `α₃^P`, so `μ/β`, `μ/α₂` or `μ/α₃` is a root of
unity; it is a monomial of exponent sum `r − 1 ≥ 1`, and Lemma U gives a
permutation of `(m + 1, m, m)` and `|det M| = 1`. ∎

*Remarks.* (i) Item 1 is not new: `N_−` is the signed matrix `S` of the
orientation-spectrum note (its Proposition 1: the oriented double cover acts
as `N` on the deck-even and as `S` on the deck-odd sector; §3: the Parikh
quotient is deck-even), and "`D_r` factors through the odd sector" is the
signed intertwiner `Q_r S = Φ_r Q_r` of the
[lowest-defect note](c4-lowest-defect-intertwiner.md) §§1–4 read on ordered
pairs. New are items 2–4. (ii) In item 3 the number `m_n(T)` is at most
`K − 1`, with `K` the uniform bound on the fibres of `h_φ` (BBK Thm 4.2),
because partners are fibre-mates (Lemma 8 (Z4), §6.1). So at least
`c ρⁿ/(K − 1)` tilings fixed by `Φ^{Pn}` have two fixed partners.
(iii) `(β |det M|)^{1/2}` is the exact modulus of `β α₂`, `β α₃` only for a
complex pair; in general `|β α₂| = |det M|/|α₃|` and
`|β α₃| = |det M|/|α₂|` both exceed `|det M| ≥ 1`, and `α₂ α₃ = det M/β`
is contracting. (iv) Compared with Theorem Fork, item 3 needs no hypothesis
on the determinant or on `dim H¹`, and its conclusion is weaker: the second
partner may be eventually coincident with the first.

## 6. The structure at coincidence rank two: Theorem W

### 6.1 Lemma 8 holds for every determinant

Lemma 8 of the (F)-class note (strict components: a compact set
`Z ⊆ Ω_σ × Ω_σ` with (Z1)–(Z4) for some `P`) is stated there in a section
whose standing assumptions are `|det M| = 1` and `dim H¹ = 3`. Its proof
uses neither, and it is used below for every `σ ∈ PIP3`. The only step where
the determinant could matter is (Z4), `g_max(T) = g_max(T′)` for
`(T, T′) ∈ Z`, read as `h_φ(T) = h_φ(T′)`. For nonunit `σ` the target is the
solenoid `𝕋_A` and `h_φ(T)` records a vertex class of `Φ^k(T)` for every
`k ∈ ℤ`. For the pair `(T₀, T₀′)` of (Z3), fixed by a power of `Φ` with a
common vertex at the origin, every member of the `Φ`-orbit of each strand
has a vertex at `0 ∈ ℤ³`, so `h_φ(T₀) = h_φ(T₀′)` is the identity of
`𝕋_A`; equivariance under the flow and density of the orbit of
`(T₀, T₀′)` in `Z` give (Z4). The construction in the proof of Lemma 8 shows
more: **the pair space of a strict primitive bigon system is a strict
component**, and every strict system yields one.

### 6.2 Statement

**Theorem W (the rank-two wall).** Let `σ ∈ PIP3` with `cr(σ) = 2` have a
strict system.

- **(W1) Uniqueness.** There is exactly one strict component `Z`. It is
  invariant under `Φ × Φ` and under the swap. The set `B` of blocks between
  consecutive common vertices of the pairs of `Z` is a strict bigon system
  for `σ` itself (`P = 1`), `B = swap(B)`, and the child substitution of
  `σ` on `B` is primitive. For every `m ≥ 1`, every sink strongly connected
  component of the child graph of every strict system for `σ^m` is `B`.
- **(W2) Injectivity almost everywhere.** If the fibre of `h_φ` through
  `T` has two elements, `T` has exactly one partner. This holds on a set of
  full measure for the invariant measure of the flow.
- **(W3) Strict odd contraction.** Let `N` be the matrix of the child
  substitution of `σ` on `B`. Then `χ_M | χ_{N_+}` and `ρ(N_−) < β`.
  Consequently every eigenvalue of `M^{⊗r}` on `im D_r`, `r = r(B)`, has
  modulus less than `β`, and it is a monomial of weight `(m, m, m)`, which
  needs `|det M|^m < β`, or of a weight that is a permutation of
  `(m + 1, m + 1, m)`, which needs `|det M|^m max(|α₂|, |α₃|) < 1`. In
  particular `r ≢ 1 (mod 3)`.
- **(W4) Partners are coincident.** If `T′` and `T″` are partners of one
  `T`, the set of `v ∈ ℝ` such that for some `k` the tilings `Φ^k(T′)`,
  `Φ^k(T″)` share a tile with `β^k v` in its interior is open and dense,
  and `h_φ(T′) = h_φ(T″)`. In the notation of B15 §3 (with `g_max = h_φ`,
  **[Std]**): `T′ ≈_s T″`. Unless `σ` is unit and `3 | r`, some `T` has two
  different partners, so `≈_s` is not trivial on `Ω_σ`, and Theorem NI(3)
  holds with `P = 1`.

Imports: Lemma 8, Lemma 6, Lemma 1 (RepoF); BBK Prop. 2.3, Def. 3.1,
Def. 4.1, Thm 4.2; for (W3) identity (L0) and R0; for the wording of (W4)
in Barge's terms B15 §3 and one **[Std]** fact.

### 6.3 Proof

*(W1).* By BBK Thm 4.2 there is a point `q ∈ 𝕋_A` whose fibre has exactly
two elements; since `h_φ(Ω_σ) = 𝕋_A`, one of them, `T`, is in `Ω_σ`. Let
`Z₁` be a strict component. Its first projection is closed, flow-invariant
and nonempty, hence all of `Ω_σ`, so `(T, T′) ∈ Z₁` for some `T′`. By (Z4),
`T′` is in the fibre of `T`, and `T′ ≠ T` by (Z2). So the fibre is
`{T, T′}`, and every strict component contains the pair `(T, T′)`. Strict
components are minimal for the diagonal flow, so two of them that share a
point are equal.

The sets `swap(Z)` and `(Φ × Φ)(Z)` are again compact, invariant and
minimal for the diagonal flow, their pairs share no tile at any level, have
relatively dense common vertices and lie in one fibre
(`h_φ ∘ Φ` is the shift of `h_φ`); they are strict components, hence equal
to `Z`.

By §6.1 and uniqueness, `Z` is the pair space of a strict primitive bigon
system `C₀` for some `σ^P`, and by step (a) of the proof of Theorem TT the
members of `C₀` are exactly the blocks between consecutive common vertices
of pairs of `Z`: `B = C₀` is finite, and its words are legal. `B = swap(B)`
because `swap(Z) = Z`. `B` contains the `σ`-children of its members: if
`(u, v) ∈ B` occurs in `(T, T′) ∈ Z` between the consecutive common vertices
`x < y`, then `(Φ T, Φ T′) ∈ Z` carries `(σ(u), σ(v))` between the common
vertices `β x`, `β y`; by Lemma 1(1) the common vertices in between are the
equal-Parikh cuts of `(σ(u), σ(v))`, so its irreducible factors are blocks
of a pair of `Z`. None is coincident, by (Z2). So `B` is a strict bigon
system for `σ`.

Let `C′` be a sink strongly connected component of the child graph of `σ`
on `B`, of period `q′`, and `C₀′` one of its cyclic classes. The child
substitution of `σ^{q′}` on `C₀′` is primitive, so `C₀′` is a strict
primitive bigon system for `σ^{q′}`; its pair space is a strict component,
hence `Z`, and its set of blocks is `C₀′`. So `C₀′ = B`, hence `C′ = B`
and `q′ = 1`: the child graph of `σ` on `B` is strongly connected and
aperiodic, i.e. the child substitution is primitive.

Finally let `𝒞` be a strict system for `σ^m` and `C′` a sink of its child
graph. The proof of Lemma 8, started from `C′`, produces a strict primitive
bigon system `C₀″ ⊆ C′` for a power of `σ^m` whose pair space is a strict
component; so `C₀″ = B` and `B ⊆ C′`. `B` contains the `σ^m`-children of
its members (the irreducible factors of `(σ^m(u), σ^m(v))` are iterated
`σ`-children), and `C′` is strongly connected, so `C′ ⊆ B`.

*(W2).* If the fibre of `T` is `{T, T*}`, every partner of `T` is a
fibre-mate different from `T`, hence `T*`, and `T` has a partner. The set of
such `T` is the preimage of a set of full Haar measure, and `h_φ` maps the
invariant measure of the uniquely ergodic flow on `Ω_σ` to Haar measure.

*(W3).* `N` is primitive by (W1), commutes with `J`, and has spectral
radius `β` with a positive left eigenvector `L` (R0). Its right Perron
vector is unique up to a factor, so it is fixed by `J` and lies in `E_+`;
the Perron root is simple and every other eigenvalue has smaller modulus,
so `ρ(N_−) < β`. `χ_M | χ_{N_+}` is Theorem NI(1). By Theorem NI(1) the
eigenvalues of `M^{⊗r}` on `im D_r` are eigenvalues of `N_−`, and with a
monomial `β^a α₂^b α₃^c` its two cyclic rotations occur. With `x, y, z` as
in the proof of Lemma U and `δ = log|det M| = x − y − z ≥ 0`, the logarithm
of the modulus of `β^a α₂^b α₃^c`, minus `x`, is

```text
(a − 1 − b) y + (a − 1 − c) z + (a − 1) δ .
```

Take the rotation with the largest exponent `a` on `β`; `a ≥ 1`. The
expression must be negative, so `b = a` or `c = a`. If `b = c = a`, the
weight is `(m, m, m)`, the eigenvalue is `(det M)^m`, and the condition is
`|det M|^m < β`. If `b = a > c`, put `k = a − 1 − c ≥ 0`; the rotations
`(a, a, c)` and `(a, c, a)` give `−y + k z + (a − 1) δ < 0` and
`k y − z + (a − 1) δ < 0`, and their sum `(k − 1)(y + z) + 2(a − 1) δ < 0`
forces `k = 0`. So the weight is `(m + 1, m + 1, m)` with `m = c`, and the
two inequalities read `|det M|^m |α₂| < 1` and `|det M|^m |α₃| < 1`. The
case `c = a > b` is symmetric. Hence `r = 3m` or `r = 3m + 2`.

(The prover's record lists a third condition for `(m + 1, m + 1, m)`,
`|det M|^{m+1} < β²`, from the rotation `(m, m + 1, m + 1)`. It follows
from the other two: that rotation has modulus
`|det M|^m |α₂| |α₃| < |α₃| < 1`.)

*(W4).* Let `U` be the set of the statement; it is open. Suppose it is not
dense: there is an open interval `I` disjoint from `U`. Fix `v₀ ∈ I` and a
sequence `k_i → ∞` such that `Φ^{k_i}` of `T − v₀`, `T′ − v₀`, `T″ − v₀`
converge, to `S`, `S′`, `S″`. `Z` is closed and invariant under the flow and
`Φ × Φ`, so `(S, S′), (S, S″) ∈ Z`; the three limits are fibre-mates, and
`S`, `S′` (resp. `S`, `S″`) share no tile at any level by (Z2). Neither do
`S′`, `S″`. Fibre-mates have strands whose vertices differ by elements of
`ℤ³` and stay in a bounded neighbourhood of the expanding line, so by
Lemma 1(1) there is `δ₀ > 0` such that two vertices of fibre-mates at
distance less than `δ₀` are equal. If `Φⁿ(S′)` and `Φⁿ(S″)` shared a tile,
then for `i` large `Φ^{k_i+n}(T′ − v₀)` and `Φ^{k_i+n}(T″ − v₀)`, which are
fibre-mates, would contain tiles of the same type within `δ₀` of it and of
each other, hence a common tile, inside `β^{k_i+n}(I − v₀)`; a point of its
interior is `β^{k_i+n}(v − v₀)` with `v ∈ I`, and then `v ∈ U`. So `S`,
`S′`, `S″` are three strands over one point of `ℝ³/ℤ³`, pairwise
non-coincident (for fibre-mates a shared tile and a shared labelled edge
are the same thing, by Lemma 1(1)), against `cr(σ) = 2` and BBK Def. 4.1.
`h_φ(T′) = h_φ(T) = h_φ(T″)` is (Z4). By B15 Thm 4(3), `U` is contained in
`{v : T′ − v ∼_s T″ − v}`, which gives the wording `T′ ≈_s T″`.

If `σ` is not unit or `3 ∤ r`, `π₁` is not injective by Theorem NI(2)
applied to `B` with `P = 1`, so some `T` has two partners `T′ ≠ T″`. ∎

*Remarks.* (i) (W4) is the first half of the proof of B15 Lemma 13, which
does not use the hypothesis that `≈_s` is trivial; nothing in it is new.
(ii) (W1) contains the contrapositive of Theorem FL at coincidence rank two
("every ordered sink is swap-symmetric") and adds uniqueness of the sink
and primitivity for `σ` itself. (iii) In (W3) only the link is new. On main,
`ρ(S) ≤ β` with equality only in the gauge and anti-gauge cases is
manuscript `prop:cocycle` and Proposition 3 of the orientation-spectrum
note; "strict odd contraction forces `r ≡ 0` or `2 (mod 3)`" is the
non-extremal case of manuscript `thm:sieve`, §8 of the multidegree-sieve
note and Corollary B of the [degree-four note](c4-degree4-free-lie.md)
(those three texts print it for three-state components or for `r = 4`; the
argument uses only that the first-defect image is a quotient of the odd
sector), with Lean `no_strictComponent_deg4_of_hasBothSigns` for the
mixed-sign case at `r = 4`; the side conditions are the strict forms of
§4.1 and §4.3 of the multidegree-sieve note. New is that coincidence rank
two forces the primitive, swap-symmetric, strictly contracted case for the
unique component. (iv) For nonunit `σ` the side conditions are restrictive:
`(m, m, m)` needs `β > |det M|^m`, and `(m + 1, m + 1, m)` with `m ≥ 1`
needs `β > |det M|^{2m+1}` (multiply the two inequalities and use
`|α₂ α₃| = |det M|/β`).

## 7. Barge's ordered-pair substitution at rank two: Lemma S+ and Theorem P+

Let `σ ∈ PIP3` with `cr(σ) = 2` and `n` admissible. As in §5.2 of the
(F)-class note, (B1)–(B6): `φ′` is the proper version of `σⁿ`, `φ′_s` its
stack substitution, `q: Ω_σ → Ω_s := Ω_{Φ′_s}` the quotient by `≈_s`,
`ψ = (φ′_s)_op` the substitution on ordered pairs of overlapping tiles of a
tiling of `Ω_s` and its twin, `ι` the exchange of the two entries (a
fixed-point-free involution of the alphabet of `ψ` commuting with `ψ`), and
`[[X, Y], [Y, X]]` the incidence matrix of `ψ`. `nz χ` is a characteristic
polynomial with its factors `t` removed. For a letter `c` of `ψ`, `g_ψ(c)`
and `g_{ψ,R}(c)` are the first and last letters of `ψ(c)`.

**Lemma S+ (the eventual range of `ψ`).** In this setting:

1. `ER(ψ)` consists of two edges `e_{x₁y₁}` and `e_{ι(x₁) ι(y₁)}`, each
   fixed by the map `g_K` of `ψ`, without a common vertex and exchanged by
   `ι`. Hence `G_0(ψ)` has rank 1, the induced map is the identity on it,
   and `G_3(ψ) = 0`. Every letter `c` satisfies
   `g_{ψ,R}^m(c) ∈ {x₁, ι(x₁)}` and `g_ψ^m(c) ∈ {y₁, ι(y₁)}` for `m` large,
   and for a legal word `cd` of `ψ`, `g_{ψ,R}^m(c) = x₁` iff
   `g_ψ^m(d) = y₁`.
2. The integer row vector `w_c = [g_{ψ,R}^m(c) = x₁] − [g_ψ^m(c) = y₁]`
   (`m` large) is nonzero, satisfies `w ∘ ι = −w` and is a left eigenvector
   of the incidence matrix of `ψ` for the eigenvalue 1. So 1 is an
   eigenvalue of `X − Y`.
3. The substitution acts on `H¹(Ω_ψ; ℚ)` with characteristic polynomial
   `nz χ_{X+Y} · nz χ_{X−Y} / (t − 1)`.
4. Write `nz χ_{X+Y} = χ_{Mⁿ} · r` (Lemma S) and
   `nz χ_{X−Y} = (t − 1) · q₁`. Then `r` and `q₁` are monic integer
   polynomials whose roots are roots of unity, and `r · q₁` divides `c_n`.
5. Let `h_n` be the part of `χ_{Mⁿ} mod 2` prime to `t`. In `𝔽₂[t]`, with a
   bar for reduction mod 2: `h_n · r̄ = (t + 1) · q̄₁`.

Imports: those of Lemma S (B15 as printed: the proper version, Thm 4(5),
Thm 5, Thm 12, Lemmas 13–14, Prop. 19, Lemma 20, and the count of periodic
words in the proof of Thm 22; BD08; the identification of the ranks), and
BD08 Theorem 4 with its proof and Theorem 4′.

*Proof.* (1) An edge `e_{xy}` of the transition graph `S` of `ψ` lies in
`ER(ψ)` iff it is periodic under `g_K`, i.e. iff `xy` is legal, `x` is
periodic for `g_{ψ,R}` and `y` for `g_ψ`. Such an edge is the seam of the
allowed bi-infinite word `lim ψ^{kj}(x).ψ^{kj}(y)`, which is periodic under
`ψ`, and two periodic allowed words with the same seam are equal. By the
proof of B15 Thm 22 there are exactly two allowed bi-infinite words
periodic under `ψ`; they are fixed, and `ι` exchanges them. So `ER(ψ)` has
exactly two edges, `e_{x₁y₁}` and its image under `ι`, both fixed. `ι` has
no fixed letter, so `ι(x₁) ≠ x₁` and `ι(y₁) ≠ y₁`: the edges have no common
vertex. `G_0(ψ)` is the limit of the reduced `H⁰`, of rank one less than
the number of components, generated by the class of `v_C` for
`C = e_{x₁y₁}` (BD08, proof of Theorem 4), and the induced map fixes it
because `g_K` fixes both components; `G_3(ψ)` is `H¹(ER)`, which vanishes.
A power `g_K^m` maps `S` into `ER(ψ)`. Every letter occurs in a legal
two-letter word on either side, which gives the two memberships; and for a
legal `cd`, `g_K^m(e_{cd})` is one of the two edges of `ER(ψ)`.

(2) By BD08 (proof of Theorem 4, and Theorem 4′), the image of `v_C` in
`H¹(K, S) ≅ ℤ^{letters}` is the sum of the dual classes of the letter edges
that end in a component of `S` mapped into `C` by `g_K^m`, minus the sum
over those that start in one; the letter edge of `c` ends at the vertex
shared by the transition edges `e_{cd}` and starts at the one shared by the
`e_{bc}`. This is the vector `w`. The equation `w M_ψ = w` is the
equivariance of the coboundary; directly, for `ψ(c) = d₁ ⋯ d_k`,
`(w M_ψ)_c = Σ_i w_{d_i}` telescopes by the last statement of (1) to
`[g_{ψ,R}^m(d_k) = x₁] − [g_ψ^m(d₁) = y₁] = w_c`. `ι` commutes with `ψ` and
exchanges `x₁` with `ι(x₁)` and `y₁` with `ι(y₁)`, so by the memberships
of (1) `w_{ι(c)} = (1 − [g_{ψ,R}^m(c) = x₁]) − (1 − [g_ψ^m(c) = y₁])
= −w_c`. If `w` were zero, every letter would be of one of two types
(ends in `x₁` and begins in `y₁`; or ends in `ι(x₁)` and begins in
`ι(y₁)`), a legal word would consist of letters of one type by (1), and
`ι` exchanges the types; but every tiling of the minimal space `Ω_ψ`
contains every letter. Writing `w = (w₁, −w₁)`,
`w M_ψ = w` reads `w₁ (X − Y) = w₁`.

(3) By (1) the sequence of BD08 for `ψ` is
`0 → G_0 → G_1 → H¹(Ω_ψ) → 0`. On `G_1 ⊗ ℚ`, the eventual range of the
transposed incidence matrix, the characteristic polynomial is
`nz χ_{X+Y} · nz χ_{X−Y}` ((B5)), and on `G_0 ⊗ ℚ` it is `t − 1`.

(4) By Lemma S and its proof, `H¹(Ω_ψ; ℚ)` embeds equivariantly in
`H¹(Ω_σ; ℚ)` with `Φⁿ*`, whose characteristic polynomial is `χ_{Mⁿ} c_n`,
and `χ_{Mⁿ}` divides `nz χ_{X+Y}`. So `χ_{Mⁿ} · r · q₁` divides
`χ_{Mⁿ} · c_n`. Divisibility of monic integer polynomials over `ℚ` is
divisibility over `ℤ`.

(5) `X − Y ≡ X + Y (mod 2)`, so `χ_{X−Y}` and `χ_{X+Y}` agree in `𝔽₂[t]`.
The constant terms of `r` and `q₁` are `±1` (integers that are products of
roots of unity), so `r̄` and `q̄₁` are prime to `t`. Compare the parts prime
to `t`. ∎

Lemma S+ sharpens Lemma S: in the notation there `ε = 1`, the sign is `+`,
and the removed factor `t − 1` sits in `X − Y`.

**Theorem P+ (parity, every determinant).** Let `σ ∈ PIP3` and

```text
d₂  :=  3 − ord_t(χ_M mod 2)  =  3 if det M is odd;  2 if det M is even and e₂(M) odd;
        1 if det M, e₂(M) are even and tr M odd;  0 if all three are even,
```

the number of nonzero roots of `χ_M mod 2` in an algebraic closure of `𝔽₂`.
If `cr(σ) = 2`, then

1. `dim H¹(Ω_σ; ℚ) ≥ 3 + |d₂ − 1|`;
2. (divisor condition) for every admissible `n` there are monic
   `r, q₁ ∈ ℤ[t]` with `r · q₁ | c_n` and `h_n · r̄ = (t + 1) · q̄₁`, where
   `h_n` has degree `d₂`.

Imports: those of Lemma S+.

*Proof.* `χ_{Mⁿ} mod 2` is the characteristic polynomial of
`(M mod 2)ⁿ`, whose nonzero eigenvalues are the `n`-th powers of those of
`M mod 2`; so `deg h_n = d₂` for every `n`. (2) is Lemma S+(4), (5). For
(1) compare degrees: `d₂ + deg r = 1 + deg q₁` and
`deg r + deg q₁ ≤ deg c_n = l`. Hence `deg r ≥ max(0, 1 − d₂)` and
`l ≥ 2 deg r + d₂ − 1 ≥ |d₂ − 1|`. ∎

*What it contains.* For `d₂ = 3` (odd determinant) item 1 is `l ≥ 2`, which
is B15 Thm 22 for `d = 3`, and item 2 at `n = 6`, where `c₆ = (t − 1)^l`,
is Theorem P. For even determinant item 1 gives `l ≥ 1` when `d₂ ∈ {0, 2}`
and nothing when `d₂ = 1`; that bound is contained in Theorem H3 below,
which gives `l ≥ 1` for every determinant. So for even determinant the
content of Theorem P+ beyond Theorem H3 is the divisor condition, which is
not implemented in the kernel (§12). *Attribution.* The mechanism (a
symmetric matrix `[[X, Y], [Y, X]]`, the eigenvalue 1 from the components of
the eventual range, and a parity count) is that of the
Barge–Bruin–Jones–Sadun theorem `not2` ("a homological Pisot substitution
with `d = 1` has coincidence rank different from 2", proved there for even
norm by this count), transplanted into Barge's ordered-pair substitution;
B15 Thm 22 is the odd-norm case.

## 8. Rank two is excluded at `dim H¹ = 3`: Theorem H3

**Lemma 9′ (classes are eigenfunction classes; every determinant).** Let
`σ ∈ PIP3` with `dim H¹(Ω_σ; ℚ) = 3`.

- (a) Every class of `Ȟ¹(Ω_σ; ℤ) = [Ω_σ, S¹]` is the class of a continuous
  eigenfunction of the flow.
- (b) If `cr(σ) ≥ 2`, let `Ω_s` be Barge's quotient of `Ω_σ` by `≈_s` (the
  stack tiling space of the proper version of a power, B15 Thm 12) and
  `g_s: Ω_s → 𝕋_max` its maximal equicontinuous factor map. Every
  continuous map `Ω_s → S¹` is homotopic to a continuous eigenfunction of
  the flow on `Ω_s`, and every such eigenfunction is constant on the fibres
  of `g_s`.

Lemma 9 of the (F)-class note is the case `|det M| = 1`. Lemma 9′ is **not
new**: it follows from Barge–Kellendonk–Schmieding 2012, Corollary 3 and
Theorem 5, as the first proof shows.

*First proof (BKS).* Let `X` be `Ω_σ` or `Ω_s`; both are tiling spaces of
primitive non-periodic substitutions (B15 Thm 12(1) for `Ω_s`), with
minimal, uniquely ergodic flows. Let `E_X ⊂ ℝ` be the group of eigenvalues
of continuous eigenfunctions and `θ: E_X → [X, S¹]`, `θ(η) = [f_η]`, the
class of an eigenfunction of modulus one. By BKS Corollary 3, `θ` is
injective, and by BKS Theorem 5 its cokernel is torsion free. The rank of
`E_X` is at least 3: for `u ∈ ℤ³`, `χ_u ∘ h_φ` is a continuous
eigenfunction on `Ω_σ` with eigenvalue `u·r` (BBK (5.3), (3.12)), `u ↦ u·r`
is injective on `ℚ³` (the entries of `r` are ℚ-independent), and a
continuous eigenfunction on `Ω_σ` factors through `g_max = g_s ∘ q` (B15 §2
and Thm 12(4)), hence defines one on `Ω_s` with the same eigenvalue. The
rank of `[X, S¹] = Ȟ¹(X; ℤ)` (**[Std]**) is at most 3: for `Ω_σ` by
hypothesis, for `Ω_s` because `q*` is injective on rational `H¹` (B15
Prop. 19). So the cokernel of `θ` is a torsion group, hence zero: (a), and
the first statement of (b). An eigenfunction on `Ω_s` factors through `g_s` by
maximality (B15 §2, Thm 12(4)). ∎

*Second proof of (a) (the route's own; kept because it identifies the
classes).* `G_0 = 0` (Lemma 7(2)) and `G_3 = 0` (`l = 0`), so by BD08
Theorem 4 over `ℤ`, `Ȟ¹(Ω_σ; ℤ) ≅ lim→(ℤ³, Mᵗ)`. Its element `[e_a, k]` is
the class of the map that winds once around the circle each time the origin
passes through a level-`k` supertile of type `a`, i.e. through a tile of
type `a` of `Φ^{−k}(T)`. **[Std]** The winding number along the flow is a
homomorphism `W: Ȟ¹(Ω_σ; ℤ) → ℝ`, and `W([e_a, k]) = r_a β^{−k}`, so
`W([v, k]) = ((Mᵗ)^{−k} v)·r`. `W` is injective, because the entries of `r`
are ℚ-independent. The characters of `𝕋_A` are the `χ_u`,
`u ∈ ⋃_k (Mᵗ)^{−k} ℤ³` (BBK (5.1)–(5.3) with Lemma 6), and
`W([χ_u ∘ h_φ]) = u·r` up to the sign convention of the flow. The two
images of `W` coincide, so every class is some `[χ_u ∘ h_φ]`. For `Ω_s` this
route then needs injectivity of `q*` on integral `H¹` (Gottschalk–Hedlund,
**[Std]**, as in Lemma 9(iv)). ∎

**Theorem H3.** Let `σ ∈ PIP3` with `dim H¹(Ω_σ; ℚ) = 3`. Then
`cr(σ) ≠ 2`, for every determinant.

For odd determinant this is B15 Thm 22 (`cr = 2` forces `dim H¹ ≥ 5`). It
is new only for even determinant. B15 Cor. 25 must not be cited for it: that
corollary is about asymptotic cycles, and `dim H¹ = 3` is not "no asymptotic
cycle" ([`dim H¹` census note](c4-h1-census-2026-11-05.md) §6).

Imports: B15 (the proper version, §4; Thm 4(5); Thm 12; Lemmas 13–15;
Thm 17; Prop. 19); Lemma 9′(b) (BKS Corollary 3 and Theorem 5; BBK (5.3));
the **[Std]** facts on line bundles and dimension, `Ȟ¹ = [X, S¹]` and the
identification of the two ranks.

*Proof.* Suppose `cr(σ) = 2`. Then the flow does not have pure discrete
spectrum, `Ω_s` is defined, `cr(Φ′_s) = 2` and `≈_s` is trivial on `Ω_s`
((B2), (B4) of the (F)-class note). By B15 Lemma 13 every `T ∈ Ω_s` has a
unique twin `ι(T)`, regionally proximal to `T` and disjoint from it. `ι` is
a homeomorphism of `Ω_s` (it is the exchange of entries on
`Ω_ψ ≅ Ω_s`, B15 Lemma 14), an involution without fixed points, it commutes
with the flow, and `g_s ∘ ι = g_s` because regionally proximal tilings have
the same image in the maximal equicontinuous factor (B15 §2). The quotient
`Ω_s/ι` is a one-dimensional substitution tiling space (B15 Lemma 15,
Thm 17), of covering dimension one **[Std]**, so the complex line bundle
`(Ω_s × ℂ)/((T, c) ∼ (ι T, −c))` over it is trivial **[Std]**: there is a
continuous `z: Ω_s → S¹` with `z ∘ ι = −z`.

By Lemma 9′(b), `z = f · exp(2πi φ)` with `f` an eigenfunction that is
constant on the fibres of `g_s` and `φ: Ω_s → ℝ` continuous. Then
`f ∘ ι = f`, so `exp(2πi (φ ∘ ι − φ)) = −1`: the continuous function
`φ ∘ ι − φ` takes values in `1/2 + ℤ` and is a constant `c` on the
connected space `Ω_s`. Applying `ι` once more, `φ − φ ∘ ι = c`, so
`c = −c`, `c = 0`. This is not in `1/2 + ℤ`. ∎

The argument is Lemma 10 of the (F)-class note at `p = 2`, applied to
Barge's twin involution, with Lemma 9′(b) in place of Lemma 9. With that
replacement the proof of Lemma 10 goes through word for word, so **Lemma 10
holds for every `σ ∈ PIP3` with `dim H¹ = 3` and `cr ≥ 2`**, unit or not.

*Where the hypotheses enter.* `dim H¹ = 3` and irreducibility: the group of
eigenvalues has rank 3, the rank of `H¹` (the entries of `r` are
ℚ-independent). The Pisot property: BBK and B15. The determinant is not
used.

*Remark (an explicit sheet function; added while this note was written,
not seen by the verifiers).* The function `z` can be written down on
`Ω_ψ ≅ Ω_s` from Lemma S+(1), which replaces the two **[Std]** facts on
bundles and dimension by the count of periodic words in the proof of B15
Thm 22. Put `a_c = 0` if `g_ψ^m(c) = y₁` and `a_c = 1` if
`g_ψ^m(c) = ι(y₁)`, `e_c = 0` if `g_{ψ,R}^m(c) = x₁` and `e_c = 1`
otherwise, and `b_c ∈ {0, 1}` with `b_c ≡ e_c − a_c (mod 2)`. For a tiling
with the origin at position `t` of a tile of type `c` and length `L_c`, let
`z = exp(πi (a_c + b_c t/L_c))`. At the right end of the tile the value is
`exp(πi e_c) = exp(πi a_d)` for the next tile `d`, by the last statement of
Lemma S+(1), so `z` is continuous; and `a_{ι(c)} = 1 − a_c`,
`b_{ι(c)} = b_c`, so `z ∘ ι = −z`.

**Corollary (dimension).** For `σ ∈ PIP3`, `cr(σ) = 2` forces
`dim H¹ ≥ 4`, and `dim H¹ ≥ 5` when `det M` is odd (B15 Thm 22).

**Corollary FC3+ (class theorem, every determinant).** Let `σ ∈ PIP3`
satisfy (F) and `dim H¹(Ω_σ; ℚ) = 3`. Then `cr(σ) = 1`: the tiling flow has
pure discrete spectrum, all pairs of letters are left and right strongly
coincident, and `σ` has no strict system. The same holds if `σ` satisfies
(F) and violates a necessary condition of Theorem P+.

*Proof.* `cr(σ) = ν_L = ν_R ≤ 2` by Theorem FC2, and `cr(σ) ≠ 2` by
Theorem H3, resp. Theorem P+. Then conclude as in Theorem FC3. ∎

Imports: those of Theorem FC2 and Theorem H3 (resp. P+); BBK Cor. 5.2;
Theorem A(4). For odd determinant this is clause (b) of Theorem FC3; the
new case is even determinant. The regression's contract cites it as
"Theorem FC3+".

**Corollary N+ (necessary conditions, every determinant).** Let
`σ ∈ PIP3` have a strict system and `dim H¹(Ω_σ; ℚ) = 3` (or violate a
necessary condition of Theorem P+). Then `cr(σ) ≥ 3`, (F) fails, and there
is an interior periodic address.

*Proof.* `cr ≥ 2` by Theorem N(1), `cr ≠ 2` by Theorem H3 (resp. P+), and
under (F) `cr ≤ 2` (Theorem FC2(2)); the interior address is Lemma 4(1), as
in the proof of Theorem N(2). ∎

*Theorem Fork for nonunit `σ` with `dim H¹ = 3`: expected, not proved.* The
proof of Theorem Fork uses unimodularity in Lemma 9 and in the first
paragraph of §7 of the (F)-class note, where the maximal equicontinuous
factor is the torus. Lemma 9′ and Lemma 10 now hold for every determinant.
Steps 1–4 of the proof of Theorem Fork were not rewritten with the solenoid
`𝕋_A` in place of the torus; the logic verifier reports having re-derived
them, the prior-art verifier did not, and no proof text exists. The
extension is recorded as expected and is used nowhere.

*Remark (not recorded as a statement; literature-facing and unreviewed).*
The proof of Theorem H3 uses the class PIP3 only through "the group of
eigenvalues has rank 3 and so has `H¹`". Read for a general one-dimensional
Pisot substitution with dilation of degree `d` and `dim H¹ = d`
("homological Pisot"), the same steps would give `cr ≠ 2` for every degree
and every norm, which is stronger than the printed statements (B15 Cor. 23;
the theorem `not2` for `d = 1`). Likewise the degree count of Theorem P+
reads `dim H¹ ≥ d + |d₂ − 1|` there. Neither was written out or checked
against the literature beyond the sources of the stop/go note, and neither
is claimed.

## 9. Obstruction T: the first-defect class does not descend

Round 1's Lemma S says that at coincidence rank two every nonzero eigenvalue
of Barge's `X − Y` is a root of unity. The first defect of a strict
component has eigenvalues on the swap-odd sector `N_−` that are not roots
of unity unless `σ` is unit and the weights are `(m, m, m)` (Lemma U). The
proposed route was to transport the defect class to Barge's quotient and
contradict Lemma S. It fails at its first premise.

**Obstruction T.** Let `σ ∈ PIP3` with `cr(σ) = 2` have a strict system,
with `Z`, `B`, `N`, `r` as in Theorem W, and let `μ` be an eigenvalue of
`M^{⊗r}` on `im D_r` that is not a root of unity. Then for every `n ≥ 1`
the generalised eigenspace of `(Φⁿ × Φⁿ)*` on `H¹(Z; ℂ)` for `μⁿ` is
nonzero and meets `π₁* H¹(Ω_σ; ℂ)` only in `0`. Consequently, if a
continuous map `Q: Z → Y` factors through `π₁`, then `Q* H¹(Y; ℂ)` contains
no generalised eigenvector for `μⁿ`. For admissible `n` this applies to the
natural map `Q = Σ_op ∘ q ∘ π₁` into `Ω_ψ` (it sends `(T, T′)` to the
ordered-pair tiling of `q(T)` and its twin `q(T′)`): the defect class is not
pulled back from Barge's space, and Lemma S and Lemma S+ say nothing about
`μ`.

Imports: Theorem W; identity (L0); BD08 Theorem 4 with its proof; Lemma 7;
for the last sentence B15 Thm 4(3), Thm 12, Lemma 13, the density statement
in the proof of Prop. 19, and the identification of the two ranks
(**[Std]**).

*Proof.* By Theorem W the child substitution `Σ` of `σ` on `B` is
primitive, `Z ≅ Ω_Σ`, and `Ω_Σ` is aperiodic (it maps onto the aperiodic
`Ω_σ`). By Theorem NI(1), `μ` is a nonzero eigenvalue of `N`. Apply the
exact sequence of BD08 to `Σⁿ`: the generalised eigenspace of `μⁿ` in
`G_1 ⊗ ℂ`, the eventual range of the transpose of `Nⁿ`, is nonzero; the
induced map acts on `G_0 ⊗ ℂ` through roots of unity (BD08, proof of
Theorem 4), and `μⁿ` is not one; so the eigenspace injects into
`H¹(Ω_Σ; ℂ) = H¹(Z; ℂ)`. On the other side
`π₁* ∘ (Φⁿ)* = (Φⁿ × Φⁿ)* ∘ π₁*`, and `(Φⁿ)*` on `H¹(Ω_σ; ℂ)` has only the
eigenvalues of `Mⁿ` and roots of unity (Lemma 7(3)). `μⁿ` is not an
eigenvalue of `Mⁿ`: otherwise `μ/β`, `μ/α₂` or `μ/α₃` would be a root of
unity, and by Lemma U the weight of `μ` would be a permutation of
`(m + 1, m, m)`, which (W3) excludes. So `π₁* H¹(Ω_σ; ℂ)` has no
generalised eigenvector for `μⁿ`. The map `Q`: `q(T)` and `q(T′)` are
regionally proximal (one fibre of `g_s`, by (Z4)) and share no stack (a
common stack would give tiles of `T`, `T′` that are stably equivalent at
some point, against (Z2)), so `q(T′)` is the twin of `q(T)` (B15
Lemma 13). ∎

*What this is and is not.* It is an obstruction to a method: the transport
of the first-defect eigenvalue of `N_−` into Barge's `X − Y` is impossible
whenever that eigenvalue is not a root of unity, and in the remaining case
(unit `σ`, weights `(m, m, m)`, eigenvalue `±1`) Lemma S+ allows it. It is
**not** shown that Lemma S and the defect intertwiner are jointly
consistent: no model exists, and the route's sentence to that effect is
withdrawn (§12). The mechanism has a concrete precedent outside PIP3: the
substitution `a → aaaab, b → abbbb` has a coincidence at position 0, hence
is an almost everywhere one-to-one extension of the 5-adic solenoid, and by
Theorem FP evaluated by hand it has `5ⁿ + 3ⁿ − 1` tilings fixed by `Φⁿ`: an
almost everywhere injective factor map can add an expanding eigenvalue. At
coincidence rank two `π₁: Z → Ω_σ` is such a map (W2).

## 10. What is still open at coincidence rank two

In their sharpest form, with the cells named by `(d₂, dim H¹)`:

1. **The wall.** `cr(σ) ≠ 2` for `σ ∈ PIP3` with `dim H¹ ≥ 4`. Recorded as
   proved, conditionally on the imports: `dim H¹ = 3` (Theorem H3, every
   determinant); `det M` odd with `dim H¹ = 4` (B15 Thm 22) or with
   `tr M ≢ e₂(M) (mod 2)` (Theorem P). Open:
   - `d₂ = 3` (odd determinant): `tr M ≡ e₂(M)` and `dim H¹ ≥ 5`;
   - `d₂ = 2` and `d₂ = 0`: `dim H¹ ≥ 4`, up to the divisor condition of
     Theorem P+, which is a necessary condition and is not implemented;
   - `d₂ = 1`: `dim H¹ ≥ 4`, where no arithmetic condition of this note
     applies.

   On the (F) class this statement is equivalent to "no strict system", to
   left strong coincidence of all pairs and, conditionally, to pure discrete
   spectrum (Corollary E), so it is the open statement 1 of the
   closure-attempt note, §10, with the even case `dim H¹ = 3` removed.
2. **A strict system at coincidence rank two.** By Theorem W the object to
   exclude is now rigid: one strict component, carried by a primitive
   swap-symmetric strict bigon system `B` for `σ` itself, with
   `ρ(N_−) < β`, first defect degree `r ≢ 1 (mod 3)`, a top-track map that
   is injective almost everywhere and (unless `σ` is unit and `3 | r`) not
   injective, with at least `c ρⁿ` multi-partner fixed points along a
   subsequence. No upper bound on that growth is proved. A comparison of
   growth rates gave no contradiction in the prover's heuristics (unit or
   nonunit; conjectural, not recorded as statements).
3. **Unit `σ` with first-defect weights `(m, m, m)`** (`r = 3m`). Every tool
   of this note is silent there: Theorem NI gives no non-injectivity and
   Obstruction T does not apply.
4. **Beyond `dim H¹ = 3` by the sheet function.** The proof of Theorem H3
   shows that at coincidence rank two the class of the sheet function `z`
   in `H¹(Ω_s; ℤ)` is not an eigenfunction class. Whether its image in
   `H¹(Ω_σ)` always has a nonzero component in the asymptotic-cycle part
   `G_3`, with a computable constraint, is open; this is what an extension
   of Theorem H3 to `l ≥ 1` along the same line would need.
5. **Theorem Fork for nonunit `σ` with `dim H¹ = 3`.** Expected, not proved
   (§8).
6. **Off (F).** Nothing here bounds the coincidence rank off (F), and
   coincidence rank two is not known to give a strict system there; the
   zero-fibre form of C4 (closure-attempt note, §10, item 2) is untouched.

Do not re-run the transport route of §9 as posed.

## 11. What is prior art

| Statement | Status relative to main and the literature |
| --- | --- |
| Theorem FP | The Anderson–Putnam zeta count, restated (their text not read). Standard; no novelty claimed. Not on main before this increment. |
| Lemma K | Elementary; the last step is Kronecker's theorem, already used on main (Proposition Q(b)). |
| Lemma U | The cubic case of Mignotte 1984 (secondary source only). The remark "a monomial is a root of unity only for equal exponents and unit `σ`" was an unproved seed of the round. |
| Theorem TT | Not found on main or in the sources read. The technique (bounded power sums, Kronecker) is that of Proposition Q(b) and of Adamczewski as cited there. |
| Theorem NI(1) | On main: Proposition 1 and §3 of the orientation-spectrum note, the signed lowest-defect intertwiner, manuscript `thm:parikh`. |
| Theorem NI(2)–(4) | Not found on main or in the sources read. It extends the non-injectivity half of Theorem Fork to every determinant and every `dim H¹`, with a weaker conclusion. It also shows that the unique-partner premise of the retired derived-substitution route ([cut-attractor note](c4-cut-attractor-window-2026-11-05.md) §7) fails beyond the class of Theorem Fork, while holding almost everywhere at rank two (W2). |
| Theorem W(1), (2) | Not found on main or in the sources read. |
| Theorem W(3) | The spectral bound, the trichotomy and the shape list are on main (see the remark after the proof); new is the link to coincidence rank two. |
| Theorem W(4) | B15 Lemma 13, first half of the proof. |
| Lemma S+, Theorem P+ | A sharpening of Lemma S of round 1 by the Barge–Bruin–Jones–Sadun `not2` mechanism; the odd-determinant content is B15 Thm 22 and Theorem P. The even-determinant content was not found in the sources read. |
| Lemma 9′ | Barge–Kellendonk–Schmieding 2012, Corollary 3 and Theorem 5. For substitutions with a common prefix and irreducible Pisot matrix their §5.1 quotes a theorem of Andress–Robinson with the same conclusion (not read). |
| Theorem H3 | For odd determinant: B15 Thm 22. For even determinant: not found in the sources read; the mechanism for `d = 1`, even norm, is the theorem `not2`. |
| Corollaries FC3+, N+ | Compositions. On the corpus the new class of FC3+ beyond prior art is 42 specimens, all already covered by `C4StandingCorpus`. |
| Obstruction T | A negative result about a route of this round. |

No novelty relative to the literature is claimed beyond "not found in the
sources read". No new corpus fact follows.

## 12. Work shown

### Assumptions and hypotheses

| Hypothesis | Where it is used | What fails without it |
| --- | --- | --- |
| primitive | Theorem FP (the only hypothesis); everything else | `1/0/22` (refused, pinned) |
| `χ_M` irreducible | Lemma U (a 3-cycle in the Galois group); Theorem TT (`R` injective, `Pk` of rank 3); Theorem NI (`χ_{M^P}` irreducible; nonzero monomials); Theorem W (Lemma 6 and (Z4): partners are fibre-mates; common vertex = cut); Lemma S+ and Theorem P+ (through Lemma S: `G_0 = 0` for `σ`, `χ_{Mⁿ}` minimal for `βⁿ`); Lemma 9′ and Theorem H3 (the eigenvalue group has rank 3) | every reducible control of the table below |
| Pisot | Lemma U and (W3) (signs of the log-moduli); finite fibres and `cr` (BBK, B15); the eigenfunctions | the binary `00001/011`: inside Theorem FP and the counting of Theorem TT, outside the rest |
| `cr(σ) = 2` | Theorem W; Lemma S+; Theorem P+ (hypothesis to be refuted); proof of H3 | no PIP3 substitution with `cr = 2` is known; these statements are vacuous on every computed PIP3 domain |
| `B = swap(B)` | Theorem NI(1)–(3) | automatic at `cr ≤ 2` (Theorem FL; (W1)) |
| `dim H¹ = 3` | Lemma 9′, Theorem H3, FC3+, N+ | Thue–Morse (`l = 1`); C-D1 (`dim H¹ = 3` but the dilation has degree 2) |
| (F) | FC3+ only | 2,760 corpus specimens |
| `det M` | not used in FP, TT, W(1), (2), (4), S+, H3; in NI, (W3) and Lemma U through `abs(det M) ≥ 1` only; in Theorem P+ through `d₂` | — |
| three letters | the constant 9 in Theorem TT; the cubic in Lemma U and (W3); `d₂ ≤ 3` | Theorem FP and the general form of Theorem TT hold on any alphabet |

### Derivation / reduction

```text
FP    =  fixed tilings = interior occurrences + periodic legal seams     [no import]
K, U  =  pigeonhole + Kronecker ;  Galois 3-cycle + Pisot signs          [Kron ; no import]
TT    =  FP for Σ and for σ^P + R injective + Pk onto + Lemma K
NI    =  (L0) + D_r J = −D_r + Pk J = Pk  (on main)  + TT + Lemma U
W     =  BBK Thm 4.2 (two-point fibre) + Lemma 8 (alignment, every determinant)
         + minimality  ⟹  one component ;  Perron–Frobenius on N ;  sieve on main ;
         B15 Lemma 13 (first half)
S+    =  B15 chain of Lemma S + two periodic words (proof of Thm 22) + BD08 Thm 4, 4′
P+    =  S+ + X − Y ≡ X + Y (mod 2) + degrees
9′    =  BKS Cor. 3, Thm 5 + rank 3 (BBK eigenfunctions ; B15 Prop. 19)
H3    =  9′ on Ω_s + B15 twin involution + sheet function + Lemma 10 at p = 2
FC3+  =  FC2 + H3 ;   N+ = Theorem N(1) + H3 + FC2
T     =  BD08 for Σⁿ + Lemma 7(3) + Lemma U + (W3)
```

Every arrow is written out in §§2–9. The finite objects certified by the
regressions are: for Theorem FP, the two counts of `Fix(Φⁿ)` on eleven
substitutions; for the class counts, six integers per corpus specimen
(`det M`, `tr M`, `e₂(M)`, `dim H¹`, the numbers of periodic letters of
`g`, `g_R`) and the exact verdict (F).

### Evidence and replay

```sh
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_fixed_point_count.mojo)
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_geometric_f.mojo)
python3 tools/check_markdown_source.py
```

Both regressions were re-run for this note on 2026-11-16 (exit 0; about
8 seconds and about 90 seconds on one core). Each ends with one
`require_contract`: no ledger claim is registered. They count classes and
periodic points; they certify no coincidence rank, no strong coincidence
and no spectrum.

*Theorem FP (`test_fixed_point_count.mojo`).* The formula
(`fixed_point_formula`: checked powers of the incidence matrix, the
endpoint maps, the legal two-letter words) and the literal count
(`literal_fixed_tilings`: reproduced pointed windows on literal words, no
trace and no endpoint map) agree for `n = 1, …, 6`, as totals, letter by
letter for the interior type, as lists of seams for the vertex type, and at
window radius 1 and 2. Pinned `|Fix(Φⁿ)|`, `n = 1, …, 6`:

| Substitution | `n = 1` | 2 | 3 | 4 | 5 | 6 |
| --- | --- | --- | --- | --- | --- | --- |
| Tribonacci `01/02/0` (`n ≤ 3` by hand) | 0 | 2 | 6 | 10 | 20 | 38 |
| `01/12/021` | 1 | 5 | 10 | 29 | 66 | 158 |
| `1/2/02` | 0 | 0 | 3 | 4 | 5 | 9 |
| `1/02/200` | 0 | 0 | 6 | 8 | 20 | 42 |
| `01/12/210` | 0 | 2 | 15 | 26 | 65 | 161 |
| C-D1 `011/120/2012` | 1 | 11 | 34 | 119 | 391 | 1298 |
| `1/012/101` | 1 | 5 | 13 | 33 | 81 | 197 |
| `10/102/211` (`n = 1` by hand: the seam `0.2`) | 1 | 7 | 19 | 55 | 151 | 415 |
| `1/012/1` (periodic): `2ⁿ − 1` | 1 | 3 | 7 | 15 | 31 | 63 |
| Fibonacci `01/0`: `L_n − 1` | 0 | 2 | 3 | 6 | 10 | 17 |
| Thue–Morse `01/10`: `2ⁿ − 1 + (−1)ⁿ` | 0 | 4 | 6 | 16 | 30 | 64 |

The five corpus rows are asserted PIP with images of length at most 3 and
have pairwise different endpoint types. The row of the periodic control is
derived independently of Theorem FP (the inflation is `t ↦ 2ⁿt + const` on
a circle). Refusals (fail closed, refuse to conclude): non-primitive input,
an erasing image, a letter outside the alphabet, one letter, nine letters,
a power below one, a window radius other than 1 or 2, a word cap ("an
exhausted budget is not a count") and an overflowing trace raise, each
matched on its message.

*Class counts (`test_c4_geometric_f.mojo`, over the 4,554 specimens of
`pip_corpus()`).* `d₂` is read from the parities of `det M`, `e₂(M)`,
`tr M` and equals the rank over `𝔽₂` of `(M mod 2)³` on every specimen; the
eight classes of `χ_M mod 2` are factored by hand in the test. Specimens by
`(d₂, dim H¹)`; `d₂ = 3` exactly for odd determinant:

| `d₂` | `dim H¹ = 3` | 4 | 5 | 7 |
| --- | --- | --- | --- | --- |
| 0 | 336 | 36 | 48 | 12 |
| 1 | 456 | 48 | 144 | 36 |
| 2 | 570 | 72 | 120 | 48 |
| 3 | 1,740 | 396 | 408 | 84 |

- `dim H¹ = 3`, the hypothesis of Theorem H3: 3,102 specimens, 1,740 with
  odd and **1,362 with even determinant**. Of the 1,362: 1,128 fail (F),
  192 have (F) and an endpoint map with fewer than two periodic letters
  (clause (a′) of Theorem FC3, prior art), and 42 have (F) and two periodic
  letters on both sides.
- (F) and `dim H¹ = 3`, the hypotheses of Corollary FC3+: 1,350 = 1,116
  odd + 234 even.
- `dim H¹ < 3 + |d₂ − 1|` (item 1 of Theorem P+ fails): 3,042 = 2,136 odd +
  906 even; for even determinant these lie in `dim H¹ = 3`, and the bound is
  silent on the 456 specimens with `d₂ = 1` and `dim H¹ = 3`.
- The hypotheses of "`cr ≠ 2`" without the divisor condition (odd
  determinant: `dim H¹ ≤ 4` or `tr M ≢ e₂(M)`; even determinant:
  `dim H¹ = 3`): 3,714 = 2,352 + 1,362 specimens; 840 = 276 odd + 564 even
  do not meet them.
- The 510 specimens with (F) and two periodic letters on both sides, by
  `(d₂, dim H¹ = 3/4/5/7)`: `d₂ = 0`: 30/0/0/0; `d₂ = 1`: 0/0/48/24;
  `d₂ = 2`: 12/0/60/0; `d₂ = 3`: 24/60/204/48. Of the 174 with even
  determinant (all `det M = 2`), **42 have `dim H¹ = 3`** (30 with
  `χ_M ≡ t³` and 12 with `χ_M ≡ t(t² + t + 1) mod 2`) and 132 do not (72
  with `d₂ = 1`; 60 with `d₂ = 2` and `dim H¹ = 5`). With the 156 odd ones
  of round 1, 198 of the 510 meet the hypotheses of Theorem FC3 or
  Corollary FC3+, and 312 = 180 + 132 do not.
- Fixtures by hand: `01/121/012` (`χ_M ≡ t³`, `d₂ = 0`, `dim H¹ = 3`, (F));
  `01/220/100` (`t(t² + t + 1)`, `d₂ = 2`, `dim H¹ = 3`, (F)); `1/212/021`
  (`t(t + 1)²`, `d₂ = 2`, `dim H¹ = 5`, (F): meets no hypothesis);
  `1/22/021` and `1/22/012` (one matrix, `t²(t + 1)`, `d₂ = 1`:
  `dim H¹ = 5` with (F), meeting no hypothesis, and `dim H¹ = 3` without
  (F)); `1/2/021` (odd, `tr M ≡ e₂(M)`, `dim H¹ = 5`: meets no hypothesis).

These are counts of classes under conditional theorems. On the corpus the
conclusions of Corollary FC3+ are known by other means
(`C4StandingCorpus`), and no specimen is certified to have, or not to have,
coincidence rank two.

*Not implemented, hence not pinned.* The divisor condition of Theorem P+
and the refinement of Remark (3) after Theorem P (Lemma S at the admissible
`n < 6`).

*Exploratory scratch observations (not replayable from the repository).*

- The prover and both verifiers computed, with their own scratch code, the
  figures "`cr ≠ 2` on 2,364 odd and 1,386 even corpus specimens (930 by
  Theorem P+, 456 more by Theorem H3)". These include the two conditions
  that are not implemented. The replayable figures are 2,352 odd and
  1,362 = 906 + 456 even.
- Spectra on the controls of the next table (child matrices, swap
  decompositions, defect actions, fixed pairs over fixed tops), reproduced
  independently by both verifiers.
- An explicit instance of Lemma S+ outside PIP3: Thue–Morse, proper version
  of `σ²` at the seam `0.0`, twin = letter exchange (B15 Example 16): 12
  ordered pair letters, `χ_{X+Y} = t⁴(t − 4)(t − 1)`,
  `χ_{X−Y} = t⁵(t − 1)`, `ER` two fixed edges, and `H¹` with characteristic
  polynomial `(t − 4)(t − 1)`. Reproduced by the logic verifier, who also
  checked items 1–3 on fourteen further coincidence-rank-two examples
  outside PIP3 (eight bijective two-letter substitutions, BBK Example 5.3,
  five lifts of even-norm quadratic Pisot substitutions).
- The verifiers' searches for counterexamples found none: Theorem FP
  against the collared Anderson–Putnam count on 400 seeded primitive
  substitutions and on 15 named ones; Lemma U and the shape list of (W3) on
  1,524 irreducible Pisot cubics; (L0), `D_r J = −D_r` and the divisibility
  of Theorem NI(1) on the 432 primitive components of the 276 strict
  carriers among the primitive ternary substitutions with images of length
  at most 3.
- The trigon system of the hub control C-D1 (58 trigons, 40 non-degenerate,
  largest root 2.769 against `β^{1/2} = 1.817`): a growth comparison that
  leaves room and decides nothing. Reproduced by one verifier.

### Negative controls

Where each argument stops on each control that has a strict system.
"Pinned" refers to a Mojo or Lean statement on disk; everything else in the
third column is scratch (exact arithmetic, reproduced by both verifiers
unless noted).

| Control | Pinned data | Where the arguments stop |
| --- | --- | --- |
| Thue–Morse `01/10` | strict `{(01,10), (10,01)}` (Lean `Psc.StrictSystem.tm_strictSystem`); `Fix(Φⁿ)` as above | Not PIP3 (`det M = 0`, reducible, degree one). Theorem FP applies. The general form of Theorem TT applies and its conclusion holds: `χ_N = t(t − 2)`, cofactor neutral, the top track injective on fixed points for `n ≤ 3`. Lemma U and Theorem NI stop at `det M = 0` (the monomial is zero). The conclusions of Theorem W hold on it (one swap-symmetric primitive component, the graph of the letter exchange; `cr = 2` by B15 Example 16), not its hypotheses. Lemma S+ holds on the explicit instance above. Theorem H3 stops at `l = 1`: not every class is an eigenfunction class. |
| `01/2/120` | 20-state strict system (`test_c4_quotient_spectrum.mojo`) | Singular, dilation 2. Lemma U and NI stop at `det M = 0` (the defect action is nilpotent). The general form of TT applies: `χ_{N_−}` has the factor `t³ + t² − 2t − 4` (root 1.659), and the top track is not injective on fixed points (`n = 3`: 6 fixed pairs over 4 tops). So `N_−` can carry an expanding eigenvalue that is not a defect monomial. Its coincidence rank was not determined (the route's reading "4" is unverified), so Theorem W is not tested. |
| `012/120/201` | strict system (`test_c4_cut_attractor.mojo`) | `χ = t²(t − 3)`; the system is flat with three states. `χ_N = χ_M`, cofactor neutral, the top track injective on fixed points (0, 6, 30 on both sides): the conclusion of TT holds. Everything else stops at degree one and `det M = 0`. |
| `1/012/1` | 4-state strict system (`test_c4_quotient_spectrum.mojo`); `Fix(Φⁿ) = 2ⁿ − 1` | Periodic and singular. Theorem FP applies (pinned). Outside every import. |
| `1/012/101` | 3 states under `σ²`, 6 under `σ` (`test_c4_reducible_pisot_controls.mojo`); `Fix(Φⁿ)` as above | Reducible, unit. Under `σ` the 6-state sink is swap-symmetric of period 2 and `J` exchanges the two cyclic classes: `χ_{N_+} = (t − 1)(t² − 2t − 1)`, `χ_{N_−} = (t + 1)(t² + 2t − 1)`, so `ρ(N_−) = β`, the Perron-extremal case that (W3) excludes under its hypotheses. On a class under `σ²`: `χ_N = χ_{M²}`, the cofactor is trivial, and the top track is still not injective (6, 34, 198 fixed pairs over 5, 33, 197 fixed tops; the tops are the pinned `Fix(Φ²)`, `Fix(Φ⁴)`, `Fix(Φ⁶)`): **the converse of Theorem TT is false**. NI stops: the defect eigenvalues `1, β², β′²` are a root of unity or eigenvalues of `M²` (reducible: Lemma U is not available). W stops at alignment (round 1: return lengths of index 2). |
| `10/102/211`, `01/201/112` | 4-state flat system (`test_c4_cut_attractor.mojo`); Lean `Psc.StrictSystem.carrier_strictSystem`; `Fix(Φⁿ)` as above | Reducible, `det M = −2`. `χ_N = (t − 1)(t + 2)(t² − 2t − 2)`: the defect eigenvalue `β β′ = −2` is an integer, not a root of unity and not an eigenvalue of `M`. The general form of TT applies in full and the top track is not injective (`n = 2`: 12 fixed pairs over the 7 pinned fixed tops). **So the conclusion of Theorem NI is realised by an actual strict system: non-injectivity alone is not a contradiction.** Lemma U stops (reducible). W stops at alignment (index 3) and at `cr`; P+ and H3 at irreducibility. |
| C-D1 `011/120/2012` | 18-state system (`test_c4_reducible_pisot_controls.mojo`); `dim H¹ = 3` (`test_c4_geometric_f.mojo`); `Fix(Φⁿ)` as above | Reducible, unit. `χ_N = (t − 1)(t + 1)² t^{10} (t² − 3t − 1)(t³ − t − 1)`: the defect action `(t + 1)(t² − 3t − 1)` is a root of unity or in the spectrum of `M`, so NI's eigenvalue step gives nothing; the plastic factor makes the cofactor non-neutral, and the top track is not injective (`n = 2`: 16 fixed pairs over 9 tops; 11 fixed tilings, pinned). W stops at alignment (index 3). H3: `dim H¹ = 3` and unit hold literally; the proof stops at irreducibility: the eigenvalue group has rank 2 (the dilation is quadratic; BBK Thm 5.1), so not every class is an eigenfunction class. |
| C-D2 `010/1222/2012` | 21 and 23 states (same test) | Reducible, unit. `χ_N/χ_M = (t − 1)(t + 1)³ t^{12} (t² + 1)` is neutral, so TT gives nothing, and the top track is not injective anyway (`n = 2`: 16 fixed pairs over 11 tops): the converse of TT fails again. |
| `1/0/22` | strict system (`test_c4_reducible_pisot_controls.mojo`) | Not primitive: `psc.fixed_point_count` refuses it (pinned), and no statement applies. |

Controls without a strict system:

- `a → aaaab, b → abbbb` (matrix `[[4,1],[1,4]]`, spectrum `{5, 3}`,
  coincidence at position 0): `5ⁿ + 3ⁿ − 1` fixed tilings by Theorem FP
  evaluated by hand (`#Fix(gⁿ) = #Fix(g_Rⁿ) = 1`, one fixed legal seam
  `ba`). It realises the phenomenon behind Obstruction T (§9).
- The productive PIP3 controls `01/12/021`, `1/02/002`, `01/20/200` have no
  strict system (`C4StandingCorpus`), so Theorems NI and W are vacuous on
  them; `01/12/021` (`det 1`, `tr 3`, `e₂ 2`, `dim H¹ 4`, pinned) meets the
  hypotheses of "`cr ≠ 2`" by Theorem P, and its fixed-point counts are
  pinned.
- The non-Pisot binary `00001/011` is inside Theorem FP and the counting
  part of Theorem TT and outside everything else.

No PIP3 substitution with coincidence rank two or with a strict system is
known. Theorems W, P+ and H3 are therefore vacuous on every computed PIP3
domain; they were tested only through their reducible analogues and through
the imported structure (Lemma S+).

*Stronger variants and wordings that failed, kept on record.*

- "Lemma S and the defect intertwiner are jointly consistent in every case;
  they cannot be combined into a contradiction" (the route's Proposition T):
  not proved, and not provable without a model. Replaced by Obstruction T.
- "Theorem H3 at `|det M| = 1` is B15 Cor. 25": wrong locator; it is B15
  Thm 22 for every odd determinant.
- "Lemma 9 without unimodularity is new": it is BKS 2012.
- "Lean covers the defect intertwiner only for `r = 2, 3, 4`": main has
  `Degree5Transport` and `Degree5Sieve`.
- "The 2-to-1 covering is B15 Theorem 15": in the arXiv text the covering is
  Theorem 17, and item 15 is the Lemma `Ω_{Ψ_p} ≅ Ω_Ψ/∼_rpd`.
- "Theorem Fork holds for nonunit `σ` with `dim H¹ = 3`": expected, not
  proved.
- The condition `|det M|^{m+1} < β²` in (W3): redundant.
- A remark of the route on `tr(J Nⁿ)` (fixed against swapped pairs) was
  imprecise as stated (it counts pairs `(T, ΦⁿT) ∈ Z` with `Φ^{2n}T = T`)
  and is not recorded.
- The route's growth paragraph ("all fibre-mates share supertile boundaries
  under (F)"; a lower bound from a "bubble matrix") is heuristic and is not
  recorded as a statement.
- "930 even specimens by Theorem P+": includes the unimplemented divisor
  condition; the replayable figure for the dimension bound is 906.

### Non-claims / remaining gaps

- **Universal C4.** Open. Nothing here excludes a strict system at
  coincidence rank two in general.
- **`cr ≠ 2` for `dim H¹ ≥ 4`.** Open in the cells of §10, item 1.
- **"At coincidence rank two `σ` is unit and `3 | r`"** and **"no strict
  system for nonunit `σ` at coincidence rank two"**: not proved.
- **Consistency.** It is not claimed that a strict system at coincidence
  rank two is consistent with all the necessary conditions of this note;
  no model is known.
- **Theorem Fork for nonunit `σ`.** Expected, not proved.
- **General Pisot substitutions.** The remark at the end of §8 is not a
  statement of this note.
- **Class counts.** The regression counts hypotheses. It decides no
  coincidence rank and no spectrum; the divisor condition of Theorem P+ is
  not implemented.
- **Status of the proofs.** None is machine-checked. Theorems TT, NI and
  (W3) rest on identity (L0), which is a written proof on main beyond
  `r = 5`. Theorem W rests on Lemma 8 of the (F)-class note and on BBK
  Thm 4.2. Lemma S+ and Theorems P+ and H3 rest on B15 as printed: on
  Thm 4, whose proofs were not followed into the papers it cites; on the
  proper version, whose rewriting references were not read; on the
  assertion, in the proof of Thm 22, that the ordered-pair substitution has
  exactly two periodic words; and on the identification of the two
  coincidence ranks. Theorem H3 uses the **[Std]** facts of §1, none of
  which was checked against a source on disk; the explicit sheet function
  of §8 was added while writing and was not seen by the verifiers.
  Anderson–Putnam 1998 and Mignotte 1984 were not read.
- **No certification.** C4, #138, #139, #84, G1 and PSC are unchanged, and
  no ledger claim is registered.
