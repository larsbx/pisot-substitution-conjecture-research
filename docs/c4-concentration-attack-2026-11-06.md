# Concentration: a four-route attack, and where each route stops — 2026-11-06

**Status:** Open Problem Concentration (manuscript `prob:concentration`) is
**not proved**. It says that no strict component of a PIP substitution on
three letters has `K₂ ≡ 0`.

This note records what a four-route attack established, by status:
- **Theorem A** (degree four) and the **reduction lemma** (§3) are written
  proofs, each checked step by step by the author after an agent produced
  it. Human review is pending. Their formalized parts are listed in §8.
- **Corollary T** (Tribonacci) is conditional on a computer-assisted
  published theorem.
- §4 lists agent proofs that the author has not checked, labelled as such.
- §5 gives two pinned negative controls, together with scratch evidence.

Nothing here changes the ledger nodes C4, BH (#139), A1′ (#138), G1 or PSC.
Notation follows the manuscript `manuscripts/PSC_balanced_pair_state_2026-09-13.tex`
and the [general-structure note](c4-general-structure-2026-11-06.md).

## 1. Stop/go

**Prior art in the repository:**
- `thm:sieve`, `prop:cocycle`, `thm:defect-intertwiner`, `thm:deg23`;
- the [degree-four note](c4-degree4-free-lie.md), whose §8 is the three-state
  case of Theorem A(iii);
- the [W₃ note](c4-w3-low-growth-and-interface-correction.md);
- [P1-A](p1a-degree3-partial-theorem.md), the corpus degree-3 exclusion.

**Literature, read in full or as PDF by an agent:**
- Lejeune–Rigo–Rosenfeld, Adv. Appl. Math. 112 (2020), Theorem 29: "Two
  factors of the Tribonacci word are 2-binomially equivalent if and only if
  they are equal". The proof is computer-assisted and the fast
  implementation uses floating point.
- Rigo–Stipulanti–Whiteland, arXiv:2201.04603: Theorems 2.3, 2.8, 2.11 and
  3.5. The bounded class there consists of Parikh-collinear morphisms, which
  have rank one and never meet PIP.
- Vivion, arXiv:2509.11172: the conjecture `b₂ = p` for Arnoux–Rauzy
  words; Tribonacci is "the only known example".
- Lejeune–Rigo–Rosenfeld, arXiv:2001.11732, Theorem 11: `Σ*/∼₂` embeds in
  the free nil-2 group, so `K₂ = 0` means equality in the free class-two
  nilpotent group.
- Mateescu–Salomaa–Salomaa–Yu 2001: Parikh-matrix equality is a different
  relation from `∼₂`.

No published theorem gives Concentration for all PIP. Decision: **proceed**
with the narrowed results below.

## 2. Theorem A: first defect degree four

**Theorem A.** Let `σ` be PIP on `{0,1,2}`, with roots `β, α, γ` and
`d = det M`. Let `C` be a strict component with `r(C) = 4`, and
`Φ = M^{⊗4}|_{Lie₄}`. Then:
- (i) `|d| = 1`;
- (ii) `im Q₄ ⊆ E_C := ker χ_{dM}(Φ)`, the `(2,1,1)` sector. In particular
  the `(2,2,0)` sector is excluded for **every** PIP;
- (iii) `S = d·DND` for a diagonal `D` with entries `±1`, so the cocycle is a
  gauge if `d = 1` and an anti-gauge if `d = −1`;
- (iv) `Q₄D = L∘P` for an injective `L : ℚ³ → Lie₄` with `LM = dΦL`. Hence
  every state has `K₄ ≠ 0` (exact defect degree four), and states with equal
  Parikh vectors have equal oriented `K₄`.

*Proof.* `im Q₄ ≅ ℚ^C / ker Q₄` as `S`-modules, so `χ_{Φ|im Q₄}` lies in
`ℤ[x]` and divides `χ_S`. Its roots therefore form a Galois-stable subset of
`spec S`, of modulus at most `ρ(S) ≤ β` (`prop:cocycle`). By the Witt formula,
the weights of `Lie₄(ℚ³)` are the permutations of `(3,1,0)`, `(2,2,0)` and
`(2,1,1)`.
- **`(3,1,0)`.** The orbit contains `β³β_j`, whose modulus exceeds `β`.
- **`(2,2,0)`.** The orbit contains `β²α²`, whose modulus exceeds `β`
  unless `α, γ` are complex and `|d| = 1`; then it equals `β`. In that case
  apply Wielandt's theorem with `λ = β²α²` (`N` irreducible, `ρ(N) = β` by
  `thm:parikh`, `|S| ≤ N`). It gives `S = e^{iφ}D′N D′^{−1}` with
  `e^{iφ} = βα²`. Since `S` is real with `|S| = N`, every edge has
  `e^{iφ}d′_i/d′_j = ±1`. Along a directed cycle of length `ℓ` this gives
  `(βα²)^{2ℓ} = 1`. Now `βα² = dα/γ`, so `α^{2ℓ} = γ^{2ℓ}`. Then
  `x = α^{2ℓ} ∈ ℚ(α)` has at most two distinct conjugates, so `x ∈ ℚ` and
  `β^{2ℓ} = α^{2ℓ}`, contradicting `|β| > 1 > |α|`.
- **`(2,1,1)`.** This leaves the eigenvalues `d{β, α, γ}`. They have modulus
  at most `β` only if `|d| = 1`, which is (i). `Φ` is semisimple, so (ii)
  follows.

For (iii): `im Q₄ ≠ 0` has characteristic polynomial a power of the
irreducible `χ_{dM}`, so `dβ ∈ spec S`. Wielandt with `λ = dβ` gives
`S = d·DND^{−1}`, and real integrality with `|S| = N` forces `d_i/d_j = ±1`
on edges. Strong connectivity normalizes `D` to `±1` entries.

For (iv): `Q₄′ = Q₄D` satisfies `Q₄′N = dΦQ₄′`. On `E_C`, `dΦ` is semisimple
with minimal polynomial `χ_M`. Since `β` is a simple root of `χ_N`, we get
`χ_N = χ_M·g` with `gcd(χ_M, g) = 1`; split `ℚ^C = ker χ_M(N) ⊕ ker g(N)`.
- `g(dΦ)` is invertible on `E_C` and `g(M)` is invertible, so `Q₄′` and `P`
  both vanish on `ker g(N)`.
- `P` is onto by `thm:parikh`, hence an isomorphism on the
  three-dimensional `ker χ_M(N)`.
- Put `L = Q₄′ ∘ (P|)^{−1}`. Then `ker L` is a rational `M`-invariant
  subspace and `L ≠ 0`, so `L` is injective. ∎

**What remains at degree four: configuration (R).**
- `σ` is unimodular with `det M = 1`, and the cocycle is gauge-trivial.
- There are two morphisms `U ≠ V` with `σU = Uτ`, `σV = Vτ`, `π∘U = π∘V`,
  and `K₁ = K₂ = K₃ = 0` on every state.
- `K₄(U(T), V(T)) = L(π(T))`.

The `det M = −1` case reduces to (R) via `σ²`. An explicit abstract object
satisfies every linear, spectral and phase constraint used here. It has
`C = {1,2,3}`, `N = M`, `P = I` and `Q₄ = L₀`, where `L₀` is the
`GL`-equivariant copy of `det ⊗ V` in `Lie₄`. So closing (R) needs
word-level realizability.

## 3. The reduction lemma and Tribonacci

**Lemma.** Let `σ` be primitive with Perron root `> 1`, and let `C` be a
strict component with `K₂ ≡ 0`. Then there are `p ≥ 1` and letters `a ≠ b`
whose `σ^p`-fixed points `x_a`, `x_b` satisfy `x_a[0,c) ∼₂ x_b[0,c)` (equal
`N₁` and `N₂`) at a set of cut points `c` with gaps at most `max_{T∈C} |T|`.

*Proof.* Let `f(T)` be the first block of `red(σ(T))`; then `fⁿ(T)` is the
first block of `red(σⁿ(T))`. `C` is finite, so some `T₀ = (u₀, v₀)` has
`f^p(T₀) = T₀`. Its first letters `a, b` differ, since otherwise
irreducibility forces a coincidence. `u₀` is a prefix of `σ^p(u₀)`, so the
`σ^{pn}(u₀)` increase to the fixed point `x_a`, and likewise `v₀` to `x_b`.

By closure, every `σ^{pn}(T₀)` splits into blocks of `C`. `K₂` is additive
over balanced blocks, because the cross terms `π(x)⊗π(y)` agree. So the
prefixes agree in `N₁` and `N₂` at every cut, and `lem:return-gap` bounds the
gaps. ∎

**Corollary.** If distinct factors of `L(σ)` of equal length are never
2-binomially equivalent (`b₂ = p`), then `σ` has no strict component with
`K₂ ≡ 0`. Reachability, caps and legality of the states play no role. The
hypothesis is invariant under relabelling, reversal, and passage to any `σ′`
with `L(σ′) = L(σ)`.

**Corollary T (conditional).** Concentration holds for the Tribonacci
substitution `01/02/0` and its relabellings and reversals, given
Lejeune–Rigo–Rosenfeld Theorem 29. That theorem is computer-assisted, so this
is an imported dependency until replayed exactly.

**Not a general route.** `011/2/120` (PIP, `det 1`) has the distinct
2-binomially equivalent factors `0112201` and `1200112` of `σ⁶(0)`; this is
pinned (§5). An agent scan over the first ~6,000 letters found such pairs of
length ≤ 24 in 2,970 of the 4,554 corpus specimens. That is scratch evidence,
but each witness is an actual factor pair.

**Galois lemma.** The three functionals `ℓ_i ∧ ℓ_j` on `Λ²ℚ³` are permuted,
up to sign, by the Galois group, and they form a basis. For a rational
`K₂(T)`, one of them vanishes if and only if all do. So `K₂(T) = 0` if and
only if the loop of `(u, v)`, projected along the Perron direction onto the
contracting plane, has zero signed area. Equivalently, the mean Perron-weighted
displacement between the two paths vanishes. The contracting-plane area and
the mixed areas therefore cannot be played against each other.

## 4. Agent results not checked by the author (scratch)

- **Moment vanishing.** If `r(C) ≥ 3`, then `∫₀^{L_T} t^k D_T(t) dt = 0` for
  `k ≤ r − 2`, where `D_T` is the displacement between the two paths, via the
  path signature.
- **Heisenberg reformulation.** For unit PIP, Concentration is equivalent to
  a non-vanishing vertical cocycle `ζ`. It would follow from "lifted hub
  disjointness": `int π_s(R^H_h ∩ R^H_x) = ∅`. That statement is weaker than
  subtile disjointness, but no method for it is known. Attempting it by
  self-similarity is circular.
- **The child-structure system at degree three.** An abstract system for
  `M0` (§5) satisfies `thm:parikh`, `prop:cocycle`, `thm:defect-intertwiner`,
  `thm:deg23`(iii), `prop:midarea`, and the endpoint-type and integrality
  constraints. It fails only literal factorization and depth-2 strong
  coincidence. The verifier is in scratch.
- **Windows.** No strict system with `K₂ ≡ 0` exists with all states of
  length ≤ 13 among the 15,192 primitive `σ` with images of length ≤ 3 and
  non-synchronizing endpoints. None exists with all states ≤ 11 among the
  592,134 such `σ` with images ≤ 4. The shortest irreducible pairs with
  `K₂ = 0` have length 7 (six classes); those with `K₁ = K₂ = K₃ = 0` have
  length 12.

## 5. Negative controls (pinned: `kernel/tests/test_c4_concentration_controls.mojo`)

- **No single-pair argument closes degree three.**
  `T13 = (1222200110120, 2201121220001)` is irreducible with `K₂ = 0` and
  `K₃ ≠ 0`. For `M0 = [[5,21,1],[6,26,1],[6,24,1]]` (primitive,
  `χ = x³ − 32x² + 5x + 2` irreducible Pisot, `det −2`) one has
  `M0^{⊗3}K₃ = −2·K₃`. So `K₃` lies in the det-sector.

  Up to length 9, every `Θ(K₃)` of a `K₂ = 0` pair has a rational eigenvalue.
  From length 10 on, irreducible ones occur (scratch enumeration).
- **`b₂ = p` fails for a PIP.** The factors `0112201 ∼₂ 1200112` of
  `σ⁶(0)` for `011/2/120`.

## 6. Where every route stops

All four routes stop at the same place: the literal factorization
`σ(u) = R₁⋯R_m`, equivalently strong-coincidence-type information.
- The linear, spectral, mid-area, endpoint-type and integrality constraints
  are jointly satisfiable at degree three (§4).
- At degree four they are jointly satisfiable in configuration (R).
- Geometrically they reduce to a lifted subtile disjointness for which no
  method exists.

This agrees with the manuscript's conclusion that no invariant coarser than
the factorization closes the problem.

## 7. Non-claims

The following are not claimed:
- Concentration, Wedge productivity, NS for PIP, C4, BH, A1′, G1, PSC;
- Concentration for Arnoux–Rauzy (that needs the Lejeune–Rigo–Rosenfeld
  conjecture) and Corollary T as a mechanically certified result;
- any §4 statement as repository-proved;
- the conjectured "combinatorial Concentration": no primitive `σ` on three
  letters has a strict system with `K₂ ≡ 0`. It is supported only by the §4
  windows.

## 8. Lean formalization (`proof/PscVerif`)

The `PscVerif` library (51 modules, those below among them) passes the proof-bank
axiom audit: 3526 declarations, 2660 theorems, using only `propext`,
`Classical.choice` and `Quot.sound`; no `sorry`, no local axioms, no
`native_decide` (audit of 2026-11-09; it was 45 modules, 2368 declarations,
1875 theorems before `StrictSystem`, `Degree3Catalogue` and `ReductioControls`
were integrated).
- *Full* means the formal statement is the stated result.
- *Given X* means the formal statement assumes X, and X is named.

| Result | Lean | Coverage |
|---|---|---|
| Block additivity of `K₂`: `n2 (x++y) = n2 x + n2 y + \|x\|_a\|y\|_b`, so concatenations of `∼₂` blocks are `∼₂` at every cut | `Psc.Binomial.n2_append`, `Equiv2.append`, `equiv2_join`, `equiv2_at_cuts` | full |
| Reduction lemma, finite form | `Psc.Binomial.ChildSystem.reduction_lemma` | full |
| Reduction lemma, limit form: two `σᵖ`-invariant limit words with different first letters, `∼₂` on a syndetic set of prefix lengths, gaps at most the maximal state length | `Psc.FixedPointLimit.reduction_limit` (with `limit_spec`, `limit_fixed`, `limit_zero`, `grow_of_nonerasing`, `fixed_points_equiv2_syndetic`) | full as an implication; for primitive `σ` via the power child system `ChildSystem.pow` (`Psc.PrimitiveExpansion.reduction_limit_of_primitive`). It is a reductio premise: the hypothesis set is empty on two letters (`binary_reduction_premise_empty`, from `binary_no_equiv2`, an elementary standard fact, cf. Rigo–Salimov 2015) and conjecturally on three (combinatorial Concentration). `thueMorse_control` meets every hypothesis except `K₂ ≡ 0` |
| Irreducible noncoincident balanced pairs have distinct first letters | `Psc.Binomial.heads_ne` | full |
| Galois lemma: an eigen-row of `Λ²M` vanishing on a nonzero rational vector is zero | `Psc.Cyclicity.eigenrow_wedge2` (via `cyclic_of_irreducible`, `irreducible_wedge2`, `ConcentrationAlgebra.eigenrow_eq_zero`) | given `χ_M` irreducible; the coordinates are those of `kw` below, so it applies to actual `K₂` vectors |
| Incidence and count layer: `inc s`, `count_subst`, `count_iterate_subst = (inc s)^k`, `n2_subst`, `n3`, `n3_append`; bridges to `Psc.N₂`/`N₃`/`K₂`/`K₃` and `ConcentrationControls.k3` | `Psc.Incidence.*`, `Psc.CountBridge.*` | full |
| Degree-2 intertwiner on words: `K₂(σu,σv) = (M⊗M)K₂(u,v)`, antisymmetry, wedge coordinates `kw(σu,σv) = Λ²M·kw(u,v)`, block additivity over children, swap | `Psc.Intertwiner2.k2_subst`, `k2_antisymm`, `kw_subst`, `kw_children`, `k2_swap`, `kw_swap` | full over raw ordered (unsigned) children; the signed normalised form is the signed-intertwiner row below; `prop:midarea`'s area/`H` identity is not formalized |
| Degree-3 intertwiner on words (`thm:defect-intertwiner` at `r = 3`, Lemma 0 of the [general-structure note](c4-general-structure-2026-11-06.md)): for `∼₂` pairs, `K₃` is additive over concatenation and `K₃(σu,σv) = M^{⊗3}K₃(u,v)` | `Psc.Incidence.n3_append`, `Psc.Incidence.n3_subst`, `Psc.Intertwiner3.k3_additive`, `k3_join`, `k3_subst`, `k3_children` | full over raw ordered pairs, block lists and child systems; `K₃ ∈ Lie₃` is the `Lie₃` row below; degree 4 is the `Defect4` row; degrees `r ≥ 5` are not formalized |
| `thm:parikh` in matrix form for a child system: `P_C N_C = M P_C`, `λ N_C = βλ` with `λ = ℓᵀP_C > 0` | `Psc.ParikhIntertwiner.pc_nc`, `lc_nc`, `lc_pos` (with `parikh_subst`, `parikh_children_top/bot`, `Lfun_subst`) | full for the raw ordered child system: `Nc` counts raw children, so for a swap-closed system it is the oriented double cover, not the manuscript's representative `N_C = A + B` (see the next rows). `pc_nc` is unconditional; `lc_nc` assumes `ℓ ᵥ* M = βℓ`; `lc_pos` assumes `ℓ > 0` and nonempty top tracks (automatic for balanced noncoincident states: `Psc.Binomial.Equiv1.tracks_ne_nil`). `perron_root_childSystem` gives `ρ(Nc) = β`. The rank and divisibility clauses are the next row |
| `thm:parikh`, rank and divisibility clauses, on normalised representatives (the manuscript's `N_C = A + B`): `P_R N_C = M P_R`, `rank P_R = d`, `\|R\| ≥ d`, `χ_M ∣ χ_{N_C}` over `ℚ` and `ℤ`, `N_C ∼ M` via `P_R` when `\|R\| = d` | `Psc.ParikhRank.prep_nrep`, `prep_surjective`, `card_rep_ge`, `charpoly_dvd_rep`, `charpoly_dvd_rep_int`, `similar_rep_of_equiv`, `exists_similar_rep_of_card_eq`, proved once for an abstract intertwiner (`surjective_of_intertwine`, `card_ge_of_intertwine`, `charpoly_dvd_of_intertwine`, `similar_of_intertwine`; Gauss `charpoly_dvd_of_map_rat`, with `charpoly_dvd_int_of_rat` its form for natural matrices) | given `χ_M` irreducible, `C` nonempty and balanced states; nonempty top tracks follow from balance under a normalisation (`Psc.SignedCocycle.Normalisation.top_ne_nil`). The double-cover versions (`pc_surjective`, `card_ge`, `charpoly_dvd`, `charpoly_dvd_int`) also hold, given nonempty top tracks; the double-cover `m = d` clause is vacuous under a normalisation (`card_state_eq_two_mul`: `\|C\| = 2\|R\|`; `no_equiv_fin3`). The cofactor `χ_{N_C}/χ_M` on `ker P_C` is the `KernelCofactor` row |
| Abstract Perron comparison: every eigenvalue of a matrix dominated by `N` has modulus `≤ β`, given `λN = βλ` or only `λN ≤ βλ` with `λ > 0` (row action; the remark after `thm:parikh` writes it transposed) | `Psc.ParikhIntertwiner.spectral_bound`, `spectral_bound_of_subinvariant`, `spectral_bound_childSystem` | full as matrix lemmas; subinvariance for an escaping or leaking SCC is not derived |
| `prop:cocycle` on normalised representatives: `A`, `B`, `N_C = A + B`, `S = A − B`; every `S`-eigenvector lifts antisymmetrically to an `Nc`-eigenvector, hence `ρ(S) ≤ β` (also directly from `λN_C = βλ` and `\|S\| ≤ N_C`); Thue–Morse non-vacuity with `S ≠ N_C` | `Psc.SignedCocycle.Normalisation.Ssign`, `Nrep`, `lift_eigen`, `lift_ne_zero`, `cocycle_spectral_bound`, `cocycle_spectral_bound_rep`, `rep_eigen`, `ssign_abs_le`, `top_ne_nil`; `thueMorseNorm`, `thueMorse_cocycle_bound`, `thueMorse_ssign_ne_nrep` | given swap closure and `children_swap` (the latter derived for zero-return children by `Psc.Reduction.redNormalisation`) and `ℓ > 0`; the double-cover route `cocycle_spectral_bound` also assumes nonempty top tracks, the representative route `cocycle_spectral_bound_rep` assumes balance instead, which gives them (`top_ne_nil`); a normalisation forces `C` coincidence-free (`Normalisation.noncoincident`). The gauge criterion, the strict and primitive equality clauses, and independence of the choice of representatives are the `CocycleSpectrum` row; the Thue–Morse control has `S = 0`, and the controls with `S ≠ 0` are in the signed-intertwiner row |
| Zero-return reduction (`def:balanced`, one step of `def:bpa`): `red u v` cuts at every zero return; for `∼₁` pairs its blocks are nonempty, balanced and irreducible, and they are the unique such factorization; `red v u` is the swap of `red u v`; the child system with `children T = red(σT₁, σT₂)` and its normalisations | `Psc.Reduction.red`, `red_top`, `red_bot`, `red_isBlock`, `red_unique`, `red_eq_iff`, `red_swap`, `equiv1_subst`, `redSystem`, `redSystem_isBlock`, `redSystem_states_isBlock`, `redSystem_children_swap`, `redNormalisation`; `tmRedSystem_eq` | full for one step, over any alphabet. `lem:descendants`, reachability from the seeds and swap closure are the `Descendants` row; G1 and the inherited/newborn split are not formalized |
| `thm:defect-intertwiner` at `r = 2, 3` on normalised representatives: a child equal to `i.swap` contributes `−K_r(i)`, so `Q₂S = (M⊗M)Q₂`, `Q₂S = Λ²M·Q₂` (wedge coordinates over `Fin 3`) and `Q₃S = M^{⊗3}Q₃` | `Psc.SignedIntertwiner.sum_children_signed`, `k2_rep`, `q2full_mul_ssign`, `wedge2_mulVec_kw_rep`, `q2_mul_ssign`, `k3_rep`, `q3_mul_ssign`, `q3_col_mem_lie3` | given a normalisation and the lower defects vanishing on every state (`∼₁` for `r = 2`, `∼₂` for `r = 3`). Controls: `exA` (zero-return, `S = (2)`, `kw ≠ 0`), `wT` (built by `redSystem`, `S = (1)`, `K₃ ≠ 0`), `exB` (`S = (−1)`; algebra-only: its state is reducible and its children are not those of `red`). None is primitive. Degree 4 is the `Defect4` row; the first-defect selection over `Fin 3` at `r = 2, 3, 4` is the `StrictSystem` row; degrees `r ≥ 5` are not formalized |
| `K₃ ∈ Lie₃` over three letters: for `∼₂` pairs, `K₃` satisfies the shuffle relation `a ⧢ bc` (the `ab ⧢ c` form is the same family re-indexed); over any field `F` of characteristic 0 the shuffle annihilator in `(F³)^{⊗3}` is exactly the span of the eight Lyndon brackets, of dimension 8 (the brackets are shuffle-annihilated and independent over any commutative ring); `M^{⊗3}` preserves it | `Psc.Lie3.count_mul_n2`, `k3_shuffle_left`, `shuffleAnnih_iff_left`, `shuffleAnnih_br`, `eq_sum_lyndon`, `linearIndependent_lyndon`, `shuffleAnnih_iff_mem_span`, `finrank_shuffleAnnihSpace`, `shuffleAnnih_phi3`, `phi3_mem_span`, `zmod3_shuffleAnnih_not_mem_span`, `k3Vec_mem_span_lyndon`, `k3Vec_example` | full at degree three on `Fin 3` (Ree's theorem as an explicit finite statement; `Lie₃` means the span of the eight bracket vectors; `K₃` itself over `ℚ`). The spanning half fails over `ZMod 3` (`zmod3_shuffleAnnih_not_mem_span`: the word `000` is shuffle-annihilated but outside the span); the intermediate hypothesis `(3 : F) ≠ 0` is not stated. degree 4 is the `LieWeights` row; Ree's theorem in general and `Lie_r` for `r ≥ 5` are not formalized |
| `lem:descendants`, `lem:inherited`, reachability (`def:bpa`): `red` commutes with concatenation and inflation, `red(σⁿu,σⁿv) = (red u v).flatMap(red ∘ σⁿ)`; the boundaries of `red` are exactly the zero returns; the depth-`n` descendants of a block are the blocks of `red(σⁿT₁,σⁿT₂)`; swap closure preserves child-closure, balance and coincidence-freeness; the lexicographic representatives form a normalisation; states reachable from `Seeds` are blocks, the reachable set is swap-closed, and every vertex of `B_σ` is a block of some `red(σⁿab,σⁿba)` | `Psc.Descendants.red_flatten`, `red_iterate_subst`, `inherited`, `zero_return_iff`, `descR_of_isBlock`, `descR_zero_return`, `redSystem_desc`, `swapClosure_childClosed`, `lexNormalisation`, `reachable_swapClosed`, `reachable_isBlock`, `mem_bpaStates_iff_red`, `mem_bpaStatesNC_iff`, `finite_bpaStates_iff`, `exists_red_of_mem_bpaStatesNC`, `bpaSystem_desc` | full on ordered pairs, over any alphabet, in the child graph where children of coincidence blocks are also formed; it has the same noncoincident reachable states as `B_σ` and is finite iff `B_σ` is. On `B_σ` itself, with terminal coincidence blocks, the path reading of `lem:descendants` fails (Fibonacci: `fib_descR_two`). `n = 0` needs `IsBlock T` (`tmReducibleSystem`). Productivity and termination with coincidence are the `StrictSystem` row; G1 and the inherited/newborn split as a stated classification are not formalized |
| `thm:parikh`, cofactor and simple Perron root; Theorem A(iv) in full: for `P` onto with `PN = MP`, `χ_N = χ_M · χ_{N\|ker P}` (iff `P` onto); under the Perron hypotheses `IsCoprime χ_M χ_{N\|ker P}` and `β` is a simple root of `χ_N`; `ρ(N) = β` from `ℓP > 0` alone; `Q = L'P` with `L'` injective unless `Q = 0`; all on representatives | `Psc.KernelCofactor.charpoly_eq_mul_restrict`, `charpoly_eq_mul_kerRestrict`, `charpoly_eq_mul_kerRestrict_iff`, `isCoprime_charpoly_kerRestrict`, `rootMultiplicity_charpoly_eq_one`, `perron_root_of_intertwine`, `factor_through_parikh_full`, `charpoly_nrep_eq_mul`, `cofactor_int`, `isCoprime_rep`, `simple_perron_root_rep`, `factor_through_rep` | given balance, `C` nonempty, strong connectivity of `N_C`, `χ_M` irreducible and `ℓ > 0`, `ℓM = βℓ` (nonempty top tracks follow from balance, `Normalisation.top_ne_nil`). The abstract forms have a full control (a 4-state splitting of `M0`, `ker P ≠ 0`); the representative forms meet every hypothesis except `χ_M` irreducible (`wT_rep_hyps`). They are reductio lemmas: a zero-return instance would be a closed coincidence-free component; on a strict component they are restated as `StrictComponent.kernel_cofactor` (the `StrictSystem` rows), and there is none on the standing corpus (`C4StandingCorpus`). Negative controls: `P` onto, strong connectivity and irreducibility are each needed. That `β` is the only eigenvalue of modulus `β` is not formalized |
| `thm:deg23` (i) formula and (ii): `χ_{Λ²M} = X³ − UX² + det(M)tr(M)X − det(M)²`; `rank_ℚ Q₂ = 3`; `χ_{Λ²M} ∣ χ_S` over `ℚ` and `ℤ`; `S ≡ N_C (mod 2)`; `lcm(χ_M, χ_{Λ²M}) ∣ χ_{N_C}` mod 2, so `\|R\| ≥ deg lcm ∈ [3,6]`, and `\|R\| ≥ 6` when `det M` is odd and `tr M ≢ U (mod 2)` | `Psc.Cyclicity.charpoly_wedge2` (with `charpoly_fin_three`); `Psc.Degree2Sector.rank_q2`, `charpoly_wedge2_dvd_ssign_int`, `ssign_mod_two`, `lcm_dvd_nrep_mod_two`, `card_rep_ge_natDegree_lcm`, `natDegree_lcm_eq_six`, `card_rep_ge_six` | the formula over any commutative ring; the rest given a normalisation over `Fin 3`, balanced states, some `kw ≠ 0` and `χ_M` irreducible. Controls: `plastic` (`0↦1, 1↦2, 2↦01`) meets the matrix-level hypotheses with `deg lcm = 6`; `exA` meets the state-level ones and shows `χ_M` irreducible is needed (`irreducible_needed`). No control meets all of them. On a strict system they are restated as `StrictSystem.deg2_sector` (the `StrictSystem` rows); the module docstring lists the formal pieces (mismatch density, Theorem A(4), the concrete no-strict-system theorems, `C4StandingCorpus`) and states what stays informal (that a full control is a three-letter PSC counterexample). The eight-class parity table and `ρ(Λ²M) = β\|β₂\|` are not formalized; (iii) is the `Degree3Sector` row |
| `prop:cocycle`, remaining clauses: the gauge criterion (a gauge exists iff every closed walk has sign product `+1`, iff `(S^n)_{aa} = (N_C^n)_{aa}` for all `n`, iff `S = DN_CD`); `ρ(S) < β` when some pair occurs with both signs; for primitive `N_C`, `‖μ‖ = β` forces `μ = ±β` and `S = ±DN_CD`; another choice of `R` conjugates `S` by a diagonal `±1` matrix, so `χ_S` is independent of `R` | `Psc.CocycleSpectrum.exists_gauge_iff_closed_walks`, `closed_walks_iff_pow_diag`, `exists_gauge_iff`, `cocycle_spectral_strict`, `cocycle_primitive_extremal`, `cocycle_primitive_gauge`, `cocycle_extremal_iff`, `choice_of_representatives`, `charpoly_ssign_eq` | given strong connectivity of `N_C` and `L > 0`, `LN_C = βL` (primitivity for the equality case). Controls: Thue–Morse (`S = 0`), `exA` (`S = N_C`), `exB` (`S = −N_C`), `qNorm` (non-constant gauge), `twoSys` (two choices of `R`). Negative controls: `bNorm` (strong connectivity needed in the strict bound and the gauge criterion), `pNorm` (primitivity needed: eigenvalue `i` of modulus `β = 1`). The morphisms `U`, `V`, `W` and the double cover's strong connectivity are not formalized |
| Perron–Frobenius for primitive matrices (Collatz–Wielandt): `A ≥ 0`, `A^k > 0` (`k ≥ 1`) give `r > 0` and `v, u > 0` with `vA = rv`, `Au = ru`, `χ_A(r) = 0`, every root of modulus `≤ r`, one-dimensional real `r`-eigenspaces; for primitive `σ`, `ℓ > 0` with `ℓM = βℓ`; consumers `ρ(Nc) = β`, `ρ(N_C) = β` on representatives (balance only), `ρ(S) ≤ β` | `Psc.PerronExistence.exists_pos_left_eigen`, `perron_frobenius`, `exists_pos_left_eigen_inc`, `perron_inc`, `perron_root_childSystem_of_primitive`, `perron_root_rep_of_primitive`, `cocycle_spectral_bound_of_primitive` | full for primitive `A`. Controls: `M0`, `011/2/120` (primitive with `k = 2`), Thue–Morse; negative controls for each hypothesis. Strict dominance, algebraic simplicity for `A` and the irreducible non-primitive case are not formalized |
| Degree-4 defect (`lem:conc-subst` (i)–(iii) and `thm:defect-intertwiner` at `r = 4`): `n4_append`; `n4_subst` with the correction `Λ₄` explicit; the infiltration identities behind `a ⧢ bcd`, `abc ⧢ d`, `ab ⧢ cd`; for `∼₃` pairs `K₄` satisfies both shuffle relations, is block-additive and `K₄(σu,σv) = M^{⊗4}K₄(u,v)`; on representatives `Q₄S = M^{⊗4}Q₄`; `K₄ ∈ Lie₄` and `Q₄S = Φ₄Q₄` with `Φ₄ = M^{⊗4}\|_{Lie₄}` | `Psc.Defect4.n4_append`, `n4_subst`, `count_mul_n3`, `n3_mul_count`, `n2_mul_n2`, `k4_shuffle_left`, `k4_shuffle_two`, `k4_additive`, `k4_subst`, `k4_rep`, `q4_mul_ssign`; `Psc.Defect4Lie.k4Vec_mem_span_lyndon4`, `q4_col_mem_lie4`, `phi4Lie_k4Lie` | given `∼₃` on every state; the Lie half over `Fin 3`. Controls: Thue–Morse blocks `t₃`, `t̄₃` (`K₄ ≠ 0`), a ternary `∼₃` pair, `w4` (zero-return, `S = (1)`), `exT` (`S = (−1)`, algebra-only). Negative: each `∼₃` hypothesis cannot be weakened to `∼₂`. `w4Pair` has the least possible length, `12`, over at most three letters (the binomial-pair census, `docs/c4-binomial-minimal-pairs-2026-11-07.md`; a finite computation cited in the docstring, not a Lean statement). The first-defect selection is the `StrictSystem` row; the spectral consequences for `Q₄` are the `Degree4Floor` row |
| Ree at degree four and the weights of `Φ₃`, `Φ₄`: the shuffle annihilator in `(F³)^{⊗4}` is the span of the 18 Lyndon brackets (dimension `(3⁴−3²)/4`), and `ab ⧢ cd` is not redundant there: the relations `a ⧢ bcd` alone cut out a space of dimension exactly `24`, spanned by the 18 brackets and the six products `[x,y]·[z,w]` of degree-two brackets; `M^{⊗4}` preserves it; `Lie₃`, `Lie₄` are the direct sums of their content components, of dimensions the generalized Witt multiplicities (`r·m(κ) = Σ μ(t)…`): `(3,1,0), (2,2,0) ↦ 1`, `(2,1,1) ↦ 3`, `(4,0,0) ↦ 0`; `(2,1,0) ↦ 1`, `(1,1,1) ↦ 2`; for `M = Q diag(x) Q⁻¹`, `χ(Φ_r) = ∏_κ (X − x^κ)^{m(κ)}`, `r = 3, 4`; `dim ker(Φ₃ − det M) = 2` for distinct nonzero `xᵢ` | `Psc.LieWeights.eq_sum_lyndon4`, `finrank_shuffleAnnih4Space`, `r1_not_shuffleAnnih4`, `r1Annih4_cat2`, `linearIndependent_r1Basis`, `eq_sum_r1Basis`, `finrank_r1Annih4Space`, `shuffleAnnih4Space_lt_r1Annih4Space`, `phi4_mem_span`, `iSup_comp4`, `finrank_comp4_shapes`, `finrank_comp3_shapes`, `mult4_eq_wittMult`, `mult3_eq_wittMult`, `charpoly_phi4Lie`, `charpoly_phi3Lie`, `charpoly_phi4Lie_rat`, `charpoly_phi3Lie_explicit`, `finrank_ker_phi3Lie_sub_det` | over a field of characteristic 0 (the degree-three objects and Ree's theorem at degree three are `Psc.Lie3`'s); given `M` diagonalizable (for irreducible `χ_M` this is the `SectorBridge` row). The Witt formula is checked at `r = 3, 4` only. `charpoly_phi4Lie_rat` reaches the hypotheses of `WeightModulus`, `GaloisOrbit` through the `SectorBridge` row; the case analysis of `thm:sieve` at `r = 4` and `thm:deg23` (iii) are the `Degree4Floor` and `Degree3Sector` rows |
| Shared steps of `thm:deg23` (iii) and `thm:sieve`: (a) a rational `M` with irreducible `χ_M` has three distinct complex roots `x` (all its roots) and `M = Q diag(x) Q⁻¹`, `Q` invertible, in the form `charpoly_phi4Lie_rat` consumes (any three distinct roots suffice); (b) every root of the rational `χ(Φ₄)` (resp. `χ(Φ₃)`) is a weight `x^κ`, `Σκ = 4` (resp. `3`), `κ` a permutation of `(3,1,0)`, `(2,2,0)`, `(2,1,1)` (resp. `(2,1,0)`, `(1,1,1)`), never of `(4,0,0)` (resp. `(3,0,0)`); (c) for `Q ∘ S = φ ∘ Q` with `Q : K^R → V`, `im Q` is `φ`-invariant and `χ(φ\|_{im Q})` divides `χ_S` and `χ_φ`, has degree `dim im Q`, and its roots are roots of both; (d) on representatives `Q₃ S = Φ₃ Q₃` into `Lie₃` (`phi3Lie_k3Lie`) and `Q₄ S = Φ₄ Q₄`, `q_r = χ(Φ_r\|_{im Q_r})` divides `χ_S` and `χ(Φ_r)`, `deg q_r = rank Q_r`, positive with a complex root when some `K_r(j) ≠ 0`; every root of `q_r` is a root of `χ_S` and a weight of a listed shape | `Psc.SectorBridge.exists_conj_diagonal`, `exists_distinct_roots`, `exists_diagonalization`, `root_phi4Lie_rat`, `root_phi3Lie_rat`, `roots_phi4Lie_of_irreducible`, `roots_phi3Lie_of_irreducible`, `Shape4.le_three`, `Shape3.le_two`, `Shape4.triple`, `mono_eq_pow_of_cube_eq`, `X_pow_three_sub_two_irreducible`, `cube_root_two_control`, `pure_power_excluded`, `pure_power_excluded_mono`, `charpoly_restrict_dvd`, `range_invariant`, `imCharpoly_dvd_left`, `imCharpoly_dvd_right`, `natDegree_imCharpoly`, `aeval_of_imCharpoly`, `exists_root_imCharpoly`, `imCharpoly_eq_of_card_eq_one`, `linearCombination_intertwine`, `range_linearCombination_ne_bot`, `phi3Lie_k3Lie`, `q3m_intertwine`, `q3_dvd_ssign`, `q3_dvd_phi3`, `natDegree_q3`, `exists_root_q3`, `root_q3`, `exists_weight_root_q3`, `q4m_intertwine`, `q4_dvd_ssign`, `q4_dvd_phi4`, `natDegree_q4`, `exists_root_q4`, `root_q4`, `exists_weight_root_q4`, `galoisOrbit_input_q4` | (a), (b), (c) full; (d) given a normalisation over `Fin 3` with `Equiv2` (resp. `Equiv3`) states, the bridge `root_q_r` also given three distinct roots of `χ_M` (e.g. `χ_M` irreducible). Controls: `M0`, `plastic` meet `χ_M` irreducible (`m0_diagonalization`, `plastic_diagonalization`, `m0_roots_phi4Lie`, `m0_roots_phi3Lie`); `wT`, `w4` meet the state hypotheses with `im Q_r ≠ 0`, and there `q_r = χ_S` (`wT_q3_eq`, `w4_q4_eq`); the 3-cycle relabelling `0 ↦ 1 ↦ 2 ↦ 0` (`χ_M = X³ − 1`, distinct roots `1, ζ, ζ²`) on the three relabellings of `wTPair` (resp. `w4Pair`) meets every hypothesis of `root_q3`, `root_q4` and `galoisOrbit_input_q4` (`cyc3_root_q3`, `cyc4_root_q4`, `cyc4_galoisOrbit_input`; a permutation substitution, so this shows joint satisfiability only). No control meets the hypotheses of `exists_weight_root_q3`, `exists_weight_root_q4` (a child system with `χ_M` irreducible): those two are reductio lemmas. `galoisOrbit_input_q4` supplies the pair `habc`, `hq` of `GaloisOrbit` for `q = q₄`; its other hypotheses (`Irreducible χ_M`, the Pisot moduli, `1 ≤ ‖βαγ‖`, the root bound `hbound`) are not supplied, and for `q₃` only `orbit_exponent_on_beta` applies directly. A listed shape constrains `κ`, not the value: for the irreducible `X³ − 2` (Eisenstein at `2`, `X_pow_three_sub_two_irreducible`; `cubeSubst = 1/2/00`) the `(1,1,1)` and `(2,1,1)` weights equal `x₀³`, `x₀⁴` (`mono_eq_pow_of_cube_eq`, negative control `cube_root_two_control`); under `χ_M` irreducible, the Pisot moduli and `1 ≤ \|det M\|`, no `(1,1,1)` weight is a cube and no `(2,1,1)` weight a fourth power of a root (`pure_power_excluded`, `pure_power_excluded_mono`; seven of the nine `(2,1,1)` equalities fail on the moduli alone, the other two only by the Galois step, `Psc.GaloisOrbit.moduli_211_control`). The case analysis (`\|det M\| = 1` at `r = 4`, `im Q₃ ⊆ ker(Φ₃ − det M)`, `rank Q₃ ≤ 2`) and `ρ(S) ≤ β` as a bound on the roots of `χ_S` are the `Degree4Floor` and `Degree3Sector` rows (`Psc.SectorBridge.ssign_root_bound_of_perron`); semisimplicity of `Φ₄\|_{im Q₄}` is not formalized |
| `thm:deg23` (iii) on normalised representatives: every root of `q₃ = χ(Φ₃\|_{im Q₃})` is `det M`; `q₃ = (X − det M)^{rank Q₃}`; `im Q₃ ⊆ ker(Φ₃ − det M)` over `ℚ`, i.e. `M^{⊗3}K₃(T) = det M·K₃(T)` for every representative; `rank Q₃ ≤ 2`; for a primitive `σ` the root bound is discharged and the Perron root of `M` is the root `β` | `Psc.Degree3Sector.deg23_iii`, `deg23_iii_of_primitive`, `deg23_iii_of_perron`, `root_q3_eq_det`, `q3_eq_pow`, `range_q3m_le_ker`, `phi3_k3Vec_eq_det`, `rank_q3_le_two`, `perron_eq_root`, `phi3Lie_sub_smul_of_pow`, `finrank_ker_sub_det_le_two`, `finrank_ker_sub_det_eq_two`, `bound_iff_le_ker`, `census_not_mem` | given a normalisation over `Fin 3` with `∼₂` states and some `K₃ ≠ 0`, `χ_M` irreducible with roots `β, α, γ`, `‖α‖, ‖γ‖ < 1`, and either the root bound on `χ_S`, a positive left eigenvector of `M`, or primitivity. The route replaces the manuscript's Galois-stable constituents by the Galois-orbit lemma (a `(2,1,0)` root `β²δ` has modulus `> β`); semisimplicity is proved in kernel form. Reductio lemmas: the only full control is degenerate (`census_empty_control`, `im Q₃ = 0`); `m0_control` is a full control of the matrix form; `census_not_mem` shows that the census state `(011212001, 120011120)` lies in no `∼₂` normalised child system over `011/2/120` (all 24 catalogue occurrences: the `Degree3Catalogue` row). `dim_ℚ ker(Φ₃ − det M) = 2` (`finrank_ker_sub_det_eq_two`). The first-defect selection is the `StrictSystem` row |
| `comp:defect`, the 24 degree-three occurrences: each is a reachable, recurrent vertex of `B_σ` (checked seed and seven-step return paths), `∼₂` with `K₃ ≠ 0`, leaks to a coincidence block within two inflations (so it lies in no child-closed coincidence-free set), and lies in no `∼₂` normalised child system over its substitution (primitive, `χ_M = X³ − 2X² − 1`, `det M = 1`). Over the 12 automata: `B_σ` has exactly 226 vertices, 224 noncoincident, 4 of those `∼₂` (the catalogue states and their swaps); every other noncoincident vertex has first defect degree 2; no nonempty child-closed coincidence-free `∼₂` set exists. §3's four state classes and two substitution classes, exactly | `Psc.Degree3Catalogue.catalogue_spec`, `occurrences_spec`, `catalogue_counts`, `catalogue_pisot`, `catalogue_complete`, `catalogue_exact`, `catalogue_card`, `catalogue_degree_two`, `catalogue_k3_ne`, `no_closed_equiv2`, `catalogue_orbit`, `state_classes_exact`, `sigma_classes_exact`, `reversal_exchanges` | full for the 24 transcribed rows of `kernel/degree3_catalog.mojo` and their 12 automata (kernel `decide`; about 55 s and 8.9 GB peak RSS). Controls: `class9a_sigmaA_control`, `class9a_not_mem_sigmaA` (negative), `tm_closed_control` (non-vacuity), `budget_control` (fail-closed), `stats_control`. Not formalized: that the 24 are the whole corpus census (Mojo, `BoundedDegree3Exclusion`), the unique sink SCC, the `Θ(K₃)` invariants, §7 beyond the 12 automata |
| `thm:sieve` at `r = 4` and Theorem A(i)–(iii): if every state is `∼₃` and some `K₄ ≠ 0`, `χ_M` irreducible with a Pisot root `β`, and every root of `χ_S` has modulus `≤ ‖β‖`, then `\|det M\| = 1` and `χ_S` has a root of modulus `‖β‖`; with `N_C` strongly connected the `(2,2,0)` case is excluded, every root of `q₄` is `d·`(a root of `χ_M`), `dβ` is an eigenvalue of `S`, and `S = d·DN_CD` with `D ∈ {±1}` (gauge if `d = 1`, anti-gauge if `d = −1`); for primitive `σ` the root bound is discharged | `Psc.Degree4Floor.sieve4`, `sieve4_roots`, `sieve4_pisot`, `sieve4_of_primitive`, `no_220_root`, `sieve4_211`, `gauge_of_sieve4`, `gauge_or_antiGauge_of_sieve4`, `theoremA_of_primitive`, `perron_eq_pisot`, `ssign_root_bound_of_primitive`, `m0_no_degree4` | given a normalisation over `Fin 3`, and `N_C` strongly connected for the Wielandt clauses. Reductio lemmas: no control meets every hypothesis. Controls: `w4_controls` (state level, root bound at `β = 1`), `plastic_matrix_controls`, `plastic_perron_control`, `m0_perron_control`; `m0_no_degree4` (no `r = 4` child system over the `det = −2` substitution `M0`); `plastic_220_control` (the root-level sieve alone does not exclude `(2,2,0)`). The subspace form of Theorem A(ii), `q₄` as a power of `χ_{dM}`, and the composition with Theorem A(iv) are not formalized |
| Strict systems and strict components (`def:bpa`, cut-pair note §2): structure, swap closure, the zero-return child system, `N_C` strongly connected for every normalisation; Theorem A(1)–(5) of the cut-pair note; productivity and termination with coincidence; `thm:sink` in existence form | `Psc.StrictSystem.StrictSystem`, `StrictComponent`, `BpaStrictComponent`, `StrictComponent.nrep_stronglyConnected`, `StrictSystem.not_witness`, `strictSystem_of_factorSet`, `exists_strictSystem_iff`, `no_strictSystem_of_strongCoincidence`, `exists_seed_not_terminates`, `exists_strictSystem_of_not_terminates`, `StrictSystem.counterexample`, `StrictSystem.exists_strictComponent_reachable`, `exists_strictComponent_subset`, `exists_bpaStrictComponent_of_not_terminates`, `exists_bpaStrictComponent_of_finite` | full on ordered pairs over any alphabet with decidable equality. The sink step assumes nonerasure, which is needed (`erase_control`); `thm:sink` assumes finiteness of the seed's reachable set (G1 is a hypothesis). "Every sink SCC is strict" is not stated. A strict system gives BPA non-termination and an unwitnessed cut pair; a failure of strong coincidence is not known to give a strict system (C4) |
| First defect degree and its selection over `Fin 3`, `r = 2, 3, 4`, for every normalisation | `Psc.StrictSystem.defectDegree`, `StrictSystem.defectDegree_spec`, `defectDegree_eq_two_iff_kw`, `defectDegree_eq_three_iff_k3Vec`, `defectDegree_eq_four_iff_k4Vec`, `exists_rep_kw`, `exists_rep_k3Vec`, `exists_rep_k4Vec` | full; `r ≥ 5` is not covered |
| The reductio lemmas on a strict system or component over `Fin 3`: `thm:deg23` (ii), (iii), `thm:sieve` at `r = 4`, Theorem A, `thm:parikh` cofactor, `prop:cocycle` walks | `Psc.StrictSystem.StrictSystem.deg2_sector`, `StrictSystem.deg23_iii`, `StrictSystem.sieve4`, `StrictSystem.three_le_card_rep`, `StrictComponent.kernel_cofactor`, `StrictComponent.theoremA`, `StrictComponent.gauge_or_antiGauge`, `StrictComponent.closed_walk_sign` | given only primitive `M`, irreducible `χ_M`, a Pisot root (where used) and the first defect degree; every structural hypothesis is discharged. Theorem A(ii) in eigenvalue form only; A(iv) abstract only, not composed with `Q₄D`; the converse of the anti-gauge walk criterion is not proved. No control meets all hypotheses; `cycC` (`012/120/201`) fails only `χ_M` irreducible (`strictComponent_controls`), and `cyc_lcm_control` shows that hypothesis is needed for `\|R\| ≥ deg lcm`. Register: [reductio lemmas](c4-reductio-lemmas-2026-11-07.md) |
| Exclusion forms of the reductio lemmas | `Psc.StrictSystem.StrictSystem.three_le_card`, `no_strictSystem_deg2_of_card_lt`, `no_strictSystem_deg2_odd`, `no_strictSystem_deg3_of_not_eigen`, `no_strictSystem_deg4_of_abs_det_ne_one`, `no_strictComponent_deg4_of_hasBothSigns` | the hypotheses hold jointly on plastic, `011/2/120` and `m0Subst` (`no_strictSystem_deg2_odd_control`, `no_strictSystem_deg3_control`, `no_strictSystem_deg4_control`); there is no strict system over any of the three, so there the exclusions are redundant with Theorem A(4) |
| Least witness levels and concrete emptiness (Theorem A(4) on specimens) | `Psc.StrictSystem.leastWitnessLevel_spec`, `specimens_no_strictSystem`, `m0_no_strictSystem`, `plastic_vacuous`, `census_vacuous` | kernel `decide` for the listed specimens only; the corpus-wide statement is `C4StandingCorpus` (Mojo census with Lean Theorem A(4)) |
| Leave-one-out controls of the reductio lemmas at the `ChildSystem` level (solidify gate §5): the `KernelCofactor`, `Degree2Sector`, `deg23_iii_of_ne` and `theoremA_of_primitive` tables, `sieve4` in literal three-root form, a non-degenerate full control of `ssign_root_bound_of_primitive`; `rotSys 0` is the swap closure of the strict component `cycC` | `Psc.ReductioControls.kernelCofactor_leave_one_out`, `degree2Sector_leave_one_out`, `degree3Sector_leave_one_out`, `degree4Floor_leave_one_out`, `wedge2_dvd_needs_irreducible`, `theoremA_needs_irreducible`, `ssign_root_bound_full_control`, `ssign_root_bound_of_top_ne_nil`, `rot0_states_eq_cycC`, `rot0_strictComponent` | full as stated; rows marked "not constructed" or "unknown" in the module docstring (`N` for degrees 3, 4; `Irr` alone for `deg23_iii_of_ne` and `sieve4`; `SC`, `PisotRoot`) are open. A control keeping `N`, balance, `C ≠ ∅` and `Irr` together would be a strict component |
| Invariant subspaces of an irreducible `3×3` matrix are `0` or everything | `Psc.Cyclicity.invariant_eq_bot_or_top` | full |
| Positivity core: `N|v| ≥ β|v| ⇒ =`; nonnegative eigenvectors have full support; `\|x\|` is an eigenvector when `x` is one for `S` with `\|S\| ≤ N` | `Psc.PerronCore.*` | given a positive left `β`-eigenvector `L` of `N` (for primitive `M`, `Psc.PerronExistence` supplies `ℓ`; from `thm:parikh`: `L = ℓP`) |
| Wielandt's equality case: `S = c·D N D⁻¹`, `\|c\| = 1`, `\|D\| = 1` | `Psc.Wielandt.wielandt` | given `L` as above; the Perron–Frobenius existence theorem is not needed |
| Theorem A(iii): real `S`, eigenvalue `±β` ⇒ `S = ±D N D` with `D ∈ {±1}` | `Psc.Wielandt.gauge_of_real` | given `L` |
| Cycle relation `(μ/β)^{2ℓ} = 1` | `Psc.Wielandt.cycle_relation` | given `L` |
| Theorem A(ii), `(2,2,0)` eigenvalue `β²α²` impossible for PIP | `Psc.Wielandt.no_220_eigenvalue`, `Psc.Degree4Sector.*` | given `L` and that `β²α²` is an eigenvalue of `S` |
| Theorem A(ii), modulus eliminations `(3,1,0)`, `(2,2,0)`, `(2,1,1)`, `(1,1,1)` | `Psc.WeightModulus.weight_310`, `weight_220`, `weight_211`, `weight_111` | full as inequalities |
| Theorem A(ii), Galois-orbit step: some conjugate of a weight puts the largest exponent on `β`, and is again a root of the rational `q`; hence `(3,1,0)` forces a root of `q` of modulus `> β²`, `(2,1,1)` forces `\|d\| = 1`, and `(2,2,0)` forces `\|d\| = 1`, `\|α\| = \|γ\|` and `α, γ` non-real. Under the Pisot moduli, `1 ≤ \|βαγ\|` and (for two of the nine `(2,1,1)` cases) a rational `βαγ`, no `(1,1,1)` weight is a cube and no `(2,1,1)` weight is a fourth power of a root | `Psc.GaloisOrbit.exists_conj`, `orbit_exponent_on_beta`, `orbit_310_excluded`, `orbit_211_root`, `orbit_211_forces_unit`, `orbit_220_both`, `orbit_220_forces_complex_unit`, `im_ne_zero_of_norm_eq`, `aeval_conj_eq_zero` (`orbit_211_root` and `aeval_conj_eq_zero` moved here from `Psc.Degree4Floor`, which keeps deprecated aliases); pure powers: `mono111_ne_cube`, `mono211_ne_pow4_of_moduli`, `mono211_ne_pow4_galois`, `mono211_ne_pow4`, `moduli_211_control` | given `q ∈ ℚ[X]` vanishing at one weight, the bound `ρ(S) ≤ β` as a hypothesis on the roots of `q`, and `1 ≤ \|d\|`; `q = q₄ ∣ χ_S` vanishing at a weight of a listed shape is supplied by the `SectorBridge` row, and the composition with the bound is the `Degree4Floor` row; the pure-power theorems use only the moduli, `1 ≤ \|βαγ\|` and, for `mono211_ne_pow4_galois`, irreducibility and a rational `βαγ` (`moduli_211_control` shows that this cannot be dropped); non-vacuity of the shape theorems witnessed numerically by Tribonacci (module docstring) |
| Theorem A(iv): Perron simplicity gives `ker P ∩ ker χ_M(N) = 0`, hence the split hypothesis and `Q = L'∘P` | `Psc.PerronSimple.charpoly_kerP_injective`, `hsplit_of_perron`, `factor_through_parikh` | assembled with injectivity and surjectivity of `P` in the `KernelCofactor` row; given `L = ℓP > 0`, `χ_M` irreducible, `P` onto |
| Theorem A(iv), injectivity of `L` | `Psc.ConcentrationAlgebra.injective_of_irreducible` | full |
| Control `T13`/`M0`: irreducible, `∼₂`, `K₃ ≠ 0`, `M0^{⊗3}K₃ = det(M0)·K₃`, `det M0 = −2` | `Psc.ConcentrationControls.t13_*`, `m0_*` | full (kernel `decide`) |
| `χ_{M0} = x³ − 32x² + 5x + 2` is monic integral, irreducible, and Pisot | `Psc.M0Pisot.f_is_charpoly`, `f_monic`, `f_eq_map`, `f_irreducible`, `m0_pisot` | full |
| Control `011/2/120`: `0112201 ∼₂ 1200112`, both factors of `σ⁶(0)` | `Psc.ConcentrationControls.factors_equiv2`, `factors_occur` | full (kernel `decide`) |

**Not formalized.** These remain manuscript results:
- the Witt formula beyond `r = 3, 4`, and `K_r ∈ Lie_r` for `r ≥ 5`
  (`r = 3, 4` on three letters are formalized; the diagonalization of `M` from
  irreducibility of `χ_M` is the `SectorBridge` row);
- the first-defect intertwiner at degrees `r ≥ 5`, and the first-defect
  selection beyond `Fin 3`, `r = 2, 3, 4` (the `StrictSystem` row). Degrees
  2, 3 and 4 are formalized, raw and signed;
- the case analysis of `thm:sieve` for `r ≥ 5` and its `|C| = 3` clauses
  (`r = 4` is the `Degree4Floor` row, `thm:deg23` (iii) the `Degree3Sector`
  row), `ρ(Λ²M) = β|β₂|`, and the eight-class parity table;
- the finiteness hypothesis G1 (`thm:sink` is formalized conditionally on
  G1, the `StrictSystem` row) and the inherited/newborn classification as a
  stated theorem;
- strict dominance and algebraic simplicity in Perron–Frobenius, and the
  irreducible non-primitive case;
- the morphisms `U`, `V`, `W` of `prop:cocycle` and strong connectivity of the
  oriented double cover.

The Lean results are the algebraic and analytic steps of §§2–3 applied to
those inputs. A mutant of `t13_det_sector` with `det` replaced by `2` fails to
compile.

## 9. Replay

```sh
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_concentration_controls.mojo)
./tools/check_lean.sh
```
