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

The `PscVerif` library (34 modules, those below among them) passes the proof-bank
axiom audit: 1049 declarations, 767 theorems, using only `propext`,
`Classical.choice` and `Quot.sound`; no `sorry`, no local axioms, no
`native_decide`.
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
| Degree-3 intertwiner on words (`thm:defect-intertwiner` at `r = 3`, Lemma 0 of the [general-structure note](c4-general-structure-2026-11-06.md)): for `∼₂` pairs, `K₃` is additive over concatenation and `K₃(σu,σv) = M^{⊗3}K₃(u,v)` | `Psc.Incidence.n3_append`, `Psc.Incidence.n3_subst`, `Psc.Intertwiner3.k3_additive`, `k3_join`, `k3_subst`, `k3_children` | full over raw ordered pairs, block lists and child systems; `K₃ ∈ Lie₃` is the `Lie₃` row below; degrees `r ≥ 4` are not formalized |
| `thm:parikh` in matrix form for a child system: `P_C N_C = M P_C`, `λ N_C = βλ` with `λ = ℓᵀP_C > 0` | `Psc.ParikhIntertwiner.pc_nc`, `lc_nc`, `lc_pos` (with `parikh_subst`, `parikh_children_top/bot`, `Lfun_subst`) | full for the raw ordered child system: `Nc` counts raw children, so for a swap-closed system it is the oriented double cover, not the manuscript's representative `N_C = A + B` (see the next rows). `pc_nc` is unconditional; `lc_nc` assumes `ℓ ᵥ* M = βℓ`; `lc_pos` assumes `ℓ > 0` and nonempty top tracks (automatic for balanced noncoincident states). `perron_root_childSystem` gives `ρ(Nc) = β`. The rank and divisibility clauses are the next row |
| `thm:parikh`, rank and divisibility clauses, on normalised representatives (the manuscript's `N_C = A + B`): `P_R N_C = M P_R`, `rank P_R = d`, `\|R\| ≥ d`, `χ_M ∣ χ_{N_C}` over `ℚ` and `ℤ`, `N_C ∼ M` via `P_R` when `\|R\| = d` | `Psc.ParikhRank.prep_nrep`, `prep_surjective`, `card_rep_ge`, `charpoly_dvd_rep`, `charpoly_dvd_rep_int`, `similar_rep_of_equiv`, `exists_similar_rep_of_card_eq`, proved once for an abstract intertwiner (`surjective_of_intertwine`, `card_ge_of_intertwine`, `charpoly_dvd_of_intertwine`, `charpoly_dvd_int_of_rat`, `similar_of_intertwine`) | given `χ_M` irreducible, `C` nonempty, nonempty top tracks and balanced states. The double-cover versions (`pc_surjective`, `card_ge`, `charpoly_dvd`, `charpoly_dvd_int`) also hold; the double-cover `m = d` clause is vacuous under a normalisation (`card_state_eq_two_mul`: `\|C\| = 2\|R\|`; `no_equiv_fin3`). The cofactor `χ_{N_C}/χ_M` on `ker P_C` is not formalized |
| Abstract Perron comparison: every eigenvalue of a matrix dominated by `N` has modulus `≤ β`, given `λN = βλ` or only `λN ≤ βλ` with `λ > 0` (row action; the remark after `thm:parikh` writes it transposed) | `Psc.ParikhIntertwiner.spectral_bound`, `spectral_bound_of_subinvariant`, `spectral_bound_childSystem` | full as matrix lemmas; subinvariance for an escaping or leaking SCC is not derived |
| `prop:cocycle` on normalised representatives: `A`, `B`, `N_C = A + B`, `S = A − B`; every `S`-eigenvector lifts antisymmetrically to an `Nc`-eigenvector, hence `ρ(S) ≤ β` (also directly from `λN_C = βλ` and `\|S\| ≤ N_C`); Thue–Morse non-vacuity with `S ≠ N_C` | `Psc.SignedCocycle.Normalisation.Ssign`, `Nrep`, `lift_eigen`, `lift_ne_zero`, `cocycle_spectral_bound`, `cocycle_spectral_bound_rep`, `rep_eigen`, `ssign_abs_le`; `thueMorseNorm`, `thueMorse_cocycle_bound`, `thueMorse_ssign_ne_nrep` | given swap closure and `children_swap` (the latter derived for zero-return children by `Psc.Reduction.redNormalisation`), `ℓ > 0` and nonempty tracks; a normalisation forces `C` coincidence-free (`Normalisation.noncoincident`). The gauge/voltage statements, the strict and equality clauses, and independence of the choice of representatives are not formalized; the Thue–Morse control has `S = 0`, and the controls with `S ≠ 0` are in the signed-intertwiner row |
| Zero-return reduction (`def:balanced`, one step of `def:bpa`): `red u v` cuts at every zero return; for `∼₁` pairs its blocks are nonempty, balanced and irreducible, and they are the unique such factorization; `red v u` is the swap of `red u v`; the child system with `children T = red(σT₁, σT₂)` and its normalisations | `Psc.Reduction.red`, `red_top`, `red_bot`, `red_isBlock`, `red_unique`, `red_eq_iff`, `red_swap`, `equiv1_subst`, `redSystem`, `redSystem_isBlock`, `redSystem_states_isBlock`, `redSystem_children_swap`, `redNormalisation`; `tmRedSystem_eq` | full for one step, over any alphabet. `lem:descendants` (`red` commuting with inflation at depth `n > 1`), the inherited/newborn split, reachability from the seeds and finiteness G1 are not formalized; swap closure of `C` is a hypothesis |
| `thm:defect-intertwiner` at `r = 2, 3` on normalised representatives: a child equal to `i.swap` contributes `−K_r(i)`, so `Q₂S = (M⊗M)Q₂`, `Q₂S = Λ²M·Q₂` (wedge coordinates over `Fin 3`) and `Q₃S = M^{⊗3}Q₃` | `Psc.SignedIntertwiner.sum_children_signed`, `k2_rep`, `q2full_mul_ssign`, `wedge2_mulVec_kw_rep`, `q2_mul_ssign`, `k3_rep`, `q3_mul_ssign`, `q3_col_mem_lie3` | given a normalisation and the lower defects vanishing on every state (`∼₁` for `r = 2`, `∼₂` for `r = 3`). Controls: `exA` (zero-return, `S = (2)`, `kw ≠ 0`), `wT` (built by `redSystem`, `S = (1)`, `K₃ ≠ 0`), `exB` (`S = (−1)`; algebra-only: its state is reducible and its children are not those of `red`). None is primitive. The first-defect selection and degrees `r ≥ 4` are not formalized |
| `K₃ ∈ Lie₃` over three letters: for `∼₂` pairs, `K₃` satisfies the shuffle relation `a ⧢ bc` (the `ab ⧢ c` form is the same family re-indexed); the shuffle annihilator in `(ℚ³)^{⊗3}` is exactly the span of the eight Lyndon brackets, of dimension 8; `M^{⊗3}` preserves it | `Psc.Lie3.count_mul_n2`, `k3_shuffle_left`, `shuffleAnnih_iff_left`, `eq_sum_lyndon`, `linearIndependent_lyndon`, `shuffleAnnih_iff_mem_span`, `finrank_shuffleAnnihSpace`, `phi3_mem_span`, `k3Vec_mem_span_lyndon`, `k3Vec_example` | full at degree three on `Fin 3` (Ree's theorem as an explicit finite statement; `Lie₃` means the span of the eight bracket vectors). Ree's theorem in general and `Lie_r` for `r ≥ 4` are not formalized |
| Invariant subspaces of an irreducible `3×3` matrix are `0` or everything | `Psc.Cyclicity.invariant_eq_bot_or_top` | full |
| Positivity core: `N|v| ≥ β|v| ⇒ =`; nonnegative eigenvectors have full support; `\|x\|` is an eigenvector when `x` is one for `S` with `\|S\| ≤ N` | `Psc.PerronCore.*` | given a positive left `β`-eigenvector `L` of `N` (from `thm:parikh`: `L = ℓP`) |
| Wielandt's equality case: `S = c·D N D⁻¹`, `\|c\| = 1`, `\|D\| = 1` | `Psc.Wielandt.wielandt` | given `L` as above; the Perron–Frobenius existence theorem is not needed |
| Theorem A(iii): real `S`, eigenvalue `±β` ⇒ `S = ±D N D` with `D ∈ {±1}` | `Psc.Wielandt.gauge_of_real` | given `L` |
| Cycle relation `(μ/β)^{2ℓ} = 1` | `Psc.Wielandt.cycle_relation` | given `L` |
| Theorem A(ii), `(2,2,0)` eigenvalue `β²α²` impossible for PIP | `Psc.Wielandt.no_220_eigenvalue`, `Psc.Degree4Sector.*` | given `L` and that `β²α²` is an eigenvalue of `S` |
| Theorem A(ii), modulus eliminations `(3,1,0)`, `(2,2,0)`, `(2,1,1)`, `(1,1,1)` | `Psc.WeightModulus.weight_310`, `weight_220`, `weight_211`, `weight_111` | full as inequalities |
| Theorem A(ii), Galois-orbit step: some conjugate of a weight puts the largest exponent on `β`, and is again a root of the rational `q`; hence `(3,1,0)` forces a root of `q` of modulus `> β²`, `(2,1,1)` forces `\|d\| = 1`, and `(2,2,0)` forces `\|d\| = 1`, `\|α\| = \|γ\|` and `α, γ` non-real | `Psc.GaloisOrbit.exists_conj`, `orbit_exponent_on_beta`, `orbit_310_excluded`, `orbit_211_forces_unit`, `orbit_220_both`, `orbit_220_forces_complex_unit`, `im_ne_zero_of_norm_eq` | given `q ∈ ℚ[X]` vanishing at one weight, the bound `ρ(S) ≤ β` as a hypothesis on the roots of `q`, and `1 ≤ \|d\|`; `Φ`, `Q₄`, `χ_S` and the Witt weights are not formalized; non-vacuity witnessed numerically by Tribonacci (module docstring) |
| Theorem A(iv): Perron simplicity gives `ker P ∩ ker χ_M(N) = 0`, hence the split hypothesis and `Q = L'∘P` | `Psc.PerronSimple.charpoly_kerP_injective`, `hsplit_of_perron`, `factor_through_parikh` | given `L = ℓP > 0`, `χ_M` irreducible, `P` onto |
| Theorem A(iv), injectivity of `L` | `Psc.ConcentrationAlgebra.injective_of_irreducible` | full |
| Control `T13`/`M0`: irreducible, `∼₂`, `K₃ ≠ 0`, `M0^{⊗3}K₃ = det(M0)·K₃`, `det M0 = −2` | `Psc.ConcentrationControls.t13_*`, `m0_*` | full (kernel `decide`) |
| `χ_{M0} = x³ − 32x² + 5x + 2` is monic integral, irreducible, and Pisot | `Psc.M0Pisot.f_is_charpoly`, `f_monic`, `f_eq_map`, `f_irreducible`, `m0_pisot` | full |
| Control `011/2/120`: `0112201 ∼₂ 1200112`, both factors of `σ⁶(0)` | `Psc.ConcentrationControls.factors_equiv2`, `factors_occur` | full (kernel `decide`) |

**Not formalized.** These remain manuscript results:
- the weight list of `Lie₄(ℚ³)` (Witt formula), the semisimplicity of `Φ`, and
  `K_r ∈ Lie_r` for `r ≥ 4` (`r = 3` on three letters is formalized);
- the first-defect intertwiner at degrees `r ≥ 4`, and the first-defect
  selection. Degrees 2 and 3 are formalized, raw and signed;
- the cofactor `χ_{N_C}/χ_M` on `ker P_C`; `lem:descendants` (`red` commuting
  with inflation at depth `n > 1`), reachability of `C` from the seeds and the
  finiteness hypothesis G1; swap closure of `C`, which is a hypothesis
  (`children_swap` is derived for zero-return children);
- the existence of the positive left Perron eigenvector `ℓ` of the incidence
  matrix, which is assumed.

The Lean results are the algebraic and analytic steps of §§2–3 applied to
those inputs. A mutant of `t13_det_sector` with `det` replaced by `2` fails to
compile.

## 9. Replay

```sh
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_concentration_controls.mojo)
./tools/check_lean.sh
```
