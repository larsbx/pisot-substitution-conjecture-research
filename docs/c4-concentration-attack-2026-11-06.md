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

Twelve modules, all checked by the proof-bank axiom audit (`propext`,
`Classical.choice` and `Quot.sound` only; no `sorry`, no local axioms, no
`native_decide`; the whole library: 603 declarations, 408 theorems).
- *Full* means the formal statement is the stated result.
- *Given X* means the formal statement assumes X, and X is named.

| Result | Lean | Coverage |
|---|---|---|
| Block additivity of `K₂`: `n2 (x++y) = n2 x + n2 y + \|x\|_a\|y\|_b`, so concatenations of `∼₂` blocks are `∼₂` at every cut | `Psc.Binomial.n2_append`, `Equiv2.append`, `equiv2_join`, `equiv2_at_cuts` | full |
| Reduction lemma, finite form | `Psc.Binomial.ChildSystem.reduction_lemma` | full |
| Reduction lemma, limit form: two `σᵖ`-invariant limit words with different first letters, `∼₂` on a syndetic set of prefix lengths, gaps at most the maximal state length | `Psc.FixedPointLimit.reduction_limit` (with `limit_spec`, `limit_fixed`, `limit_zero`, `grow_of_nonerasing`, `fixed_points_equiv2_syndetic`) | given a nonerasing `σ` under which every state is strictly lengthened (true for a suitable power of a primitive `σ`, not formalized) |
| Irreducible noncoincident balanced pairs have distinct first letters | `Psc.Binomial.heads_ne` | full |
| Galois lemma: an eigen-row of `Λ²M` vanishing on a nonzero rational vector is zero | `Psc.Cyclicity.eigenrow_wedge2` (via `cyclic_of_irreducible`, `irreducible_wedge2`, `ConcentrationAlgebra.eigenrow_eq_zero`) | given `χ_M` irreducible; that `K₂(σT) = Λ²M·K₂(T)` in these coordinates is `prop:midarea`, not formalized |
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
- the weight list of `Lie₄(ℚ³)` (Witt formula) and the semisimplicity of `Φ`;
- the first-defect intertwiner `Q_r S = Φ_r Q_r` and the bound `ρ(S) ≤ β`
  (`thm:defect-intertwiner`, `prop:cocycle`);
- the identification of `N`, `S`, `P`, `L` with the data of an actual strict
  component (`thm:parikh`).

The Lean results are the algebraic and analytic steps of §§2–3 applied to
those inputs. A mutant of `t13_det_sector` with `det` replaced by `2` fails to
compile.

## 9. Replay

```sh
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_concentration_controls.mojo)
./tools/check_lean.sh
```
