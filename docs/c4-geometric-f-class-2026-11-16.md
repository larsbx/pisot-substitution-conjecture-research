# C4 on the geometric property (F) class: automatic bounded gaps, coincidence rank, and a parity refinement of Barge's bound — 2026-11-16

**Status:** recorded proofs with an exact corpus replay. Theorem FC1 is
elementary and uses no literature import; it uses Theorem A and the "Powers"
paragraph of the cut-pair note, which are on main (§1). Theorems FC2, P,
FC3, N and Fork are conditional on the imports listed in §1. All six were
verified by independent adversarial re-derivation within the session of
2026-11-15/16 (Theorem Fork from a sketch, written out here for the first
time); none is machine-checked, and independent human review is pending for
all of them, FC1 included. Universal C4 remains open; nothing here changes a
governed claim status (C4, #138, #139, #84, G1 and PSC are unchanged).
[Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
Baseline `main@febe7535`.

*Update 2026-11-16 (round 2).* The text of this note is that of round 1.
Three of its statements are corrected or extended by dated additions that
leave the round-1 sentences in place: Theorem FC1 is now machine-checked
(§10(a)); Theorem FC3 extends to "(F) and `dim H¹ = 3`" for every
determinant (§10(b)); and two sentences of §7 on unimodularity are
superseded (§10(c)). Universal C4 remains open and no governed claim status
changes.

Literature gate:
[`c4-geometric-f-class-literature-2026-11-16.md`](c4-geometric-f-class-literature-2026-11-16.md).
The [FC2 rank-transfer review](c4-fc2-rank-transfer-review-2026-11-16.md)
checks the half-open endpoint convention in §4 and supplies the cited
continuous-eigenfunction argument for the rank comparison in §1. It also
records the range of the proof in arbitrary degree and its Lean interface.
Record of the attempt that produced these statements, with the routes that
failed: [`c4-closure-attempt-2026-11-16.md`](c4-closure-attempt-2026-11-16.md).
Canonical implementation `kernel/psc/c4_geometric_f.mojo`, regression
`kernel/tests/test_c4_geometric_f.mojo`.

The note answers one question. C4 asks that no strict system exist; its only
hypothesis beyond "some letter pair is not strongly coincident" is that the
equal-Parikh cuts of the two rays have bounded gaps. Is that hypothesis ever
automatic? **Yes, on the whole geometric property (F) class** (Theorem FC1;
1,794 of the 4,554 corpus specimens). On that class C4 is therefore
equivalent to left strong coincidence of all pairs (Theorem FC1) and,
conditionally on the imports of Theorem FC2 and (for the spectrum) on BBK Cor. 5.2, to strong coincidence on both
sides and to pure discrete spectrum (Corollary E). Within this note that is
settled only where an endpoint map is eventually constant (prior art in part, §8) and, conditionally on its imports, on
an arithmetic subclass (Theorem FC3). The sections are: §2 the state map and
(F); §3 Theorem FC1;
§4 the coincidence rank on (F); §5 the parity refinement; §6 the class
theorem and the necessary conditions; §7 Theorem Fork; §8 prior art; §9 the
five "work shown" headings, with replay, controls and non-claims.

## 1. Standing class, notation, imports

**PIP3.** `σ` is a primitive substitution on `{0,1,2}` with incidence matrix
`M` (`M[a][b] = |σ(b)|_a`, so `p(σ(w)) = M p(w)` for the Parikh vector `p`),
whose characteristic polynomial `χ_M` is irreducible over `ℚ` with roots
`β > 1 > |λ₂|, |λ₃|`. Put `ρ = max(|λ₂|, |λ₃|) < 1`. `|det M| = 1` is not
assumed. Every `σ ∈ PIP3` is translation-aperiodic, as BBK, B15 and BD08
require: a periodic subshift has rational letter frequencies, whereas the
entries of `r` below are ℚ-independent (proof of Lemma 6). BBK, footnote 4,
notes this for Pisot substitutions with `dim V ≥ 2`.

- `ℓ > 0` is a left Perron row, `ℓ M = β ℓ` (tile lengths); `η₂, η₃ ∈ ℂ³` are
  left eigenvectors for `λ₂, λ₃`; `r > 0` is the right Perron column with
  `ℓ·r = 1` (letter frequencies per unit length). `ℓ_max`, `ℓ_min` are the
  extreme entries of `ℓ`.
- `g(a)` and `g_R(a)` are the first and last letters of `σ(a)`. A letter is
  `g`-periodic if `g^k(a) = a` for some `k ≥ 1`.
- Letters `a ≠ b` are **left strongly coincident** if for some `n` there are
  factorisations `σⁿ(a) = P x S`, `σⁿ(b) = P′ x S′` with a letter `x` and
  `p(P) = p(P′)`; **right** strongly coincident if instead `p(S) = p(S′)`.
  `ν_L` (`ν_R`) is the largest size of a set of letters no two of which are
  left (right) strongly coincident; `SC_L(σ)` means `ν_L = 1`, `SC_R(σ)`
  means `ν_R = 1`.
- A **strict system** is a finite nonempty set of ordered irreducible
  noncoincident balanced pairs closed under children
  ([cut-pair note](c4-cut-pair-productivity-2026-11-04.md) §2). `C4(σ)` is
  read as "`σ` has no strict system"
  ([finite-domain note](c4-finite-domain-closure-2026-11-05.md) §1: C3-local
  holds for every strict component exactly when there is none).
- `σ^R` is the reversal (`σ^R(a)` is `σ(a)` read backwards); it has the same
  `M`, so `σ^R ∈ PIP3`, and `g_{σ^R} = g_R`.
- `Ω_σ` is the tiling space with tile lengths `ℓ`, `Φ` the inflation
  homeomorphism, `T ↦ T − t` the flow. `e₂(M)` is the sum of the principal
  `2×2` minors, so `χ_M(t) = t³ − (tr M) t² + e₂(M) t − det M`. `dim H¹`
  always means `dim H¹(Ω_σ; ℚ)`.

**Imports.** Each is used only where the table says.

| Tag | Source and statement | Hypotheses | Read | Used in |
| --- | --- | --- | --- | --- |
| BBK | Baker–Barge–Kwapisz, Ann. Inst. Fourier 56 (2006) 2213–2248: Def. 3.1 (the geometric realization `h_φ`); Def. 4.1 (coincidence rank `cr_φ`: the maximal number of strands over one point of `V/Σ` no two of which are coincident); Remark 4.3 (for every `q ∈ V/Σ`, `cr_φ` is the largest size of a pairwise non-coincident family of states over `q`); Thm 4.2 (the geometric realization `h_φ` is uniformly finite-to-one, a.e. `cr_φ`-to-one, with minimal fibre cardinality `cr_φ`); Thm 5.1 (the eigenfunctions are `χ_u ∘ h_φ`); Cor. 5.2 (pure discrete spectrum iff `cr_φ = 1`) | primitive, translation-aperiodic, `λ` a Pisot number (their Def. 2.1); reducible and non-unimodular allowed | full text | FC2 (Def. 4.1, Remark 4.3); Corollary E (Cor. 5.2); §5–§7 (Thm 4.2, Thm 5.1; Def. 3.1 in §7) |
| BD02 | Barge–Diamond, Bull. Soc. Math. France 130 (2002) 619–626, Theorem 1: some pair of distinct letters is left strongly coincident | Pisot type: all non-Perron eigenvalues of modulus strictly between 0 and 1 | in full | FC2, Theorem N (remark), Theorem Fork |
| B15 | Barge, Bull. Soc. Math. France 143 (2015), arXiv:1301.7094: Thm 4(1)–(5); Thm 5; Thm 12; Lemmas 13, 14; Example 16 (Thue–Morse); Prop. 19; Lemma 20; exact sequence (4.1); Thm 22 (`λ` of degree `d` and odd norm, `cr = 2 ⇒ dim H¹ ≥ 2d − 1`); the proper version of a substitution (§4) | primitive, non-periodic, Pisot dilation; Thm 12 also border forcing and no pure discrete spectrum; Thm 22 odd norm | full text; the proofs of Thm 4 are deferred there to other papers and were not followed; the references for the proper version (Durand; Barge–Diamond 2001) were not read | Lemma S, Theorem P, FC3(b), Theorem N, Theorem Fork; Example 16 only in the remark after Lemma 8 |
| BD08 | Barge–Diamond, Proc. Amer. Math. Soc. 136 (2008) 2183–2191, arXiv:math/0702669: Lemma 2, Corollary 3, Theorem 4 and its proof | primitive, aperiodic | TeX source | §5.1, Lemma 7, Theorem P, Theorem Fork |
| Repo | Theorem A of the [cut-pair note](c4-cut-pair-productivity-2026-11-04.md) §2 (formalised in Lean, `proof/PscVerif/PscVerif/StrictSystem.lean`) and the "Powers" paragraph of its §3 (prose only, not formalised; the direction used is re-proved in step (S) of §3 below); Lemma F(c) of the [cut-attractor note](c4-cut-attractor-window-2026-11-05.md) | nonerasing `σ` for Theorem A; the Powers paragraph is stated there for primitive `σ` with irreducible Pisot incidence, and the direction used needs only nonerasure; primitive for F(c) | on main | FC1, FC3, Theorem N, Theorem Fork |
| Std | Standard facts with no locator on disk: `Ȟ¹(X; ℤ) = [X, S¹]` for compact metric `X`; the winding number of a circle-valued map along a uniquely ergodic flow; the Gottschalk–Hedlund theorem; vanishing of `Ȟ²` in covering dimension at most one and the classification of line bundles; the maximal equicontinuous factor of a minimal flow is determined by its continuous eigenfunctions | — | **not read; marked where used** | Theorem Fork; and the identification of the two coincidence ranks (next paragraph), on which Theorems P, FC3(b),(c), N(2) and Fork rest |

Barge–Kwapisz, Amer. J. Math. 128 (2006), was not obtained during the proof
attempts or when the proofs below were written, and no proof uses it. It was
obtained on 2026-11-16, during the audit of this note, from the
author-hosted PDF that repository gates of 2026-11-11 already cite, and read
in part; what was read is recorded in the literature gate and in §8.

*The two coincidence ranks.* The maximal equicontinuous factor map of B15
is written `g_max` below (B15 writes `g`). The identification of the BBK
coincidence rank with the minimal fibre cardinality of `g_max` is a
derivation of this note, not a printed statement of B15. BBK Thm 4.2 gives
the minimal fibre cardinality of `h_φ` as `cr_φ`. By BBK Thm 5.1 the
eigenfunctions are the `χ_u ∘ h_φ`; they separate exactly the fibres of
`h_φ`, so on the minimal set `Ω_σ` of BBK's strand space `h_φ` is `g_max`
**[Std]**. (BBK's strand space may contain finitely many non-recurrent
orbits besides `Ω_σ`, their footnote 5; they lie over a set of measure zero
and do not change the almost-everywhere fibre cardinality; by B15 Thm 4(1) the almost-everywhere fibre cardinality of `g_max` is its minimum, so the minimum is `cr_φ`.) B15 §2 compares
its rank only with the minimal rank of Barge–Kellendonk and with the
coincidence rank of Barge–Kwapisz 2006, and does not cite BBK. The
identification is stated, without proof and with reference to BBK, in
Barge–Bruin–Jones–Sadun §1 and in Barge, arXiv:1505.04408, §1, items
(1)–(3). It is used in §5–§7, not in Theorems FC1 and FC2.

## 2. The prototile state map and property (F)

**Lemma 1 (arithmetic of `ℓ`).** Let `σ ∈ PIP3`.

1. If `w ∈ ℚ³` and `ℓ·w = 0`, then `w = 0`.
2. `v ↦ (ℓ·v, η₂·v, η₃·v)` is injective on `ℝ³`. Hence for all `a, b ≥ 0`
   the set `{v ∈ ℤ³ : |ℓ·v| ≤ a, |η₂·v| ≤ b, |η₃·v| ≤ b}` is finite.
3. No eigenvalue of `M` is `0` or a root of unity; `M^k − I` is invertible
   over `ℚ` for every `k ≥ 1`.

*Proof.* (1) `ℓ·M^k w = β^k ℓ·w = 0` for `k = 0, 1, 2`, and for `w ≠ 0` the
vectors `w, Mw, M²w` span `ℚ³` because `χ_M` is irreducible; then `ℓ = 0`.
(2) The roots of an irreducible polynomial over `ℚ` are distinct, so
`ℓ, η₂, η₃` is a basis of `ℂ³`; a bounded set of lattice points is finite.
(3) The roots are conjugate; a root `0` or a root of unity would make all of
them `0` or of modulus one, against `β > 1`. ∎

**States.** A *state* is a pair `(j, v)` with `j` a letter, `v ∈ ℤ³` and
`0 ≤ ℓ·v < ℓ_j`: the lattice point `v` seen from the left end of a tile of
type `j` that contains it. By Lemma 1(1), `v = 0 ⟺ ℓ·v = 0`, so a state is a
letter together with a position `ℓ·v ∈ [0, ℓ_j)` in the module `ℓ·ℤ³`. The
sub-tiles of `σ(j)` partition `[0, βℓ_j)` into half-open intervals, so there
is exactly one factorisation `σ(j) = P j′ S` with

```text
ℓ·p(P)  ≤  ℓ·Mv  <  ℓ·p(P) + ℓ_{j′},        f(j, v) := (j′, Mv − p(P)),
```

and `f(j, v)` is again a state. *Vertex states* `(j, 0)` are forward
invariant: `f(j, 0) = (g(j), 0)`.

> **(F)**: no `f`-periodic state has `v ≠ 0`.

**Lemma 2 (powers).** `f_{σ^m} = f^m` for every `m ≥ 1`.

*Proof.* If `f(j, v) = (j₁, Mv − p(P₁))` with `σ(j) = P₁ j₁ S₁` and
`f(j₁, v₁) = (j₂, Mv₁ − p(P₂))` with `σ(j₁) = P₂ j₂ S₂`, then
`σ²(j) = σ(P₁) P₂ j₂ S₂ σ(S₁)` and `f²(j, v) = (j₂, M²v − p(σ(P₁)P₂))` is a
state, i.e. `ℓ·p(σ(P₁)P₂) ≤ ℓ·M²v < ℓ·p(σ(P₁)P₂) + ℓ_{j₂}`. That is the
defining property of `f_{σ²}(j, v)`. Induction on `m`. ∎

**Lemma 3 (finiteness; the Pisot bound).** Let
`D = max |η_i·p(P)|` over `i ∈ {2,3}` and all proper prefixes `P` of the
images `σ(j)`, and `B = D/(1 − ρ)`. For a state `s = (j, v)` write
`‖s‖_i = |η_i·v|`.

1. `‖f(s)‖_i ≤ ρ‖s‖_i + D`, hence `‖fⁿ(s)‖_i ≤ max(‖s‖_i, B)` for all `n`.
2. For every `b` the set of states with `‖s‖₂, ‖s‖₃ ≤ b` is finite. So every
   `f`-orbit is eventually periodic.
3. Every `f`-periodic state has `‖s‖_i ≤ B`.
4. (F) holds iff every state reaches a vertex state under iteration of `f`.

*Proof.* (1) `η_i·(Mv − p(P)) = λ_i η_i·v − η_i·p(P)`; by induction
`‖fⁿ(s)‖_i ≤ ρⁿ‖s‖_i + (1 − ρⁿ)B`. (2) Lemma 1(2) with `0 ≤ ℓ·v < ℓ_max`.
(3) If `f^k(s) = s` then `‖s‖_i ≤ ρ^{kn}‖s‖_i + B` for all `n`. (4) An orbit
is eventually periodic by (2); under (F) its periodic part consists of
vertex states. Conversely a periodic state whose orbit meets a vertex state
is itself a vertex state, since those are forward invariant. ∎

Irreducibility enters through Lemma 1; the Pisot property only through
`ρ < 1`.

**Lemma 4 (interior periodic addresses, powers, reversal).** Let `σ ∈ PIP3`.

1. A state `(j, v)` with `v ≠ 0` satisfies `f^k(j, v) = (j, v)` iff there is a
   factorisation `σ^k(j) = P j Q` with `(M^k − I) v = p(P)`; then `P` and `Q`
   are nonempty. Conversely, for every factorisation `σ^k(e) = P e Q` with
   `P`, `Q` nonempty and `v := (M^k − I)^{-1} p(P) ∈ ℤ³`, `(e, v)` is a state
   with `v ≠ 0` and `f^k(e, v) = (e, v)`. Such a triple `(k, e, P)` is an
   **interior periodic address**; (F) says there is none.
2. (F) holds for `σ` iff it holds for `σ^m`.
3. (F) holds for `σ` iff it holds for `σ^R`.

*Proof.* (1) By Lemma 2, `f^k(j, v) = (j′, M^k v − p(P))` for the
factorisation `σ^k(j) = P j′ Q` with
`ℓ·p(P) ≤ β^k ℓ·v < ℓ·p(P) + ℓ_{j′}`. If this is `(j, v)`, then
`(M^k − I)v = p(P)`, `ℓ·p(P) = (β^k − 1) ℓ·v > 0` so `P ≠ ε`, and
`ℓ·p(P) < (β^k − 1) ℓ_j = ℓ·p(P) + ℓ·p(Q)` so `Q ≠ ε`. If instead a
factorisation with `(M^k − I)v = p(P)` is given, then `M^k v − p(P) = v` has
`ℓ`-value in `[0, ℓ_j)`, so it is the factorisation used by `f^k` and
`f^k(j, v) = (j, v)`. For the last statement,
`ℓ·v = ℓ·p(P)/(β^k − 1)` lies in `(0, ℓ_e)` exactly because `P` and `Q` are
nonempty, and `β^k ℓ·v = ℓ·v + ℓ·p(P) ∈ [ℓ·p(P), ℓ·p(P) + ℓ_e)`, so
`f^k(e, v) = (e, M^k v − p(P)) = (e, v)`. (2) `f_{σ^m} = f^m` has the same
periodic states as `f`. (3) `(σ^R)^k(e) = Q^R e P^R`, and
`p(Q) = (M^k − I) e_e − p(P)` gives
`(M^k − I)^{-1} p(Q^R) = e_e − v ∈ ℤ³`. So interior periodic addresses of
`σ` and `σ^R` correspond. ∎

**Lemma 5 (identifications; used in no proof below).**

1. *Minervino–Thuswaldner.* Their map `T_σ(y, b) = (αy − δ(P), a)`
   (arXiv:1402.2002 §4.1) is `f` read on positions, with `α = β`,
   `δ(P) = ℓ·p(P)` and admissible points `y ∈ V[β⁻¹] ∩ [0, ℓ_b)`, `V = ℓ·ℤ³`,
   `V[β⁻¹] = ⋃_k β^{−k} V`. By their Prop. 9.4 the geometric property (F)
   of their Def. 9.3 says that every admissible point reaches position `0`.
   This is (F): `βV ⊆ V`, so a point `β^{−k} ℓ·w` is a lattice state after `k`
   steps, and by Lemma 3(4) (F) says that every lattice state reaches a vertex
   state. No unimodularity is used.
2. *Corollary LC5.* For an overlap `(i, j, w)` of negative offset the top
   tile starts inside the bottom tile at relative position `−ℓ·w`, and the
   leftmost step of the
   [leftmost-chain note](p1b-leftmost-chain-periodic-pair-2026-10-05.md) is
   `(i, j, w) ↦ (g(i), f(j, −w))` (its Lemma S: the top index is `0`);
   positive offsets are the mirror image. So the terminal leftmost cycles are
   the cycles of `g × f` on (`g`-periodic letters) × (`f`-periodic states with
   `v ≠ 0`), and their number is `2 Σ gcd(|C|, |G|)` over the interior
   `f`-cycles `C` and the `g`-cycles `G`. "No terminal leftmost cycle" is
   (F). Replayed on every corpus specimen (§9).

## 3. On (F) bounded gaps are automatic: Theorem FC1

**Theorem FC1.** Let `σ ∈ PIP3` satisfy (F). Let `m ≥ 1`, `τ = σ^m`, and let
`c ≠ c′` be letters with `g^m(c) = c`, `g^m(c′) = c′`. Let `X_c`, `X_c′` be
the `τ`-fixed right-infinite words beginning with `c`, `c′`, and
`V_c, V_c′ ⊆ ℤ³` the sets of Parikh vectors of their finite prefixes. Then:

1. there is `N ≥ 0` with `M^{mN}(V_c ∪ V_c′) ⊆ V_c ∩ V_c′`;
2. consecutive elements of `V_c ∩ V_c′`, ordered by `ℓ·`, are at `ℓ`-distance
   at most `β^{mN} ℓ_max`;
3. if `c, c′` are not left strongly coincident, the blocks of `(X_c, X_c′)`
   between consecutive common vertices form a strict system for `τ`, and `σ`
   has a strict system.

Consequently, for `σ ∈ PIP3` with (F) the following are equivalent: `σ` has
a strict system; some pair of distinct `g`-periodic letters is not left
strongly coincident; `SC_L(σ)` fails.

*Proof.* The rays exist: `τ(c)` begins with `c` and is not `c` (else
`M^m e_c = e_c`, against Lemma 1(3)), so `τⁿ(c)` is a strictly increasing
chain of prefixes. Write `y₀ = 0, y₁, y₂, …` for the elements of `V_c` in
order (`y_n = p(X_c[0, n))`), and `y′_n` for those of `V_c′`. The positions
`ℓ·y_n` increase strictly to infinity, `ℓ·(y_{n+1} − y_n) ≤ ℓ_max`, and
`M^m V_c ⊆ V_c` because `τ` maps prefixes of `X_c` to prefixes of `X_c`.

*Relative states.* For `y ∈ V_c` let `n` be the index with
`ℓ·y′_n ≤ ℓ·y < ℓ·y′_{n+1}` and put

```text
s(y) := (X_c′[n],  y − y′_n),
```

the tile of `X_c′` that contains the point `y`, and `y` seen from its left
vertex. It is a state. Define `s′(y′)` for `y′ ∈ V_c′` symmetrically, and let
`R` be the set of all `s(y)` and `s′(y′)`.

*(E) Equivariance: `s(M^m y) = f^m(s(y))`.* Let `s(y) = (j, v)`, `j = X_c′[n]`,
`v = y − y′_n`, and `f_τ(j, v) = (j′, M^m v − p(P))` with `τ(j) = P j′ S`.
The word `τ(X_c′[0, n)) P` is a prefix of `X_c′ = τ(X_c′)` followed by the
letter `j′`; its Parikh vector is `y″ = M^m y′_n + p(P) ∈ V_c′`. Since
`M^m y − y″ = M^m v − p(P)` has `ℓ`-value in `[0, ℓ_{j′})`, the tile of `X_c′`
containing the point `M^m y` is that `j′`-tile, and
`s(M^m y) = (j′, M^m v − p(P)) = f_τ(s(y)) = f^m(s(y))` by Lemma 2.

*(C) Common vertices: `y ∈ V_c` lies in `V_c′` iff `s(y)` is a vertex state.*
`s(y) = (j, y − y′_n)` is a vertex state iff `y = y′_n`; and if `y = y′_k`
then `n = k`.

*(Fin) `R` is finite, with an explicit bound.* Let `D_τ` be the constant `D`
of Lemma 3 for `τ` and `B_τ = D_τ/(1 − ρ^m)`. Claim: `|η_i·y| ≤ B_τ` for
every `y ∈ V_c ∪ V_c′`. For `y = y_N` with `N ≥ 1` there is a unique `n` with
`|τ(X_c[0, n))| ≤ N < |τ(X_c[0, n+1))|`, so `X_c[0, N) = τ(X_c[0, n)) P` with
`P` a proper prefix of `τ(X_c[n])`, and `n < N` because `|τ(c)| ≥ 2`. Then
`y_N = M^m y_n + p(P)` and `|η_i·y_N| ≤ ρ^m |η_i·y_n| + D_τ`; the claim
follows by induction from `y₀ = 0`. Hence every relative state has
`‖s‖_i ≤ 2B_τ`, and by Lemma 3(2) `R` is contained in the finite set of
states with `‖s‖_i ≤ 2B_τ`.

*(N) A uniform `N`.* By (F) and Lemma 3(4) every `s ∈ R` has a least
`n(s) ≥ 0` with `f^{n(s)}(s)` a vertex state. Let `N₀ = max_{s ∈ R} n(s)` and
`N = ⌈N₀/m⌉`. (By Lemma 3(1) the orbit of `s` stays among the states with
`‖·‖_i ≤ max(B, 2B_τ)` and visits no state twice before it reaches a vertex
state, so `N₀` is less than the number of those states.) For `y ∈ V_c`,
`s(M^{mN} y) = f^{mN}(s(y))` by (E), and this is a vertex state because
`mN ≥ n(s(y))` and vertex states are forward invariant; by (C),
`M^{mN} y ∈ V_c′`, and `M^{mN} y ∈ V_c`. The same holds for `y′ ∈ V_c′`. This
is (1).

*(G) Gaps.* The points `z_n = M^{mN} y_n` lie in `V_c ∩ V_c′`, `z₀ = 0`,
`ℓ·z_n = β^{mN} ℓ·y_n` increases to infinity, and
`ℓ·(z_{n+1} − z_n) ≤ β^{mN} ℓ_max`. This is (2); in letters the gaps are at
most `β^{mN} ℓ_max/ℓ_min`.

*(S) The strict system.* Let `0 = z₀ <_ℓ z₁ <_ℓ ⋯` now denote all of
`V_c ∩ V_c′`, an infinite set by (2), and let `(u_k, v_k)` be the pair of
factors of `X_c`, `X_c′` between `z_k` and `z_{k+1}`. Each `(u_k, v_k)` is a
balanced pair (`p(u_k) = z_{k+1} − z_k = p(v_k)`) and is irreducible (a proper
balanced prefix would be a common vertex strictly between). If some
`(u_k, v_k)` were coincident, `u_k = v_k = x` for a letter `x`, then for `n`
large `τⁿ(c)` and `τⁿ(c′)` would contain `x` after prefixes of Parikh vector
`z_k`: a left strong-coincidence witness for `c, c′`. So under the hypothesis
of (3) no block is coincident. There are finitely many distinct blocks, their
lengths being bounded by (2). The set `C` of blocks is stable under
`τ`-children: `(τ(u_k), τ(v_k))` is the part of `(X_c, X_c′)` between the
common vertices `M^m z_k` and `M^m z_{k+1}`, and its complete balanced
factorisation cuts it exactly at the common vertices in between. So `C` is a
strict system for `τ`. By the "Powers" paragraph of the cut-pair note the
irreducible factors of `σ^r(C)`, `0 ≤ r < m`, form a strict system for `σ`
(a coincident factor of `σ^r(S)` would inflate to coincident factors of
`τ(S)`).

*The equivalences.* If two distinct `g`-periodic letters are not left
strongly coincident, (3) with `m` a common period gives a strict system; this
is the only implication that uses (F). Conversely, by Theorem A(3),(4) the
first-letter pairs `A(C)` of a strict system are mapped into `A(C)` by
`g × g` without collapsing and none is left strongly coincident; iterating
`g × g` on one of them reaches a pair of distinct `g`-periodic letters in
`A(C)`. Finally, if `a ≠ b` are not left strongly coincident, then for `n`
large `gⁿ(a)`, `gⁿ(b)` are `g`-periodic, they are distinct (equal first
letters of `σⁿ(a)`, `σⁿ(b)` are a witness with empty prefixes), and they are
not left strongly coincident (a witness for them at level `k` is a witness
for `a, b` at level `n + k`, read in the first images). ∎

*Where the hypotheses enter.* Irreducibility: Lemma 1, i.e. a state is a
letter and a position, the three eigen-coordinates determine a lattice point,
and `M^m e_c ≠ e_c`. Pisot: `ρ < 1` in (Fin) and Lemma 3. (F): only in (N).
Neither the determinant nor any source is used. The proof does not use the
size of the alphabet; it is recorded for three letters because that is the
standing class and the replayed one.

*Without (F).* Steps (E), (C), (Fin) hold for every `σ ∈ PIP3`. A vertex whose
relative state enters an interior `f`-cycle never becomes a common vertex
under `M^m`, so (N) fails; whether the common vertices are nevertheless
relatively dense is then a separate question, on which this note says
nothing.

*Replay.* `kernel/tests/test_c4_geometric_f.mojo` computes `R` exactly, as
the overlap closure of the root `(c, c′, 0)` at the levels divisible by the
joint period, and `N₀` (its "transient", in `f`-steps):
`test_fixed_ray_relative_states_match_the_literal_definition` and
`test_fc1_inclusion_on_words` on `1/2/02` (11 relative states per pair,
`N₀ = 7`, `m = 3`, so `N = 3`: `M⁹` sends the first 60 vertices of each ray
into both vertex sets and `M⁶` does not); the corpus counts are in §9.

## 4. The coincidence rank on (F)

### 4.1 Strands, the return lattice, states

Notation of BBK §§2–4, specialised to PIP3 (`V = ℝ³`, `Γ = ℤ³`,
`E^s = ker ℓ`, `E^u = ℝ r`). A *labelled edge* `(x, i)` is the segment from
`x ∈ ℝ³` to `x + e_i`, with label `i`. A *strand* is a sequence of labelled
edges, each starting where the previous one ends. `Φ` replaces the edge
`(x, i)` by the strand that starts at `Mx` and is labelled by `σ(i)`. Two
strands are *coincident* if for some `k ≥ 0` their `Φ^k`-images share a
labelled edge. BBK's lattice `Σ ⊆ Γ` (their (3.1)–(3.3)) contains `x′ − x`
whenever a strand of the strand space carries two edges `(x, i)`, `(x′, i)`
with the same label, and `cr_φ` counts strands over one point of `V/Σ`.

**Lemma 6 (return lattice).** For `σ ∈ PIP3` the group `Λ_ret` generated by
the vectors `p(w)`, `w` a nonempty legal word such that `w w₁` is legal
(`w₁` the first letter of `w`), is `ℤ³`. Hence `Σ = Γ = ℤ³`.

*Proof.* This is Theorem R of the
[fibre gate](p1b-periodic-pair-fibre-literature-gate-2026-10-02.md), whose
proof is repeated because BBK defer the statement to a paper that had not
been obtained when this was written (Barge–Kwapisz 2006, which proves the
unimodular case; §8). Let `χ: ℤ³ → ℚ/ℤ` be a homomorphism vanishing on
`Λ_ret`, and `x` a two-sided sequence of the subshift. Put `G(n) = χ(p(x_{[0,n)}))` for `n ≥ 0`
and `G(n) = −χ(p(x_{[n,0)}))` for `n < 0`. If `n < m` and `x_n = x_m` then
`p(x_{[n,m)}) ∈ Λ_ret`, so `G(m) = G(n)`: `G(n) = H(x_n)` for a function `H`
on letters. Then `χ(e_a) = H(c) − H(a)` for every legal word `ac`, i.e. every
letter `c` that can follow `a` has `H(c) = K(a) := H(a) + χ(e_a)`. So
`H(x_{n+1}) = K(x_n)`, and for each value `h` the numbers of `n < N` with
`H(x_n) = h` and with `K(x_n) = h` differ by at most one. Dividing by `N`
(letter frequencies exist and are proportional to `r`):
`Σ_{H(a)=h} r_a = Σ_{K(a)=h} r_a`. The entries of `r` are ℚ-independent (a
rational relation would hold for the conjugate eigenvectors, which form a
basis), so `H = K`, `χ(e_a) = 0` for all `a`, `χ = 0`. A proper subgroup of
`ℤ³` is annihilated by a nonzero such `χ`; so `Λ_ret = ℤ³`. Every legal word
occurs in an inflation-periodic strand of the strand space, so
`Λ_ret ⊆ Σ ⊆ Γ = ℤ³`. ∎

With Lemma 6 the quotient `Γ/Σ` is trivial, the vectors `u_i` of BBK (3.6)
vanish, and a strand lies over `0 ∈ V/Σ` iff its vertices are in `ℤ³` (an
*integer strand*). From here on `cr(σ) := cr_φ` of BBK Def. 4.1.

*States.* BBK (4.6): the states over `0` are the labelled edges `(x, i)`,
`x ∈ ℤ³`, that meet `E^s` in a point other than their end point, i.e.
`ℓ·x ≤ 0 < ℓ·x + ℓ_i`. With `v = −x` this is the state `(i, v)` of §2, and
the edge of the strand `Φ(x, i)` that is again a state is the one with state
`f(i, v)`:

```text
(St)         state(Φ(I))  =  f(state(I)).
```

The edge `(0, c)` has the vertex state `(c, 0)`, and two edges `(0, c)`,
`(0, c′)` are coincident iff `c, c′` are left strongly coincident or equal.

### 4.2 The rank is the number of non-coincident letters: Theorem FC2

**Theorem FC2.** Let `σ ∈ PIP3`.

1. `cr(σ) ≥ max(ν_L, ν_R)`, and `ν_L ≤ 2`, `ν_R ≤ 2`.
2. If `σ` satisfies (F), then `cr(σ) = ν_L = ν_R ≤ 2`.

Imports: BBK Def. 4.1 and Remark 4.3; BD02 Theorem 1.

*Proof.* (a) `cr ≥ ν_L`. Let `c₁, …, c_ν` be letters no two of which are left
strongly coincident. The edges `(0, c_i)` are states over `0`, pairwise
non-coincident; Remark 4.3 at `q = 0` gives `cr ≥ ν`.

(b) Under (F), `cr ≤ ν_L`. By Remark 4.3 at `q = 0` there are `cr` states
`I₁, …, I_cr` over `0`, pairwise non-coincident. Let `I_i^{(k)}` be the edge
of `Φ^k(I_i)` whose state is `f^k(state(I_i))` (by (St)). The edges
`I_i^{(k)}` are pairwise non-coincident: `Φⁿ(I_i^{(k)})` is part of
`Φ^{n+k}(I_i)`, so a shared edge would make `I_i` and `I_j` coincident. By
Lemma 3(4) and (F), for `k` large every `I_i^{(k)}` has a vertex state,
`I_i^{(k)} = (0, c_i)`. Non-coincident edges are distinct, so the `c_i` are
distinct letters, pairwise not left strongly coincident. Hence `cr ≤ ν_L`.

(c) Reversal. The reflection `ϱ(x) = −x` maps the labelled edge `(x, i)` to
the labelled edge `(−x − e_i, i)` and strands to strands, with the order
reversed. It conjugates `Φ_σ` to `Φ_{σ^R}`: `Φ_σ(x, i)` runs from `Mx` to
`M(x + e_i)` with labels `σ(i)`, and `Φ_{σ^R}(−x − e_i, i)` runs from
`−M(x + e_i)` to `−Mx` with labels `σ(i)` reversed. It preserves shared
labelled edges, and since `Σ = ℤ³` for both substitutions it maps the
strands over a point `q ∈ V/Σ` to the strands over `−q`. So `ϱ` maps a
pairwise non-coincident family of strands over `q` for `σ` to such a family
over `−q` for `σ^R`, and conversely; the maximum in Def. 4.1 is over all
points, hence `cr(σ^R) = cr(σ)`. Moreover
`ν_L(σ^R) = ν_R(σ)`, since `(σ^R)ⁿ(a)` is `σⁿ(a)` reversed, and (F) is
reversal-invariant (Lemma 4(3)). Applying (a) to `σ^R` gives `cr ≥ ν_R`;
applying (b) to `σ^R` gives `cr ≤ ν_R` under (F).

(d) `χ_M` is irreducible and `β` is Pisot, so the non-Perron eigenvalues are
nonzero of modulus below one: `σ` and `σ^R` are of Pisot type, and by BD02
two of the three letters are left strongly coincident for each. So
`ν_L, ν_R ≤ 2`. ∎

*Two corrections to the route's first write-up, both applied above.*
(i) `cr ≥ ν_R` is not Remark 4.3 read literally: BBK's states exclude the end
point of an edge, so edges ending at a lattice point are not states over it.
Step (c) replaces that reading. (ii) "`Σ = Γ` for irreducible `A`" is one
sentence of BBK that defers to Barge–Kwapisz 2006; Lemma 6 replaces it.

*What is not shown.* `cr ≤ 2` is obtained on (F) only. The proof covers only
(F); it does not show that the bound fails elsewhere.

**Corollary E (equivalences on (F)).** For `σ ∈ PIP3` with (F) the following
are equivalent: (i) `σ` has no strict system, i.e. `C4(σ)`; (ii) `SC_L(σ)`;
(iii) `SC_R(σ)`; (iv) `cr(σ) = 1`; (v) the tiling flow has pure discrete
spectrum. If they fail, `cr(σ) = 2`.

*Proof.* (i) ⟺ (ii) is Theorem FC1. `ν_L = 1 ⟺ cr = 1 ⟺ ν_R = 1` is
Theorem FC2(2). (iv) ⟺ (v) is BBK Cor. 5.2. ∎

What `cr ≤ 2` on (F) says about the shape of a hypothetical strict system
there (only swap-symmetric ordered sinks) is recorded with the flat-system
statements of the [closure-attempt note](c4-closure-attempt-2026-11-16.md)
§6.2, not here.

**Corollary H (hardness on the (F) class).** If no `σ ∈ PIP3` has a strict
system, then every `σ ∈ PIP3` with (F) has `cr(σ) = 1`: pure discrete
spectrum, and strong coincidence of all letter pairs on both sides.

*Proof.* Corollary E. ∎

### 4.3 What Corollary H means for the C4 route

C4 follows from all-pairs strong coincidence (#138), and the reason for
attacking C4 separately was its extra hypothesis: only configurations with
bounded common-vertex gaps have to be excluded. The
[finite-domain note](c4-finite-domain-closure-2026-11-05.md) §4 put it as
"the only content of C4 beyond #138 is the bounded-gap slack". Theorem FC1
says that on the (F) class there is no slack: every pair of periodic rays has
bounded gaps, so the bounded-gap hypothesis carries no information there, and
C4 restricted to (F) *is* strong coincidence restricted to (F).

Three consequences, stated without more than they contain.

- A uniform proof of C4 must, on (F), derive strong coincidence of all pairs
  with no help from bounded gaps, and with it pure discrete spectrum
  (Corollary E). In the sources read, the corresponding conclusion on (F),
  that the self-replicating multiple tiling is a tiling, is obtained only
  with strong coincidence as a hypothesis (Minervino–Thuswaldner Thm 9.9),
  and pure discrete spectrum is obtained on special classes (for instance
  Barge 2016 Thm 3.13). By Corollary H, conditional on BBK Cor. 5.2 and on the imports of
  Theorem FC2, universal C4 is at least as strong as "pure discrete spectrum
  for every ternary irreducible Pisot substitution with (F)".
- Any leverage from bounded gaps can only come from substitutions with an
  interior periodic address. On the corpus every pair of periodic first
  letters of every non-(F) specimen has a relative state absorbed by an
  interior cycle (§9), so there the mechanism of FC1 is silent.
- Nothing here says that C4 is false or out of reach, and nothing is said
  about C4 off (F). On the corpus nothing changes: no strict system exists
  there by the finite-domain theorem `C4StandingCorpus`.

What remains on (F) is the single statement "`ν_L = 2` is impossible for
ternary irreducible Pisot substitutions with (F)". Theorem FC3 gives it for
odd determinant under one of two arithmetic conditions; it is open for
`det M` even and for `det M` odd with `tr M ≡ e₂(M)` and `dim H¹ ≥ 5`.

## 5. Lemma S and Theorem P: a parity refinement of Barge 2015 Thm 22

### 5.1 The substitution action on `H¹`

BD08 attach to a primitive aperiodic substitution a complex `K` with one edge
`e_a` per letter and one transition edge `e_{ab}` per legal two-letter word
`ab`, the subcomplex `S` of transition edges, and a map
`g_K: (K, S) → (K, S)` (their `g`; the subscript keeps it apart from the
first-letter map `g`) homotopic to the map `f_K` induced by `Φ`, with
`g_K(e_{ab}) = e_{g_R(a) g(b)}`. They show `Ω_σ ≅ lim←(K, f_K)` (their
Lemma 2) and `Ȟ¹(Ω_σ) ≅ lim→(H¹(K), g_K*)` (their Corollary 3). The
homeomorphism conjugates `Φ` with the shift (from `f_K ∘ p = p ∘ Φ`, with
`p: Ω_σ → K` their projection), so `Φ*` corresponds to the map
induced by `g_K*` on the direct limit; the source states the isomorphism and
not this equivariance, which is immediate. The morphism of the exact sequence
of the pair `(K, S)` induced by `g_K` gives, in the limit, an exact sequence
commuting with the induced maps,

```text
0 → G_0 → G_1 → G_2 → G_3 → 0,
G_1 = lim→(H¹(K,S), g_K*) ≅ lim→ Mᵗ,   G_2 = Ȟ¹(Ω_σ),
G_3 = lim→(H¹(S), g_K*) ≅ ℤ^l,         G_0 = lim→(H̃⁰(S), g_K*) ≅ ℤ^{k−1},
```

with `ER = ⋂ g_Kⁿ(S)` the eventual range, `k` its number of components and
`l` its number of independent cycles (B15 writes the same sequence as its
(4.1), with `k + 1` components).

**Lemma 7 (the substitution action).** Let `σ ∈ PIP3`.

1. `ER` consists of the edges `e_{ab}` with `ab` legal, `a` `g_R`-periodic
   and `b` `g`-periodic. `g_K` permutes them, and `g_K⁶` is the identity on
   `ER`.
2. `G_0 = 0`, i.e. `ER` is connected.
3. For every `n ≥ 1`,
   `charpoly(Φⁿ* | H¹(Ω_σ; ℚ)) = χ_{Mⁿ}(t) · c_n(t)`, where `c_n` is the
   characteristic polynomial of `(g_Kⁿ)*` on `H¹(ER; ℚ)`. It has degree `l`,
   its roots are roots of unity, and `c₆(t) = (t − 1)^l`. In particular
   `dim H¹(Ω_σ; ℚ) = 3 + l`.

*Proof.* (1) An edge of `g_Kⁿ(S)` has the form `e_{g_Rⁿ(a′) gⁿ(b′)}`, so edges
of `ER` have periodic end letters; conversely an edge with periodic end
letters is fixed by a power of `g_K`. On three letters the periodic parts of
`g_R` and `g` are permuted with orders in `{1, 2, 3}`, so `g_K⁶` fixes every
vertex of `ER`, hence every edge (an edge is determined by its ends). (2) The
generators of `G_0` are fixed by a power of the induced map (BD08, proof of
Theorem 4), `G_0 → G_1` is injective and equivariant, and on `G_1 ⊗ ℚ = ℚ³` the induced
map is `Mᵗ`, no power of which has the eigenvalue `1` (Lemma 1(3)). (3) With
`G_0 = 0` the sequence `0 → G_1 → G_2 → G_3 → 0` is exact and equivariant, so
the characteristic polynomial on `G_2 ⊗ ℚ` is the product of those on
`G_1 ⊗ ℚ` (namely `χ_M`) and on `G_3 ⊗ ℚ`. Since a power of `g_K` maps `S`
into `ER` and `g_K` is invertible on `ER`, `G_3 ⊗ ℚ ≅ H¹(ER; ℚ)` with the
action of `(g_K|ER)*`. Take `n`-th powers of the eigenvalues; use (1) for
`n = 6`. ∎

The formula `dim H¹ = 3 + l` is the one of the
[`dim H¹` census](c4-h1-census-2026-11-05.md).

### 5.2 Barge's factorisation at coincidence rank two

Let `σ ∈ PIP3` with `cr(σ) = 2`. Call `n ≥ 1` *admissible* if there is a legal
word `ba` with `g_Rⁿ(b) = b` and `gⁿ(a) = a`; `n = 6` is always admissible by
Lemma 7(1). The following are B15 as printed, for such an `n`.

- (B1) *Proper version* (B15 §4). The return words between occurrences of the
  seam `b.a` carry a proper primitive substitution `φ′` induced by `σⁿ`. Its
  tiling space is `Ω_σ` with the same flow, and its inflation is `Φⁿ`; the
  coincidence rank is that of `σ`, the dilation is `βⁿ`, of degree 3 and norm
  `(det M)ⁿ`. (That the inflation of `φ′` is `Φⁿ` is by construction; B15
  cites Durand and Barge–Diamond 2001 for the rewriting, which were not
  read.)
- (B2) *Stack substitution* (Thm 12, applicable because a proper substitution
  forces its border and `cr = 2` excludes pure discrete spectrum, B15
  Thm 4(5)). There are a proper substitution `φ′_s` and a factor map
  `q: Ω_{Φ′} → Ω_{Φ′_s}` (B15's `Σ`) that semi-conjugates the flows and `Φ′`
  with `Φ′_s`; `Ω_{Φ′_s}` is `Ω_{Φ′}/≈_s`, and `≈_s` is trivial on it.
- (B3) *Injectivity* (Prop. 19). `q*: H¹(Ω_{Φ′_s}; ℚ) → H¹(Ω_{Φ′}; ℚ)` is
  injective.
- (B4) *Ordered pairs* (Lemmas 13–14). `cr(Φ′_s) = 2` (used without comment in
  the proof of Thm 22; it follows from `g_max = g_s ∘ q` and Thm 5, since
  `cr(Φ′_s) = 1` with `≈_s` trivial would make `g_s` injective and `Ω/≈_s`
  the maximal equicontinuous factor of `Ω`). So every tiling of `Ω_{Φ′_s}`
  has a unique regionally proximal partner disjoint from it, and the
  substitution `ψ := (φ′_s)_op` on ordered pairs of overlapping tiles of a
  tiling and its partner has `Ω_ψ ≅ Ω_{Φ′_s}` by a homeomorphism conjugating
  flows and substitutions.
- (B5) *The involution* (Lemma 20). Exchanging the two entries is a
  fixed-point-free involution of the alphabet of `ψ` commuting with `ψ`, so
  in a suitable order the incidence matrix of `ψ` is `[[X, Y], [Y, X]]`,
  conjugate over `ℤ` to the block-triangular matrix
  `[[X + Y, Y], [0, X − Y]]` (B15, proof of Lemma 20; over `ℚ`, not over
  `ℤ` in general, it is conjugate to `diag(X + Y, X − Y)`). So its characteristic
  polynomial is `χ_{X+Y} · χ_{X−Y}`. `X + Y` is the incidence matrix of the
  substitution on unordered pairs, a tile substitution with dilation `βⁿ`.
- (B6) *Components* (proof of Thm 22). `ψ` has exactly two allowed bi-infinite
  periodic words, so the eventual range for `ψ` has at most two components:
  `G_0(ψ)` has dimension `ε ∈ {0, 1}`, and the induced map acts on it by `±1`.

Write `nz χ` for a characteristic polynomial with its factors `t` removed.

**Lemma S (signed overlap matrix).** Let `σ ∈ PIP3` with `cr(σ) = 2`, `n`
admissible, and `X, Y` as in (B5). Then `χ_{Mⁿ}` divides `χ_{X+Y}`, and with
`nz χ_{X+Y} = χ_{Mⁿ} · r`,

```text
r(t) · nz χ_{X−Y}(t)   divides   (t ∓ 1)^ε · c_n(t)        in ℤ[t].
```

In particular every nonzero eigenvalue of `X − Y` is a root of unity, and
`X − Y` has at most `l + ε` nonzero eigenvalues.

*Proof.* Apply the exact sequence of §5.1 to `ψ`. On `G_1(ψ) ⊗ ℚ`, the
eventual range of the transposed incidence matrix, the induced map has
characteristic polynomial `nz χ_{X+Y} · nz χ_{X−Y}` by (B5), and on
`G_0(ψ) ⊗ ℚ` it has `(t ∓ 1)^ε` by (B6). So the cokernel of
`G_0(ψ) → G_1(ψ)` is an invariant subspace of `H¹(Ω_ψ; ℚ)` on which the
substitution acts with characteristic polynomial
`nz χ_{X+Y} · nz χ_{X−Y} / (t ∓ 1)^ε`. By (B4), (B3) and (B2) there are
equivariant maps

```text
H¹(Ω_ψ; ℚ)  ≅  H¹(Ω_{Φ′_s}; ℚ)  ↪  H¹(Ω_{Φ′}; ℚ)  =  H¹(Ω_σ; ℚ)  with Φⁿ*,
```

and the characteristic polynomial of an invariant subspace divides that of
the space, which is `χ_{Mⁿ} · c_n` by Lemma 7(3). So
`nz χ_{X+Y} · nz χ_{X−Y}` divides `(t ∓ 1)^ε χ_{Mⁿ} c_n`. The lengths of the
pair tiles form a positive left eigenvector of `X + Y` for `βⁿ` (B5).
`χ_{Mⁿ}` is the minimal polynomial of `βⁿ`: it is
`(t − βⁿ)(t − λ₂ⁿ)(t − λ₃ⁿ)`, of degree 3, and `βⁿ` has degree 3 because
`ℚ(βⁿ)` is `ℚ` or `ℚ(β)` and `βⁿ` is not rational (its conjugates `λ₂ⁿ`,
`λ₃ⁿ` are smaller in modulus). So `χ_{Mⁿ}` divides
`χ_{X+Y}`, and since `χ_{Mⁿ}(0) ≠ 0` it divides `nz χ_{X+Y}`. Cancel it.
Divisibility of monic integer polynomials over `ℚ` is divisibility over
`ℤ`. ∎

Irreducibility enters three times: `G_0 = 0` for `σ`, `χ_{Mⁿ}` is the minimal
polynomial of `βⁿ`, and (through Lemma 7) the only eigenvalues of `Φ*` on
`H¹(Ω_σ)` besides the conjugates of `β` are roots of unity. For a reducible
substitution the other factors of `χ_M` leave room for `X − Y`.

**Theorem P (parity).** Let `σ ∈ PIP3` with `det M` odd. If `cr(σ) = 2`, then
`tr M ≡ e₂(M) (mod 2)` and `dim H¹(Ω_σ; ℚ) ≥ 5`.

Imports: B15 (the proper version of §4, whose rewriting references were not
read; Thm 4(5); Thm 5; Thm 12; Lemmas 13–14; Prop. 19; Lemma 20; sequence
(4.1) and the count of periodic words in the proof of Thm 22), BD08 Lemma 2,
Corollary 3 and Theorem 4, and the identification of the two coincidence
ranks (§1, **[Std]**). Label: derived from B15 as printed; re-derived by
three verifiers and once more for this note; not machine-checked.

*Proof.* Take `n = 6` in Lemma S: `c₆ = (t − 1)^l`. Write
`χ_{X+Y} = t^i χ_{M⁶} r` and `χ_{X−Y} = t^j q` with `q = nz χ_{X−Y}`. Since
`X − Y ≡ X + Y (mod 2)`, the two characteristic polynomials agree in `𝔽₂[t]`
(a bar denotes reduction mod 2):
`t^i χ̄_{M⁶} r̄ = t^j q̄`. The constant term of `χ_{M⁶}` is `−(det M)⁶`, odd,
so `χ̄_{M⁶}` is prime to `t` and divides `q̄`. By Lemma S, `q` divides
`(t ∓ 1)^ε (t − 1)^l`, so `q̄` divides `(t + 1)^{l+ε}`. Hence

```text
χ̄_{M⁶}(t) = (t + 1)³   in 𝔽₂[t],        and   l + ε ≥ 3.
```

The second statement gives `l ≥ 2`, i.e. `dim H¹ = 3 + l ≥ 5` (this is B15
Thm 22 for `d = 3`). The first says that every eigenvalue `μ` of `M mod 2` in
an algebraic closure of `𝔽₂` has `μ⁶ = 1`, i.e. `μ³ = 1`. Now
`χ̄_M = t³ + a t² + b t + 1` with `a ≡ tr M`, `b ≡ e₂(M)`. For
`(a, b) = (0, 0)` it is `(t + 1)(t² + t + 1)` and for `(1, 1)` it is
`(t + 1)³`: all roots are cube roots of unity. For `(1, 0)` and `(0, 1)` it
is `t³ + t² + 1`, resp. `t³ + t + 1`, irreducible over `𝔽₂` with roots of
order 7 in `𝔽₈`. So `χ̄_{M⁶} = (t + 1)³` iff `a = b`. ∎

*Remarks.* (1) The hypothesis `det M` odd is used once, to make `χ̄_{M⁶}`
prime to `t`; Lemma S itself has no parity hypothesis. (2) The theorem is a
necessary condition only: the parity `tr M ≡ e₂(M)` says nothing in the
other direction (it holds for Tribonacci, `tr = 1`, `e₂ = −1`). Also, the
condition `tr M ≢ e₂(M)` with `det M` odd says that `χ_M mod 2` is an
irreducible cubic, which already forces `χ_M` to be irreducible over `ℚ`;
so no reducible substitution lies in that parity class, and the reducible
controls of §9 cannot test it. (3) *Not pinned:* Lemma S for the
admissible `n < 6` gives further conditions,
`χ̄_{Mⁿ} | (t + 1)^ε c̄_n`. A scratch census found that they exclude a few
more corpus specimens than the parity alone and none on the (F) class; they
are recorded as a remark only. (4) Theorem P is a statement about the tiling
space of an actual substitution. For the plastic cubic `x³ − x − 1`
(`tr = 0`, `e₂ = −1`, `det = 1`) it says that a substitution of PIP3 with
this characteristic polynomial does not have `cr = 2`; it says nothing about
abstract child-closed systems.

*Relation to the degree-2 parity sieve.* The class "`det M` odd and
`tr M ≢ e₂(M) (mod 2)`" is the class on which `χ_M mod 2` is an irreducible
cubic. It is the arithmetic class of the repository's degree-2 parity sieve
(`kernel/psc/degree2_sieve.mojo`, Lean `no_strictSystem_deg2_odd`), which
there yields only a floor on the number of states of a strict system of
first defect degree 2.

## 6. The class theorem and the necessary conditions

**Theorem FC3 (class theorem).** Let `σ ∈ PIP3` satisfy (F) and one of:

- (a) `ν_L = 1` or `ν_R = 1`; in particular (a′) `g` or `g_R` is eventually
  constant;
- (b) `det M` is odd and `dim H¹(Ω_σ; ℚ) ≤ 4`;
- (c) `det M` is odd and `tr M ≢ e₂(M) (mod 2)`.

Then `cr(σ) = 1`: the tiling flow has pure discrete spectrum, all pairs of
letters are left and right strongly coincident, and `σ` has no strict system.

*Proof.* By Theorem FC2, `cr = ν_L = ν_R ≤ 2`. In case (a), `cr = 1`. In case
(b), `cr = 2` would give `dim H¹ ≥ 5` by B15 Thm 22 (`d = 3`; the norm of `β`
is `det M`). In case (c), `cr = 2` contradicts Theorem P. So `cr = 1`. Then
`ν_L = ν_R = 1` by Theorem FC2(1), the spectrum is pure discrete by BBK
Cor. 5.2, and there is no strict system by Theorem A(4). ∎

Imports: those of Theorem FC2; BBK Cor. 5.2; repository Theorem A(4); for
(b) B15 Thm 22 and for (c) Theorem P, both with the identification of the
two coincidence ranks (§1, **[Std]**).

Case (a) is prior art in part (§8). In case (a′) every pair has a witness
with empty prefixes (resp. suffixes) and Theorem A(3) alone excludes a
strict system, with or without (F). Clause (b) was reached by two of the six
routes
independently, by the zero fibre and by cohomology, where it was stated for
unit `σ` in the form "no interior periodic address and `dim H¹ ≤ 4`"; it is
stated once here, for odd determinant.

**Theorem N (necessary conditions).** Let `σ ∈ PIP3` have a strict system.

1. `cr(σ) ≥ 2`.
2. If `det M` is odd and (`dim H¹ ≤ 4` or `tr M ≢ e₂(M) (mod 2)`), then
   `cr(σ) ≥ 3`, (F) fails, and there is an inflation-periodic integer strand
   with the origin in the interior of an edge (an interior periodic
   address).

*Proof.* (1) By Theorem A(4) a first-letter pair of the system is not left
strongly coincident, so `ν_L ≥ 2`, and `cr ≥ ν_L` by Theorem FC2(1). (2)
`cr = 2` is excluded by B15 Thm 22, resp. Theorem P, so `cr ≥ 3`. Under (F),
`cr ≤ 2` (Theorem FC2(2)); so (F) fails, and by Lemma 4(1) there is an
`f`-periodic state `(e, v)` with `v ≠ 0`, `f^k(e, v) = (e, v)`. The edge
`(−v, e)` is in the interior of its own `Φ^k`-image, and the union of the
strands `Φ^{kn}(−v, e)` is a bi-infinite `Φ^k`-fixed integer strand with the
origin inside the edge `(−v, e)`. ∎

Imports: for (1), repository Theorem A(4) and BBK Def. 4.1, Remark 4.3 with
Lemma 6 (through Theorem FC2(1)); for (2) additionally the other imports of
Theorem FC2, and B15 Thm 22, resp. Theorem P, with the identification of the
two coincidence ranks (§1, **[Std]**).

*Remark (sharper form, extra import B15 Thm 4(2)).* With `cr ≥ 3`, the fibre
of `g_max` over the image of the origin contains three tilings pairwise
tile-disjoint at every level. That fibre is finite and `Φ`-invariant, so its
members are `Φ`-periodic integer strands. If all three had a vertex at the
origin, the three letters to its right would be distinct and two of them left
strongly coincident (BD02), giving a common tile at some level. So one of
the three is of interior type.

## 7. Forked partners for unit `σ` with `dim H¹ = 3`: Theorem Fork

Throughout this section `σ ∈ PIP3` is **unit** (`|det M| = 1`) with
**`dim H¹(Ω_σ; ℚ) = 3`**, i.e. `l = 0`. The maximal equicontinuous factor
is the torus `𝕋³ = ℝ³/ℤ³` and `g_max = h_φ: Ω_σ → 𝕋³` sends a tiling to the
class of a vertex of its strand (BBK Def. 3.1 with `Σ = ℤ³`, Lemma 6; for
unit `M` the inverse limit `𝕋_A` is the torus; that `h_φ` is the maximal
equicontinuous factor map is BBK Thm 5.1 with the **[Std]** fact of §1 that
this factor is determined by the continuous eigenfunctions).
`g_max(T − t) = g_max(T) + t r` up to the sign convention of the flow, and
`g_max ∘ Φ = M ∘ g_max`. The first-letter map `g` of §1 does not occur in
this section. The proof was left as a sketch by its route and reconstructed
by three verifiers; it is written out here. Steps resting on a standard fact
that was not checked against a source on disk are marked **[Std]**.

**Lemma 8 (strict components).** Suppose `σ` has a strict system. Then
there are `P ≥ 1` and a nonempty compact set `Z ⊆ Ω_σ × Ω_σ` such that:

- (Z1) `Z` is invariant under the diagonal flow and under `Φ^P × Φ^P`, and
  minimal for the diagonal flow;
- (Z2) for `(T, T′) ∈ Z` the common vertices of `T` and `T′` are relatively
  dense, and `Φⁿ(T)`, `Φⁿ(T′)` share no tile for any `n ≥ 0`;
- (Z3) `Z` contains a pair `(T₀, T₀′)` fixed by a power of `Φ^P × Φ^P` with a
  common vertex at the origin;
- (Z4) `g_max(T) = g_max(T′)` for every `(T, T′) ∈ Z`.

Such a `Z` is called a **strict component**.

*Proof.* Let `C′` be a sink strongly connected component of the child graph
of the system. The first factor of `σ(S)`, `S ∈ C′`, is again a state of
`C′`; this first-child map has a periodic point `S₀ = (u, v)`, of period
`p₀` say. The first factor of `σ^{p₀}(S₀)` is then `S₀`, so `u` and `v` are
prefixes of `σ^{p₀}(u)` and `σ^{p₀}(v)`, hence of the `σ^{p₀}`-fixed rays
through their first letters, and the pair of rays is the limit of
`σ^{p₀ n}(S₀)`: an infinite concatenation of states of `C′` (this is
Lemma F(c) of the cut-attractor note). The states that occur form a finite
strict system `C₁` for `σ^{p₀}` whose words are factors of the rays, hence
legal. Take a sink strongly connected component of the child graph of `C₁`,
of period `q`, and a cyclic class `C₀`; with `P = p₀ q` the child
substitution `Σ₀` of `σ^P` on the alphabet `C₀` is primitive. Give the letter
`S = (u, v)` the length `ℓ·p(u)`; this is a self-similar tile substitution
with dilation `β^P`. Let `Z̃` be its tiling space and `Z` its image under
the map that reads each block as a pair of patches. Both entries are tilings
of `Ω_σ` because their patches are factors of `σ^{Pn}(u)`, `σ^{Pn}(v)` with
`u`, `v` legal. (Z1): the tiling
space of a primitive substitution is flow-minimal and invariant under its
inflation, which the reading map turns into `Φ^P × Φ^P`. (Z2): block
boundaries are common vertices; by Lemma 1(1) a common vertex inside a block
would be a balanced cut, which irreducibility excludes; a shared tile has
two common end points, hence is a coincident block; so there is none at the
levels `Pn`, and a shared tile at level `n` persists at all higher levels.
(Z3): a primitive substitution has a bi-infinite word fixed by a power, with
the seam at the origin. (Z4): `T₀` and `T₀′` are inflation-periodic with a
vertex at the origin. The strand through the origin of `ℤ³` that carries the
letters of `T₀` is fixed by a power of `Φ` and has bounded `η_i`-coordinates
(the estimate of step (Fin) in §3, on both sides of the origin), so it
belongs to BBK's strand space and is the strand of `T₀`; likewise for
`T₀′`. Both are integer strands, so `g_max(T₀) = 0 = g_max(T₀′)`; then
`g_max(T₀ − t) = g_max(T₀′ − t)` for all `t`, and the flow orbit of
`(T₀, T₀′)` is dense in `Z`. ∎

(Z4) is the *alignment* of the two tracks. It rests on `Σ = ℤ³`, i.e. on
irreducibility (Lemma 6). It fails on the reducible strict controls
`10/102/211`, its reversal and `1/012/101` (scratch, §9: the two tracks lie
in different cosets of the return lattice). It does not fail on every
reducible strict control: for Thue–Morse the two tracks of the strict system
`{(01,10), (10,01)}` are obtained from each other by exchanging the two
letters, and by B15 Example 16 a tiling and its letter-exchanged copy are
regionally proximal, hence in one fibre of the maximal equicontinuous factor
map. The argument for Theorem Fork stops there at its hypotheses instead
(`det M = 0` and `l = 1`, the Morse–Thue example of BD08, so Lemma 9 is not available). Alignment was not
checked on the other controls of §9.

**Lemma 9 (classes are eigenfunction classes).** Let `Ω_s = Ω_σ/≈_s` be
Barge's quotient, `q: Ω_σ → Ω_s` the quotient map and `g_max = g_s ∘ q`. Then
`g_max*: H¹(𝕋³; ℤ) → Ȟ¹(Ω_σ; ℤ)` and `g_s*: H¹(𝕋³; ℤ) → Ȟ¹(Ω_s; ℤ)` are
isomorphisms: every map `Ω_s → S¹` is homotopic to `χ_u ∘ g_s` for a
character `χ_u` of `𝕋³` (by `Ȟ¹(X; ℤ) = [X, S¹]` **[Std]**).

*Proof.* (i) `G_0 = 0` (Lemma 7(2)) and `G_3 = 0` (`l = 0`), so
`Ȟ¹(Ω_σ; ℤ) ≅ G_1 = lim→(ℤ³, Mᵗ)`, and since `Mᵗ` is invertible over `ℤ`
this is `ℤ³`, generated by the three level-zero classes `w_a`: `w_a` is the
class of the map that winds once around the circle each time the origin
passes through a tile of type `a` (BD08, Theorem 4, with the definition of
`p: Ω → K`). Here both the unit hypothesis and `l = 0` are used. (ii)
**[Std]** The winding number of a circle-valued map along the flow is a
homomorphism `W: Ȟ¹(Ω_σ; ℤ) → ℝ`; `W(w_a) = r_a`, the frequency of `a` per
unit length. The `r_a` are ℚ-independent, so `W` is injective. (iii) By BBK
Thm 5.1 the eigenfunction `χ_u ∘ g_max`, `u ∈ ℤ³`, has eigenvalue `u·r`, so
`W(g_max*χ_u) = u·r = W(Σ u_a w_a)` and `g_max*χ_u = Σ u_a w_a`: `g_max*` is
an isomorphism. (iv) **[Std]** (Gottschalk–Hedlund) For a factor map
`q: X → Y` of minimal flows on compact metric spaces, `q*` is injective on
`Ȟ¹(·; ℤ)`: if `h: Y → S¹` and `h ∘ q = exp(2πi φ)` with `φ` continuous,
then the additive cocycle `c(y, t)` lifting `h(y − t)/h(y)` equals
`φ(x − t) − φ(x)` for `q(x) = y`, so it is bounded, hence a coboundary
`ψ(y − t) − ψ(y)`, and `h · exp(−2πi ψ)` is flow-invariant, hence constant.
(v) `g_max* = q* ∘ g_s*` is bijective and `q*` is injective, so `q*` and
`g_s*` are bijective. ∎

**Lemma 10 (no free symmetry of prime order over the factor).** Assume
`cr(σ) ≥ 2` (true when `σ` has a strict system, by Theorem N(1)). There is
no homeomorphism `ρ′` of `Ω_s` without fixed points, of prime order `p`,
with `g_s ∘ ρ′ = g_s`.

*Proof.* `Ω_s` is compact, connected, and of covering dimension at most
one: the flow does not have pure discrete spectrum, so by B15 Thm 12,
applied to the proper version of a power, `Ω_s` is homeomorphic to a
one-dimensional substitution tiling space, which is locally the product of a
Cantor set and an interval (B15 §2) and so has covering dimension one
**[Std]**. (Reconstructed, not checked against the source: that `≈_s` is the
same relation for `Φ` and for the proper version of `Φⁿ`. It is defined from
`g_max` and from stable equivalence, and by B15 Thm 4(3) tilings stably
equivalent along the multiples of `n` are stably equivalent.) **[Std]** The
quotient of `Ω_s` by the free action of
`ℤ/p` has dimension at most one, so its `Ȟ²(·; ℤ)` vanishes and
the complex line bundle associated with the character `ρ′ ↦ e^{2πi/p}` is
trivial: there is `z: Ω_s → S¹` with `z ∘ ρ′ = e^{2πi/p} z`. By Lemma 9
(with `Ȟ¹(X; ℤ) = [X, S¹]` **[Std]**),
`z = (χ_u ∘ g_s) · exp(2πi φ)` with `φ` continuous. Since `χ_u ∘ g_s` is
`ρ′`-invariant, `φ ∘ ρ′ − φ` takes values in `1/p + ℤ`, so it is a constant
`1/p + k` (`Ω_s` is connected). Summing over a `ρ′`-orbit gives
`0 = p(1/p + k) = 1 + pk`, which is impossible. ∎

The argument needs the index of the eigenfunction classes in
`Ȟ¹(Ω_s; ℤ)` to be prime to `p`; Lemma 9 gives index one, and that is where
this argument uses unimodularity and `l = 0`. Whether the conclusion of
Theorem Fork holds without them is not known here.

*Update 2026-11-16 (round 2).* The two sentences above are superseded; the
exact status is in §10(c). In short: for `dim H¹ = 3` the eigenfunction
classes have index one for every determinant (Lemma 9′ of the
[rank-two note](c4-rank-two-wall-2026-11-16.md), which is
Barge–Kellendonk–Schmieding 2012), so Lemma 10 needs `l = 0` and not
unimodularity; the extension of Theorem Fork itself to nonunit `σ` is
expected and not proved.

**Theorem Fork.** Let `σ ∈ PIP3` be unit with `dim H¹(Ω_σ; ℚ) = 3`, and let
`Z` be a strict component. Then for every `(T, T′) ∈ Z` there is `T″` with
`(T, T″) ∈ Z` such that `Φⁿ(T′)` and `Φⁿ(T″)` share no tile for any
`n ≥ 0`. Consequently:

1. the first projection `π₁: Z → Ω_σ` is injective at no point;
2. no point is a common vertex of `T`, `T′` and `T″`: the cut sets
   `V(T) ∩ V(T′)` and `V(T) ∩ V(T″)` are disjoint;
3. `σ` has an interior periodic address, i.e. (F) fails.

Imports: B15 Thm 4(1),(3),(4),(5), Thm 12; BBK Def. 3.1, Thm 4.2, Thm 5.1,
Cor. 5.2, and Def. 4.1, Remark 4.3 through Theorem N(1); BD08 Theorem 4;
BD02 Theorem 1; repository Theorem A(4) (through Theorem N(1)) and
Lemma F(c); Lemma 6; the identification of the two coincidence ranks (§1);
the **[Std]** facts of this section (its first paragraph, Lemmas 9 and 10).

*Proof.* *Step 1 (the quotient pair space).* `Z_s := (q × q)(Z)` is compact,
flow-invariant and minimal. It does not meet the diagonal: `T ≈_s T′` would
give `T − v ∼_s T′ − v` for a dense set of `v`, i.e. common tiles at the
origin at some level (B15 Thm 4(3)), against (Z2). By (Z4),
`g_s(a) = g_s(b)` for `(a, b) ∈ Z_s`. Both projections of `Z_s` are onto
`Ω_s` (minimality of `Ω_s`).

*Step 2 (the first projection of `Z_s` is not injective).* Suppose it were.
Then it is a homeomorphism onto `Ω_s`, and `ρ_s := π₂ ∘ π₁^{-1}` is a
continuous surjection of `Ω_s` commuting with the flow, without fixed
points, with `g_s ∘ ρ_s = g_s`. It maps each fibre of `g_s` onto itself
(it is onto and preserves fibres), and the fibres are finite of uniformly
bounded cardinality (B15 Thm 4(1); BBK Thm 4.2), so `ρ_s` is a bijection of
finite order. For each `j` the fixed-point set of
`ρ_s^j` is a flow-invariant closed set, hence empty or everything. If `N`
is the order of `ρ_s` and `p` a prime dividing `N`, then `ρ′ = ρ_s^{N/p}`
has order `p`, and none of its nontrivial powers has a fixed point. This
contradicts Lemma 10.

*Step 3 (lifting).* So there are `(T₁, T₁′), (T₂, T₂″) ∈ Z` with
`T₁ ≈_s T₂` and `T₁′ ≉_s T₂″`; all four lie in one fibre of `g_max`. The set
of `v` with `T₁′ − v ∼_s T₂″ − v` is open (B15 §3) and not dense, so there
is an open interval `J` on which `Φ^k(T₁′ − v)` and `Φ^k(T₂″ − v)` never
have the same tiles at the origin; the set of `v` with
`T₁ − v ∼_s T₂ − v` is open and dense, so there are `v₀ ∈ J` and `k₀` with
`Φ^{k₀}(T₁ − v₀)` and `Φ^{k₀}(T₂ − v₀)` having the same tiles at the
origin. Along a sequence `k_i → ∞` of multiples of `P` let

```text
Φ^{k_i}(T₁ − v₀) → S,   Φ^{k_i}(T₂ − v₀) → S₂,
Φ^{k_i}(T₁′ − v₀) → S′,  Φ^{k_i}(T₂″ − v₀) → S″.
```

The patch common to `Φ^{k₀}(T₁ − v₀)` and `Φ^{k₀}(T₂ − v₀)` at the origin
contains the origin in the interior of its support, and its inflations
exhaust the line, so `S₂ = S`. By (Z1), `(S, S′) ∈ Z` and `(S, S″) ∈ Z`.
For every `n ≥ 0`, `Φⁿ(S′)` and `Φⁿ(S″)` share no tile: they are the limits
of `Φ^{k_i+n}(T₁′ − v₀)` and `Φ^{k_i+n}(T₂″ − v₀)`, which share no tile
inside `β^{k_i+n}(J − v₀)`; and two tilings of one fibre of `g_max` whose
vertices are close have them equal (their strands have vertices differing
by elements of `ℤ³` in a bounded region; equivalently B15 Thm 4(4)), so a
shared tile of the limits would be a shared tile of the approximants.

*Step 4 (spreading).* Let `𝔉` be the set of `(T, T′) ∈ Z` for which a `T″`
as in the statement exists. It is nonempty (Step 3), invariant under the
flow, and a closed subset of `Z` (pass to a convergent subsequence of the
`T″`; tile-disjointness at each level survives the limit for the reason
just given, all the tilings involved lying in one fibre of `g_max`). By (Z1),
`𝔉 = Z`.

*Consequences.* (1) `T′ ≠ T″`. (2) At a common vertex of `T, T′, T″` the
three letters to the right would be pairwise distinct (two equal ones give
a shared tile), and by BD02 two of them are left strongly coincident, which
gives a shared tile at some level, against (Z2) or the fork. (3) Apply the
theorem to `(T₀, T₀′)` of (Z3). `g_max(T₀″) = g_max(T₀) = 0`, the fibre over
`0` is finite and `Φ`-invariant (`g_max ∘ Φ = M ∘ g_max`), so `T₀″` is
`Φ`-periodic with an integer strand. By (2) the origin, a common vertex of
`T₀` and `T₀′`, is not a vertex of `T₀″`. The edge of the strand of `T₀″` over the origin is
then a periodic state with `v ≠ 0` by (St). ∎

*What the theorem does and does not say.* It is a necessary condition on
strict components, and it is vacuous on every computed domain, since no
strict system of a PIP3 substitution is known. For this class it shows that
the unique-partner premise of the retired derived-substitution route
(cut-attractor note §7) is false, not merely unproved. The correct reading
is "for unit PIP3 with `dim H¹ = 3`, `π₁` is not injective"; whether `π₁`
is a covering map is open, and nothing is shown for `dim H¹ ≥ 4` or for
nonunit `σ`. The clause `cr ≥ 3` that the route also drew is not new: it is
Theorem N(2). The new content is the second partner inside `Z`, the
disjoint cut sets, and (3) with the interior strand realised as a partner.

## 8. What is prior art

| Statement | Status relative to main and the literature |
| --- | --- |
| The (F) class | Minervino–Thuswaldner Def. 9.3 / Prop. 9.4; on main it is the "no terminal leftmost cycle" class of Corollary LC5 (ledger 2026-10-05). The corpus count 1,794 and the cycle count 10,584 are the LC census. |
| Theorem FC1 | A short corollary of the catch-up mechanism of LC5 together with Propositions 2 and 3 of the cut-attractor note. It is stated nowhere on main, and no C4 note cites LC5; the use on prefix-aligned roots, which yields the strict system itself, is what is recorded here. |
| Lemma 6 | Theorem R on main. For unimodular Pisot substitutions it is Barge–Kwapisz 2006 Thm 12.1 (with Fact 12.2), proved there by a frequency argument of the same kind (their Lemma 12.4; Fact 12.2(ii) uses unimodularity); BBK p. 2220 assert it for irreducible Pisot matrices "by the argument in" that paper, without a locator. The Barge–Kwapisz text was read only during the audit of this note, after the proof of Lemma 6 was written. |
| "On (F), strong coincidence ⟺ pure discrete spectrum" | ⟸ needs no (F): on main it is Akiyama–Lee 2014 Cor. 4.5 (PDS/strong-coincidence gate; not re-read); here it is BBK Cor. 5.2 with Theorem FC2(1). ⟹: Minervino–Thuswaldner Thm 9.9 gives, from (F) and strong coincidence, that the self-replicating multiple tiling is a tiling; the passage from that tiling to pure discrete spectrum of the tiling flow is not in the parts read and was not checked for nonunit `σ`. In this note ⟹ is Corollary E (FC2 with BBK Cor. 5.2). Akiyama 2016 (Thm 3.2, Cor. 3.3: for the suspension tiling of a Pisot substitution, *multiple* strong coincidence of some level `n` is equivalent to overlap coincidence) is the closest statement of "strong coincidence ⟹ pure discrete spectrum" among the sources read; it was read only during the audit of this note and **not compared** with Corollary E: whether on (F) its hypothesis reduces to ordinary strong coincidence was not checked. |
| Theorem FC2, `cr = ν_L = ν_R ≤ 2` on (F) | Not found in the sources read, nor on main (Akiyama 2016 not compared, previous row). It replaces the strong-coincidence hypothesis of Minervino–Thuswaldner Thm 9.9, the one (F) criterion read, by a count. |
| The zero fibre as the set of periodic integer strands; interior members ⟺ interior periodic addresses | The correction in §6 of the cut-attractor note; Lemma F there is Sirvent–Solomyak 2002. |
| FC3(a) | Prior art in part. No strict system: Theorem A(4) for `ν_L = 1` and its mirror image for `ν_R = 1`; in sub-case (a′) already Theorem A(3), the endpoint-collapse stratum (3,012 corpus specimens, pinned in `test_c4_cut_attractor.mojo`; 1,284 of them with (F), §9). Spectrum: the tiling of Minervino–Thuswaldner Thm 9.9 (the step from that tiling to pure discrete spectrum was not checked for nonunit `σ`), and Barge 2016 Thm 3.13 for injective-initial / constant-final substitutions. |
| FC3(b), the exclusion of `cr = 2` for `dim H¹ ≤ 4` | B15 Thm 22; on main in the `dim H¹` census (2,136 specimens). New only in combination with FC2. |
| Theorem P | The parity statement is not in B15; it is a re-derivation of the proof of Thm 22 with the substitution action kept. The parity class itself is the one of the degree-2 parity sieve on main. |
| Theorem N | Part (1) is immediate from Theorem A and BBK. Part (2) with `dim H¹ ≤ 4` is implicit in the ledger entry of 2026-11-05 for unit specimens; the parity clause and "(F) fails" are new. |
| Theorem Fork | The obstruction "no unique partner" is consistent with retired route 5; `cr ≥ 3` is not new; the fork, the disjoint cut sets and the forced interior address are new. |

No novelty relative to the literature is claimed beyond "not found in the
sources read". No new corpus fact follows: every corpus specimen is already
covered by the finite-domain theorem `C4StandingCorpus`.

## 9. Work shown

### Assumptions and hypotheses

| Hypothesis | Where it is used | What fails without it |
| --- | --- | --- |
| `χ_M` irreducible | Lemma 1 (`ℓ` injective on `ℤ³`, the eigen-coordinates determine a lattice point, no root of unity); Lemma 6 (`Σ = Γ = ℤ³`, so the fibre over `0` is the set of integer strands and two tracks through one lattice point are aligned); BD02 needs nonzero eigenvalues; Lemma 7 (`G_0 = 0`); Lemma S (`χ_{Mⁿ}` minimal for `βⁿ`) | every reducible control of the table below |
| Pisot | `ρ < 1`: finiteness of states and of relative states (Lemma 3, FC1); BBK, BD02, B15 | the binary `00001/011` (conjugate `3 − √2 > 1`): there is no contraction, and Lemma 3 gives no finiteness |
| primitive (aperiodicity is automatic on PIP3, §1) | existence of the rays and of `Ω_σ`; all imports | the reducible control `1/012/1` is periodic |
| (F) | step (N) of FC1; step (b) of FC2 | 2,760 corpus specimens; `01/12/021` |
| `det M` odd | the reduction mod 2 in Theorem P; B15 Lemma 20 and Thm 22; FC3(b),(c); Theorem N(2) | the 1,926 corpus specimens with `det M = 2` |
| `det M = ±1` and `dim H¹ = 3` | Lemma 9 (integral cohomology `ℤ³`, eigenfunction classes of index one), hence Theorem Fork | the proof: Lemma 9 needs `Ȟ¹(Ω_σ; ℤ) = ℤ³` and index one. No member of PIP3 for which the conclusion fails is known here. The examples of Barge–Bruin–Jones–Sadun (`cr = 3` with minimal cohomology, norm divisible by 3) are reducible; they bound only what cohomology alone can give |
| three letters | `ν ≤ d − 1 = 2`; `g_K⁶ = id` on `ER` and the list of cubics over `𝔽₂` in Theorem P | — |

### Derivation / reduction

```text
FC1   =  equivariance (E) + common vertex ⟺ vertex state (C) + finiteness (Fin)
         + (F) ⟹ uniform N + Theorem A                       [no import]
FC2   =  BBK Def. 4.1, Remark 4.3 at q = 0 + Lemma 6 + state(Φ I) = f(state I)
         + reflection (cr, (F) reversal-invariant) + BD02
E, H  =  FC1 + FC2 + BBK Cor. 5.2
S     =  B15 (Thm 12, L. 13–14, Prop. 19, L. 20, (4.1)) + BD08 Thm 4 + Lemma 7
P     =  S at n = 6 + det odd + cubics over 𝔽₂
FC3   =  FC2 + (a) | B15 Thm 22 | P ;   N = Theorem A + FC2 + B15 Thm 22 | P
Fork  =  Lemma 8 (alignment) + Lemma 9 (H¹ = eigenfunction classes)
         + Lemma 10 (equivariant circle map) + B15 Thm 4, 12 + BD02
```

Every arrow is written out in §§2–7. The finite objects certified by the
regression are: the set of interior `f`-cycles of each corpus specimen
(complete by the box bound of Lemma 3(3), made explicit in the module's
Lemma B, with radii computed by outward rounding and pinned in the
regression, and by its Lemma W; both are recorded proofs in the module
docstring, not machine-checked); the set `R` of relative states of each
pair of periodic first letters; and six integers per specimen (`det M`,
`tr M`, `e₂(M)`, `dim H¹`, the numbers of periodic letters of `g`, `g_R`).

### Evidence and replay

```sh
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_geometric_f.mojo)
PYTHONPATH=tools python3 -m claim_governance.cli --root .
python3 tools/check_markdown_source.py
```

The regression takes about two minutes on one core (re-run for this note on
2026-11-16: exit 0). It ends with `require_contract`, not `require_claim`: no
ledger claim is registered. Workflow `.github/workflows/c4-geometric-f.yml`
(not yet run on GitHub). The numbers under the next three headings are
asserted by that test, in exact integer and `ℤ[β]` arithmetic, over the
4,554 specimens of `pip_corpus()`.

*(F) and interior cycles.*

- (F) holds on **1,794** specimens and is invariant under image reversal on
  all 4,554 (0 mismatches). The corpus has 348 distinct incidence matrices.
- There are 3,756 interior `f`-cycles with 12,828 states; the longest period
  is 13; 0 / 1 / 2 / 3 cycles occur on 1,794 / 1,860 / 804 / 96 specimens.
  The least interior period over the 2,760 specimens without (F) is
  `1:816 2:252 3:744 4:228 5:492 6:12 7:24 8:72 10:84 11:12 13:24`.
- Every state of every interior cycle replays `(M^k − I) v = p(P)` at an
  interior occurrence (Lemma 4(1)); a failed replay raises.
- Lemma 5(2): the number of terminal leftmost cycles equals
  `2 Σ gcd(|C|, |G|)` on every specimen; 10,584 in all, on 2,760 specimens,
  longest 39, none exactly on the 1,794 (F) specimens. The comparison runs
  `psc.leftmost_chain` on the leftmost closure of the box start states, and
  on the literal box graph for every 97th specimen (47) and the four fixtures that fail (F).
- Counter-calibration: with half the certified radii strictly fewer cycles
  are found and more than 1,794 of the halved boxes hold no cycle. Such a
  search returns no verdict: `interior_cycles_in_box` returns a `BoxSearch`
  without `holds`, and only `decide_geometric_f` and
  `decide_geometric_f_with`, which take the box from `stable_radii`, return
  (F). This calibrates the halved box only.
- The certified radii are pinned: `[2,3,4]`, `[4,3,3]`, `[4,5,3]`,
  `[26,15,16]`, `[18,15,17]` on Tribonacci, `01/12/021`, `1/12/022`,
  `1/012/010`, `1/22/012` (each with a complex conjugate pair) and `[4,5,3]`
  on the totally real `1/02/202`; the sum of the three radii is 8,562 over the 348
  incidence matrices and 99,078 over the 4,554 specimens. These pins, not
  the cycle pins, guard the bound of Lemma B.

*Relative states (the content of Theorem FC1).*

- On the (F) specimens there are 1,956 pairs of distinct periodic first
  letters with 97,992 relative states in all; **every one reaches a vertex
  state** (0 absorbed). The maximal transient `N₀` is 51 `f`-steps, on 24
  pairs, and no pair has transient 38. The full distribution of `N₀` is
  `2:36 3:252 4:300 5:342 6:54 7:174 8:126 9:12 10:48 11:96 12:6 13:24 15:66
  16:102 18:30 19:24 20:24 21:54 22:18 31:72 35:72 51:24`; all 22 bins are
  asserted.
- On the other specimens there are 2,790 such pairs, and each of them has a
  relative state absorbed by an interior cycle.
- Fixtures: `1/2/02` (three pairs of period 3, 11 relative states each, equal
  to the set read off 3,000-letter prefixes, `N₀ = 7`; `M⁹` maps the first 60
  vertices of each ray to common vertices and `M⁶` does not); `1/012/100`,
  pair `(0, 1)` of period 2 (240 relative states, `N₀ = 51`).

*Arithmetic classes (the hypotheses of Theorems P and FC3; counts only).*

- 2,628 specimens have odd determinant; 2,136 of them have `dim H¹ ≤ 4`,
  1,344 have `tr M ≢ e₂(M)`, 2,352 have at least one of the two.
- Of the 1,794 (F) specimens, 1,284 have an endpoint map with fewer than two
  periodic letters (clause (a′)). Of the other 510: 84 satisfy (b), 120
  satisfy (c), 156 satisfy (b) or (c), and 354 satisfy neither (174 with
  `det M = 2`; 180 with odd determinant, `tr M ≡ e₂(M)` and `dim H¹ ≥ 5`).
  So the hypotheses of Theorem FC3 hold, without any coincidence search, on
  1,284 + 156 = 1,440 corpus specimens.
- Fixtures: Tribonacci `01/02/0` (`det 1`, `tr 1`, `e₂ −1`, `dim H¹ 3`, one
  periodic first letter); `01/12/021` (`det 1`, `tr 3`, `e₂ 2`, `dim H¹ 4`).

These are counts of classes. The test certifies no coincidence rank, no
strong coincidence and no spectrum, and on the corpus the conclusions of
FC3 are in any case known by other means (`C4StandingCorpus`).

*Withdrawn figure.* The route's "maximal transient 38" came from reading
relative states off 3,000-letter ray prefixes, which gives a lower bound
only. The exact value over the complete set `R` is 51;
`test_a_ray_prefix_is_not_the_set_of_relative_states` pins the difference
on `1/012/100` (a 3,000-letter prefix shows 60 of the 240 relative states
and transient 36). The existence statement of FC1 is unaffected; 38 must not
be used as a uniform `N₀`.

*Exploratory scratch observations (not replayable from the repository).*

- Six members of the non-trivial part of the FC3 class outside the corpus
  were named by the verifiers: `102/20/1200`, `20/001/0201`, `2120/0/012`,
  `0210/2021/210`, `200120/2/0201`, `01/1210/02101`. One scratch run of the
  canonical module on 2026-11-16 reproduced for each: PIP3, (F), odd
  determinant, `dim H¹ ≤ 4`, at least two periodic letters on both sides. They are
  not pinned by a regression. Whether the non-trivial part of the class is
  infinite, beyond powers and reversals, is open.
- Scratch Python (verifiers): seeded samples of PIP3 substitutions with
  images of length up to 6 found no member of the FC3 class lacking a
  strong-coincidence witness; an overlap search gave coincidence rank 1 on
  every corpus specimen; the refinement of Remark (3) after Theorem P
  excluded `cr = 2` on a few more odd-determinant corpus specimens than the
  2,352 above; for BBK Example 5.3 (reducible, `cr = 2`) the six-letter
  substitution has, with respect to its sheet-exchange involution,
  `χ_{X−Y} = (t − 1)(t² − 4t + 1)`, so the conclusion of Lemma S fails for
  these matrices (B15's ordered-pair substitution was not constructed, and
  the hypotheses of Lemma S are not met). None of this is evidence of
  record.
- While this note was written, steps (E), (C) and (N) of Theorem FC1 were
  re-checked by a separate scratch script working on words alone with exact
  integer arithmetic: on `1/2/02` (two pairs) and `1/012/100` the
  equivariance `s(M^m y) = f^m(s(y))` held at every one of several thousand
  vertices of 4,000- and 6,000-letter prefixes, with the same 11 relative
  states and `N₀ = 7` for `1/2/02`. It adds nothing to the pinned regression.
- The scratch statements about the reducible controls in the next table are
  marked there.

### Negative controls

Where each argument stops on each control that has a strict system. "Pinned"
refers to a Mojo regression on disk; "scratch" to the attempt's exploratory
Python.

| Control | Data | First hypothesis that fails |
| --- | --- | --- |
| Thue–Morse `01/10` | two letters, `χ = x(x − 2)`; strict `{(01,10), (10,01)}` | Not PIP3 (`decide_geometric_f` raises, pinned). `ℓ = (1, 1)` is not injective on `ℤ²`; the eigenvalue `0` is outside Pisot type and no pair is strongly coincident, so `ν_L = 2 = d` and FC2 stops at BD02; `det M = 0` is even (Theorem P); `l = 1` (Theorem Fork). FC1's mechanism is not contradicted: every even index is an equal-Parikh cut, and FC1 *predicts* a strict system when a periodic pair is not coincident. |
| `10/102/211` and reversal `01/201/112` | `χ = (x − 1)(x² − 2x − 2)`, `det M = −2`; 4-state strict system (pinned in `test_c4_cut_attractor.mojo`) | Refused as non-PIP3 (pinned). `ℓ·(2, 0, −1) = 0` (cut-attractor note): Lemma 1 fails, and the eigenvalue `1` is not contracted, so Lemma 3 fails. Lemma 6 fails (ℚ-dependent frequencies); scratch: the return lengths have index 3 and the two tracks of the strict pair lie in different cosets, so (Z4) fails. Even determinant (Theorem P); nonunit (Theorem Fork). Scratch: its common-vertex gaps are bounded although interior cycles exist in the position module, so the *conclusion* of FC1 can hold where its hypotheses do not. |
| `1/012/1` | `χ = x(x − 2)(x + 1)`, `det M = 0`; 4-state strict system (pinned in `test_c4_quotient_spectrum.mojo`) | Translation-periodic (the `σ²`-fixed word is `(1012)^∞`), so outside every import; singular and reducible. Scratch annotation, corrected: periodic, tile/return quotient `ℤ/3` (an earlier "`ℤ/2`" was wrong). |
| `1/012/101` | `χ = (x + 1)(x² − 2x − 1)`, `det M = 1`; 3 states under `σ²`, 6 under `σ` (pinned in `test_c4_reducible_pisot_controls.mojo`) | Reducible: Lemma 1 fails and the eigenvalue `−1` is not contracted. It is unit with odd determinant and (scratch) `dim H¹ = 2`, the degree of its inflation, so the arithmetic hypotheses of FC3(b) and Theorem N(2) are met, and so is the analogue of the cohomological hypothesis of Theorem Fork (not `dim H¹ = 3` itself). What fails is irreducibility: in Lemma 6 and (Z4), and in Lemma 7(2) (scratch, recomputed for the audit: `ER = {e_10, e_21}` has two components exchanged by `g_K`, so `G_0 ≠ 0`; this removes the eigenvalue `−1` of `Mᵗ`, and `Φ*` acts on `H¹` with characteristic polynomial `x² − 2x − 1`, so no root of unity occurs in `H¹`). Lemma S is not tested by this control: with the scratch value `dim H¹ = 2 < 3`, B15 Thm 22 (degree 2, norm `−1`) gives `cr ≠ 2`. Scratch: the return lengths have index 2 and the letters `0`, `1` lie in different cosets, so the strict pair is not in one fibre and its strict system does not give `cr ≥ 2`. This is the control showing that "a strict system gives two non-coincident strands in one fibre" (Theorem N(1)) needs irreducibility. |
| `012/120/201` | `χ = x²(x − 3)`; strict system (pinned in `test_c4_cut_attractor.mojo`) | Refused (pinned). Dilation of degree one; no pair is strongly coincident (the three images differ at every position), so `ν = 3` and BD02's conclusion fails; singular. |
| `01/2/120` | `χ = x²(x − 2)`; 20-state strict system (pinned in `test_c4_quotient_spectrum.mojo`; ledger 2026-11-06) | Singular, dilation `2` of degree one; outside every hypothesis. |
| C-D1 `011/120/2012` | `χ = (x − 1)(x² − 3x − 1)`, `det M = −1`; one closed 18-state system for `(X₀, X₁)` and `(X₀, X₂)` (pinned in `test_c4_reducible_pisot_controls.mojo`) | Reducible with eigenvalue `1`: Lemma 1 fails, the eigenvalue-one direction is not contracted (Lemma 3), the frequencies are ℚ-dependent (Lemma 6), and the hypothesis of BD02 fails. Unit with odd determinant; `tr M ≡ e₂(M)`, as for every cubic with a rational root and odd constant term (Remark (2) after Theorem P). Its `dim H¹` is 3 (`h1_profile`, pinned in `test_arithmetic_profile_fixtures` of `test_c4_geometric_f.mojo`), so with `det M = −1` the arithmetic hypotheses of FC3(b), Theorem N(2) and Theorem Fork (unit, `dim H¹ = 3`) are met literally; what fails is irreducibility, and `fc3_profile` refuses it (pinned). |
| C-D2 `010/1222/2012` | `χ = (x − 1)(x² − 4x + 1)`, `det M = 1`; 21 states for `(X₀, X₁)` and 23 for `(X₁, X₂)` (pinned, same test) | As C-D1, except that its `dim H¹` is not computed in the repository. |

Controls without a strict system, bounding the statements from the other
side:

- `01/12/021` (PIP3, unit) is not (F): the `f`-fixed state `(2; (−1, 0, 1))`
  with `(M − I) v = e₀` is pinned, re-derived from the word, and its pair
  `(0, 1)` has 19 relative states of which 2 are absorbed. All its pairs are
  strongly coincident (`C4StandingCorpus`). So "interior periodic address ⟹
  strict system" is false, FC1 is a sufficient condition only, and the (F)
  class is not the class of substitutions without a strict system.
- `1/02/002` and `01/20/200` are not (F) either (scratch: interior cycles of
  period 3 and 4).
- Tribonacci satisfies (F) and has a constant first-letter map: clause (a′).
- The non-Pisot binary `00001/011` is outside every statement (Lemma 3).
- The abstract plastic-cubic degree-five survivor is not a substitution;
  Theorem P concerns tiling spaces (Remark (4) after it).

*Refusals (fail closed, refuse to conclude).* `decide_geometric_f` raises on
non-PIP3 input, on an uncertifiable radius and on a state cap; `OrbitMemo`
raises if an orbit closes on a cycle the verdict did not certify; a point
that is not a state has no image. `fc3_profile` raises on non-PIP3 input
(pinned on `011/120/2012`). The PIP3 gate is exercised arm by arm, each
refusal matched on its message: singular `1/012/1`, primitive irreducible
non-Pisot `1/2/001`, primitive reducible `011/120/2012`, and an image of
length 7 (not an arm of PIP3 membership: `0⁵1/120⁵/0⁶` is PIP3, and the module is certified only for image lengths at most six, so it is refused, not decided). All but the radius refusals are
exercised, in `test_refusals` and, for `fc3_profile`, in `test_arithmetic_profile_fixtures`; the radius refusals of `stable_radii` (an
enclosure not separated from zero, a contraction not certified below 1, a
radius beyond `RADIUS_CAP`) are reached by no test.

*Stronger variants that failed, kept on record.* "Maximal transient 38"
(withdrawn above). "`cr ≥ ν_R` is BBK Remark 4.3" (false as a literal
reading; replaced by reversal). "`cr ≤ 2` is provable only on (F)" (not
shown; the proof covers only (F)). "`π₁` is not a covering map" (not shown;
only non-injectivity). "The beta-substitution family `0→0^a 1, 1→0^b 2,
2→0` is new scope for FC3(b)" (it is in the mirror Barge class and the
endpoint-collapse stratum). "Theorem FC3 gives 1,440 new specimens" (1,284
of them are clause (a′), prior art; the other 156 are already in
`C4StandingCorpus`).

### Non-claims / remaining gaps

- **Universal C4.** Open. By Corollary H, conditional on BBK Cor. 5.2 and on the imports of
  Theorem FC2, it is at least as strong as pure discrete spectrum on the (F)
  class.
- **Strong coincidence or pure discrete spectrum on (F) outside Theorem
  FC3.** Open: `det M` even (174 corpus specimens of the 510 with at least two
  periodic letters on both sides), and `det M` odd with `tr M ≡ e₂(M)` and
  `dim H¹ ≥ 5` (180).
- **`cr ≤ 2` off (F).** Not asserted; nothing is known here about the
  coincidence rank of a substitution with an interior periodic address.
- **Even determinant.** Nothing beyond FC1 and FC2. Theorem P, FC3(b),(c)
  and Theorem N(2) say nothing for `det M = 2`.
- **Infinitude of the non-trivial part of the FC3 class.** Not shown.
- **C4 off (F).** No statement. In particular it is not claimed that bounded
  gaps fail off (F).
- **Larger alphabets.** FC1 and the equality `cr = ν_L = ν_R` do not use
  `d = 3` in their proofs, but no statement is recorded or replayed for
  `d > 3`.
- **Status of the proofs.** FC1 is elementary; like the others it is not
  machine-checked and awaits independent human review. FC2, P, FC3, N and
  Fork are conditional on the imports of §1 as printed; the proofs of B15
  Thm 4 were not followed into the papers it cites; the equivariance used in
  Lemma S is read off B15 and BD08 and not machine-checked, and the
  rewriting to a proper version rests on references of B15 that were not
  read; Theorems P, FC3(b),(c) and N(2) use the identification of the two
  coincidence ranks, which rests on one **[Std]** fact; Theorem Fork
  additionally uses the other **[Std]** facts; none of them was checked
  against a source on disk. Barge–Kwapisz 2006 was not obtained when the
  proofs were written and no proof uses it; the parts read during the audit
  are listed in the literature gate. Akiyama 2016 was not compared with
  Corollary E (§8).
- **No certification.** The regression counts classes; it decides no
  coincidence rank and no spectrum. C4, #138, #139, #84, G1 and PSC are
  unchanged, and no ledger claim is registered.

## 10. Update 2026-11-16 (round 2)

Added on 2026-11-16, after the second round of the attempt. The record of
that round for coincidence rank two is the
[rank-two note](c4-rank-two-wall-2026-11-16.md), with its gate
[`c4-rank-two-wall-stop-go-2026-11-16.md`](c4-rank-two-wall-stop-go-2026-11-16.md).
Nothing in §§1–9 was edited, except for two dated paragraphs (after the
status paragraph and in §7) that point here. Each item names the round-1
sentences it supersedes, verbatim. Status of this section: Universal C4
remains open; nothing changes a governed claim status (C4, #138, #139, #84,
G1 and PSC are unchanged); no ledger claim is registered; independent human
review pending.

### (a) Theorem FC1 is machine-checked

Superseded sentences: in the status paragraph, "none is machine-checked, and
independent human review is pending for all of them, FC1 included"; in §9,
"FC1 is elementary; like the others it is not machine-checked and awaits
independent human review". Human review is still pending. What changed is
the first half, for Theorem FC1 only.

*Abstract form* (`proof/PscVerif/PscVerif/GeometricFInclusion.lean` and
`GeometricFStrict.lean`, namespace `Psc.GeometricF`; axioms `propext`,
`Classical.choice`, `Quot.sound`). For a substitution `s` on a finite
alphabet and an additive length functional `L` the hypotheses are:

- (H1) `LengthData s L β`: `β > 0`, `L(Mv) = β L(v)`, `L` positive on
  letters;
- (H1′) `1 < β`;
- (H2) `ContractionData s L ν ρ`: a subadditive even `ν` with
  `ν(Mv) ≤ ρ ν(v)`, `0 ≤ ρ < 1`, and `{v : |L v| ≤ a, ν v ≤ b}` finite for
  all `a, b` (this is where Lemma 1(2) and the Pisot bound enter);
- (H3) `PropertyF s L`: no `f`-periodic state has `v ≠ 0`.

Under them: items 1 and 2 of Theorem FC1 are `fc1_inclusion_gap` (from
(Fin) and (F) on the relative states) and `fc1_inclusion_gap_of_contraction`
((H1), (H2), (H3)); item 3 is `fc1_strictSystem` ((H1), (H1′), two
`σ^m`-fixed words, (Fin), (F) on `R`, no witness for the first letters); the
equivalences are `fc1_equivalence` and `fc1_equivalence_of_contraction`
((H1), (H1′), (H2), (H3)). The direction of the "Powers" paragraph that the
proof uses is `strictSystem_of_power` (nonerasing `σ`). Lemma 2 is
`step_power_iff`; steps (E), (C), (Fin) are `relState_stepN`,
`relState_vertex_iff`, `relStates_finite_of_contraction`; Lemma 3(1), (4)
are `stepN_bound`, `reaches_vertex_of_propertyF`,
`propertyF_of_reaches_vertex`. Non-vacuity: every hypothesis holds on
Thue–Morse and the three statements of the equivalence are true there
(`tm_fc1`). Negative controls: the reducible strict controls admit no
contraction data (`carrier_not_contractionData`,
`reducible_controls_not_contractionData`).

*On the standing class* (`proof/PscVerif/PscVerif/GeometricFPisot.lean`,
namespace `Psc.GeometricFPisot`; same axioms). The abstract hypotheses are
derived from the spectral hypotheses in the forms used on main:

- (P) primitivity, `∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c`;
- (I) `Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly`;
- (E) a positive left eigen-row, `∀ a, 0 < ℓ a` and
  `ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ`;
- (R) the Pisot hypothesis in root form: every complex root `z ≠ β` of
  `χ_M` has `‖z‖ < 1`;
- (F) `PropertyF s (lenHom ℓ)`.

`exists_contractionData_of_pisot` gives (H2) from (I), (E), (R);
`Psc.BPrimeCore.one_lt_perron`, already on main, gives (H1′) from (P) on at
least two letters. Then:

- `fc1_equivalence_of_primitive_pisot` (any finite alphabet with at least
  two letters) and **`fc1_pip3`** (three letters): under (P), (I), (E), (R)
  and (F), `σ` has a strict system iff some pair of distinct `g`-periodic
  letters has no left strong-coincidence witness, iff left strong
  coincidence fails for some pair of distinct letters;
- `fc1_inclusion_gap_of_pisot` ((I), (E), `β > 0`, (R), (F)) and
  `fc1_inclusion_gap_of_primitive_pisot`: items 1 and 2;
- `fc1_strictSystem_of_pisot` ((I), (E), `β > 1`, (R), (F)): item 3;
- `fc1_equivalence_of_isPisot` and `fc1_equivalence_of_pisot_root`: the
  equivalence with the Pisot hypothesis in the two other forms used on main
  (`Psc.BPrime.IsPisot β`; the form of the sieve theorems);
- `periodic_bound`, `periodicStates_finite`: Lemma 3(1), (3) in abstract
  form.

So on the standing class property (F) is the only hypothesis of Theorem FC1
that is not a hypothesis of the class itself.

*What is not machine-checked.* No three-letter substitution is shown in Lean
to satisfy `PropertyF`: Tribonacci satisfies every hypothesis except (F)
there (`trib_fc1_hypotheses`), and the one complete instance is Fibonacci,
on two letters (`fib_propertyF`, `fib_fc1_hypotheses`, `fib_fc1`), where the
three statements of the equivalence are all false. The exact decision of
(F) on the corpus remains the Mojo regression of §9. Not formalised:
Lemma 1(1), (3); the explicit bound on `N₀`; Lemma 4 ((F) for powers and for
the reversal; interior periodic addresses); Lemma 5; the converse of the
"Powers" paragraph; Theorems FC2, P, FC3, N and Fork. The Lean statements
deviate from the text in presentation only (any finite alphabet; `f` and
the relative states as relations with proved existence and uniqueness; `ν`
a sum over the contracted eigen-coordinates; injectivity of `ℓ` is not
assumed), as their module docstrings list.

*Evidence.* An incremental build and a module-restricted `#print axioms`
audit on 2026-11-16 (exit 0); the isolated checker `tools/check_lean.sh`
was not run in this session, and hosted CI has not run. Replay:

```sh
(cd proof/PscVerif && lake build PscVerif.GeometricFPisot)
```

Theorem FC1 is an equivalence. Its formalisation excludes no strict system
and leaves universal C4 where it was.

### (b) Theorem FC3 extends to "(F) and `dim H¹ = 3`", for every determinant

**Corollary FC3+** (rank-two note, §8). If `σ ∈ PIP3` satisfies (F) and
`dim H¹(Ω_σ; ℚ) = 3`, then `cr(σ) = 1`: pure discrete spectrum, strong
coincidence of all pairs on both sides, and no strict system. For odd
determinant this is clause (b) of Theorem FC3; the new case is even
determinant. It follows from Theorem FC2 and **Theorem H3** of the rank-two
note (`dim H¹ = 3` excludes `cr = 2` for every determinant). Correspondingly
**Corollary N+** extends Theorem N(2): a strict system with `dim H¹ = 3`
forces `cr ≥ 3` and the failure of (F), for every determinant. Both are
recorded proofs, conditional on the imports listed in the rank-two note
(Barge 2015 as printed; Barge–Kellendonk–Schmieding 2012, Corollary 3 and
Theorem 5; Baker–Barge–Kwapisz; standard facts that were not read), not
machine-checked, independent human review pending.

Also in the rank-two note: **Lemma S+** sharpens Lemma S (in its notation
`ε = 1`, the sign is `+`, and the factor `t − 1` sits in `X − Y`), and
**Theorem P+** extends the parity count of Theorem P to every determinant
(`cr = 2` forces `dim H¹ ≥ 3 + |d₂ − 1|`, `d₂ = 3 − ord_t(χ_M mod 2)`, and
a divisor condition at every admissible `n`). For even determinant its
dimension bound is contained in Theorem H3, and its divisor condition is
not implemented.

Superseded sentences:

- §4.3: "Theorem FC3 gives it for odd determinant under one of two
  arithmetic conditions; it is open for `det M` even and for `det M` odd
  with `tr M ≡ e₂(M)` and `dim H¹ ≥ 5`."
- §5, Remark (1) after Theorem P, as far as it suggests that only odd
  determinant can be treated: "The hypothesis `det M` odd is used once, to
  make `χ̄_{M⁶}` prime to `t`; Lemma S itself has no parity hypothesis."
  The sentence is correct; Theorem P+ is what Lemma S gives without that
  hypothesis.
- §9, Non-claims: "Open: `det M` even (174 corpus specimens of the 510 with
  at least two periodic letters on both sides), and `det M` odd with
  `tr M ≡ e₂(M)` and `dim H¹ ≥ 5` (180)."
- §9, Non-claims: "**Even determinant.** Nothing beyond FC1 and FC2.
  Theorem P, FC3(b),(c) and Theorem N(2) say nothing for `det M = 2`."

As they now stand: on (F), "`ν_L = 2` is impossible" is open for `det M`
even with `dim H¹ ≥ 4`, and for `det M` odd with `tr M ≡ e₂(M)` and
`dim H¹ ≥ 5`. Pinned by the extended regression
`kernel/tests/test_c4_geometric_f.mojo` (class counts, not open cases): of
the 174 corpus specimens with (F), `det M = 2` and two periodic letters on
both sides, 42 have `dim H¹ = 3` and 132 do not (72 with `d₂ = 1`; 60 with
`d₂ = 2` and `dim H¹ = 5`); with the 156 odd ones, 198 of the 510 meet the
hypotheses of Theorem FC3 or Corollary FC3+ and 312 = 180 + 132 do not.
Over the corpus, (F) and `dim H¹ = 3` hold on 1,350 = 1,116 + 234
specimens; of the 234 with even determinant, 192 fall under clause (a′).
No new corpus fact follows: every corpus specimen is covered by
`C4StandingCorpus`.

### (c) Lemma 9, Lemma 10 and unimodularity; Theorem Fork without unit

Superseded sentences:

- §7, after Lemma 10: "The argument needs the index of the eigenfunction
  classes in `Ȟ¹(Ω_s; ℤ)` to be prime to `p`; Lemma 9 gives index one, and
  that is where this argument uses unimodularity and `l = 0`. Whether the
  conclusion of Theorem Fork holds without them is not known here."
- §7, proof of Lemma 9: "Here both the unit hypothesis and `l = 0` are
  used." This is true of that proof, not of the statement.
- §7, after Theorem Fork: "nothing is shown for `dim H¹ ≥ 4` or for nonunit
  `σ`."
- §9, table of hypotheses, row "`det M = ±1` and `dim H¹ = 3`": "the proof:
  Lemma 9 needs `Ȟ¹(Ω_σ; ℤ) = ℤ³` and index one."

The exact status, with locators in the rank-two note:

1. **Lemma 9′ (§8).** For `σ ∈ PIP3` with `dim H¹ = 3` and every
   determinant, every class of `Ȟ¹(Ω_σ; ℤ)` is the class of a continuous
   eigenfunction, and when `cr ≥ 2` the same holds on Barge's quotient
   `Ω_s`. The index is one; the hypothesis that matters is `l = 0`, not
   `|det M| = 1`. This is not new: it follows from
   Barge–Kellendonk–Schmieding 2012 (Corollary 3: `π*` is injective in
   degree one; Theorem 5: its cokernel is torsion free) once the ranks
   agree. That source was not found in round 1.
2. **Lemma 10** therefore holds for every `σ ∈ PIP3` with `dim H¹ = 3` and
   `cr ≥ 2`; its proof is unchanged, with Lemma 9′ in place of Lemma 9.
3. **Theorem H3** is Lemma 10 at `p = 2`, applied to Barge's twin
   involution.
4. **Theorem Fork for nonunit `σ` with `dim H¹ = 3`: expected, not
   proved.** Besides Lemma 9 its proof uses unimodularity in the first
   paragraph of §7 (the torus as maximal equicontinuous factor; for nonunit
   `σ` it is a solenoid). Steps 1–4 were not rewritten for the solenoid;
   one of the two verifiers of round 2 reports having re-derived them, the
   other did not, and no proof text exists. The statement of Theorem Fork
   stays as printed above, for unit `σ`.
5. **For every determinant and every `dim H¹`** the rank-two note has a
   weaker non-injectivity statement (Theorem NI: the top-track map of a
   swap-symmetric strict component is injective on periodic points only
   for unit `σ` with first defect degree divisible by 3; the second partner
   may be eventually coincident with the first) and, at coincidence rank
   two, Theorem W.

### (d) Pointer

The non-claim "**Infinitude of the non-trivial part of the FC3 class.** Not
shown." and the sentence of §9 "Whether the non-trivial part of the class is
infinite, beyond powers and reversals, is open." are the subject of the
[family note of round 2](c4-fc3-family-2026-11-16.md), which is the record
for them. Nothing is asserted about them here.

## 11. Update 2026-11-17 (FC2 orientation)

Added on 2026-11-17; §§1–10 are unchanged. Theorem FC2 is unchanged as a
statement; its imports shrink. In the proof of §4.2, the strand-reflection
part of step (c) (`cr(σ^R) = cr(σ)`) is no longer needed; its duality
`ν_L(σ^R) = ν_R(σ)` and the reversal invariance of (F) are still used.
`cr ≥ ν_R` follows from
Remark 4.3 at `q = 0` alone, because the right-anchored vertex edges, shifted
by the Parikh vector of a shortest letter, are states over `0`; and on (F)
`ν_L = ν_R` holds by an integer argument with no rank input, for every
alphabet size. Correction (i) after the proof ("Step (c) replaces that
reading") is superseded in the same sense. Corollary E's (i) ⟺ (ii) ⟺ (iii)
is machine-checked on the standing class; (iv) and (v) still rest on the
one-sided input `cr = S(σ)` and on BBK Cor. 5.2. Superseded in the same
sense, and not edited: in §9, "'`cr ≥ ν_R` is BBK Remark 4.3' (false as a
literal reading; replaced by reversal)" (it now follows from Remark 4.3 at
`q = 0` with the shifted right-anchored edges) and the derivation line
"+ reflection (cr, (F) reversal-invariant)" (the `cr` part is no longer
used; the (F) part is). Lemma 1 (1), in its integer
form (equivalent by clearing denominators), and the first clause of
Lemma 1 (3) (`0` is not an eigenvalue) are machine-checked. Record:
[FC2 orientation note](c4-fc2-orientation-2026-11-17.md); Lean:
`PscVerif.GeometricFOrientation`.
