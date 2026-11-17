# FC2 without the reversed rank: the orientation transfer on property (F) — 2026-11-17

**Status:** written proofs. Theorem O, Lemma Z and Corollary E′ have a
complete machine-checked counterpart (Lean module
`PscVerif.GeometricFOrientation`; axioms a subset of `propext`,
`Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`); Corollary
FC2-1s is machine-checked only in its integer part (`cr(σ) = S(σ)` and
Barge–Diamond Theorem 1 are imported).
**Universal C4 is not proved and remains open.** Nothing here changes a
governed claim status (C4, #138, #139, #84, G1 and PSC are unchanged), no
ledger claim is registered or promoted, and independent human review is
pending. The isolated checker `tools/check_lean.sh` was not run; the
formal-audit receipt has to come from CI.
[Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).

Parents: the [(F)-class note](c4-geometric-f-class-2026-11-16.md) (§4.1
states over `0`, (St), Lemma 6; §4.2 Theorem FC2, Corollaries E and H) and
the [FC2 rank-transfer review](c4-fc2-rank-transfer-review-2026-11-16.md)
(§2, §3, and its "next Lean obligation"). Lean parents:
`PscVerif.GeometricFRank` (the integer edge layer, reflection,
`fc2_rank_transfer`), `PscVerif.GeometricFInclusion` (states, the state map,
(F), absorption), `PscVerif.GeometricFPisot` (the standing-class binding),
`PscVerif.GeometricFTriple` ((F) for Tribonacci). Notation is that of the
review: `I(x, a)` is the labelled edge from `x ∈ ℤ^d` to `x + e_a`, its
descendant at an occurrence `σⁿ(a) = P b Q` is `I(Mⁿx + p(P), b)`, two edges
are *coincident* if they share a labelled descendant at a common level (BBK
§4: "for some `k ≥ 0` their `Φ^k`-images share a labelled edge"), and the
states over `0` are the edges `I(−v, a)` with `0 ≤ ℓ·v < ℓ_a`.

## 0. What changes, in one paragraph

The review's next Lean obligation was to instantiate **two** zero-slice rank
realisations, `IsMaximumSize (StateFamily s L) c` and
`IsMaximumSize (StateFamily (reverseSubstitution s) L) c`, for one common BBK
rank `c`; the second needed reflection of full strands
(`cr(σ^R) = cr(σ)`, step (c) of the class note's proof of FC2). It is not
needed. A common **integer** translation preserves coincidence, and the
right-anchored edges `I(−e_c, c)` shifted by the Parikh vector of a shortest
letter are states over `0`; with absorption under (F) this gives
`ν_L = ν_R` on (F) by an integer argument, with no rank input, in every
alphabet size. On (F) the integer zero-slice maximum then exists and is one
number in four forms (states of `σ`, states of `σ^R`, left and right letter
families). FC2 (2) needs one geometric input instead of two, and that one is
one-sided: `cr(σ)` is the zero-slice maximum of `σ` (BBK Def. 4.1 and
Remark 4.3 at `q = 0`, with Lemma 6). Off (F), the integer content of the
dropped step is recovered anyway: with `ℓ` injective and `d ≥ 2`, every
family of states over `0` of `σ` reflects to one of `σ^R`, so
`S(σ) = S(σ^R)` for every such `σ`
and the reversed rank realisation is a consequence of the direct one.
Corollary E's equivalences
(i) ⟺ (ii) ⟺ (iii) (no strict system; left; right strong coincidence of all
pairs) become elementary and are machine-checked on the standing class. The
"ℤ-kernel premise" (injectivity of `v ↦ ℓ·v` on `ℤ^d`) is machine-checked from
the standing hypotheses.

## 1. Targeted stop/go

*Timing, stated plainly.* The idea (integer translation instead of a
translation along `E^u`) and a first Lean draft came first; the literature
check, three independent adversarial verifiers (Lean semantics, geometry
and the BBK interface, hypotheses and counterexamples) and a kernel scout
ran in parallel with the draft, and the draft was changed by their findings
(the density step was replaced by the shortest-letter shift; the reflection
of arbitrary families and the Barge–Diamond counter-calibration were added).
No verifier refuted the argument. The record below was written after the
results existed.

**Proposed claim.** For a primitive substitution with an irreducible Pisot
incidence matrix and geometric property (F), in every alphabet size and
every determinant: `ν_L = ν_R`, and both equal the integer zero-slice maximum
of `σ` and of `σ^R`, by an integer argument with no rank input; so FC2 (2)
needs only the one-sided import `cr(σ) = S(σ)`.

**Sources read** (read level in brackets).

| Source | Locator | What it gives | Bearing |
| --- | --- | --- | --- |
| Minervino–Thuswaldner, AIF 64 (2014); [arXiv:1402.2002v1](https://arxiv.org/pdf/1402.2002v1) | Def. 2.1; §8.2; §9: Lemma 9.1 and its proof, Def. 9.3, Prop. 9.4, Lemma 9.8, Thm 9.9 (arXiv numbering; journal Def. 9.4, Prop. 9.5, Thm 9.10) [full text of §2.1, §8.2, §9] | strong coincidence is per pair, prefix **or** suffix (mixed); (F) in prefix orientation; (F) + SC ⟹ tiling; the proof of Lemma 9.1 uses density of the module to slide patches | no comparison of the two orientations; the closest printed use of a small translation in the module |
| Siegel–Thuswaldner, Mém. SMF 118 (2009), [numdam](https://www.numdam.org/item/10.24033/msmf.430.pdf) | Def. 2.9; Def. 3.6; Thm 3.20; Thm 4.6, 4.7, Example 4.8 [statements read, proofs not] | mixed SC; (F); unit: (F) + SC ⟹ tiling; tiling ⟺ super-coincidence; examples failing (F) | a link of the unit composite chain below |
| Berthé–Siegel–Thuswaldner, CANT ch. 5 (2010), [PDF](https://www.irif.fr/~berthe/Articles/Chapter5.pdf) | Def. 5.2.9; Thm 5.4.2 with proof; Def. 5.4.3; Def. 5.6.4–5.6.5; Thm 5.6.8 with proof [read] | prefix SC; (F) + SC ⟹ tiling, by pushing tiles into level-`N` subtiles (the measure form of absorption, rank one only); the proof of Thm 5.6.8 uses integer translation invariance of geometric coincidence | (T) and the rank-one absorption are in print in the unit case |
| Baker–Barge–Kwapisz, AIF 56 (2006), [numdam](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf) | Def. 4.1; Thm 4.2; (4.6), Remark 4.3 with proof; §7 [read] | `cr`; Remark 4.3 for every `q`, proved by translating along `E^u`, which "winds densely in `V/Σ`" | the one import left, at `q = 0` |
| Barge–Kwapisz, AJM 128 (2006), [PDF](https://math.montana.edu/jarek/documents/papers/AJM2006.pdf) | (7.3); Fact 7.2 with proof; Def. 7.1 [read] | coincidence is translation equivariant, `I ∼ J ⟺ I + x ∼ J + x`; `cr` can be computed over any `q` | (T) is (7.3); unimodular paper, but the identity is determinant-free |
| Akiyama–Lee, EJC 39 (2014), [author PDF](https://www.math.tsukuba.ac.jp/~akiyama/papers/OverlapC-to-StrongC-EJC_revise4-finalSubmit2_1.pdf) | §3 footnote 1; Ex. 3.6; Lemma 4.3; Cor. 4.5; Ex. 4.6, 4.7 [final-submission PDF] | prefix/suffix SC are Arnoux–Ito's positive/negative SC; ℚ-independence of the Perron row; overlap coincidence ⟹ prefix SC; reducible examples failing both orientations | Lemma Z is Lemma 4.3 (by a Galois argument) |
| Barge–Diamond, BSMF 130 (2002), [numdam](https://www.numdam.org/article/BSMF_2002__130_4_619_0.pdf) | Theorem 1; final paragraph, `φ = (121, 221)` [full text] | one prefix-coincident pair for Pisot type; `φ` fails prefix SC | the counter-calibration of §6 |
| Sellami–Sirvent, [arXiv:1410.6229v2](https://arxiv.org/pdf/1410.6229v2) | Cor. 2.1; §5 remarks [read] | the trivial duality: prefix SC for `σ` ⟺ suffix SC for `σ^R` | only `vertexCoincident_reverse_iff` |
| Akiyama–Barge–Berthé–Lee–Siegel, Progr. Math. 309 (2015), [HAL](https://inria.hal.science/hal-01196318/document) | §3.1, §5.1, §5.2 [read] | `cr` through the maximal equicontinuous factor; SC in prefix form; `cr` as pairwise non-coincident segments crossing `E^s` in their interior | no orientation comparison; `cr(σ^R) = cr(σ)` follows quickly from the factor definition but is not stated |
| Ito–Rao, Israel J. Math. 153 (2006) | via CANT Thm 5.4.14, 5.6.8 and Siegel–Thuswaldner Thm 3.20 [**not reached**; secondary statements only] | unit: tiling ⟺ super-coincidence | used only in the composite chain below, not verified in the original |
| Solomyak, Ergodic Theory Dynam. Systems 17 (1997) | the overlap-coincidence criterion [**not re-read**; known through its statements in Akiyama–Lee and Barge–Kwapisz] | pure discrete spectrum ⟺ overlap coincidence | a link of the unit composite chain below, not verified in the original |

**What is known.** None of the sources read states `ν_L = ν_R` on (F), or
any comparison of the two orientations beyond the reversal duality (prefix
SC of `σ` is suffix SC of `σ^R`). In the **unit** case the rank-one statement
"on (F), all pairs left strongly coincident ⟺ all pairs right strongly
coincident" follows by composing printed results: left (or right) SC is
mixed SC; with (F) it gives a tiling (Siegel–Thuswaldner Thm 4.6;
Minervino–Thuswaldner Thm 9.9; CANT Thm 5.4.2); tiling ⟺ super-coincidence
(Ito–Rao, seen only through CANT's statement) ⟺ pure discrete spectrum
(Barge–Kwapisz 2006), where the subshift and the tiling-flow forms of pure
discrete spectrum are equivalent (as Barge–Kwapisz recall); pure discrete
spectrum ⟺ overlap coincidence (Solomyak's theorem, not re-read for this
note); overlap coincidence ⟹ prefix SC (Akiyama–Lee Cor. 4.5, no
unimodularity), applied to `σ` and, since pure discrete spectrum passes to
`σ^R` by time reversal, to `σ^R`. The only unit-dependent link is tiling ⟹
pure discrete spectrum; for nonunit `σ` it was not found. The
chain says nothing at rank two. The ingredients of the integer argument are
standard: (T) is Barge–Kwapisz (7.3) and the proof of CANT Thm 5.6.8; the
small-translation step is in the proofs of BBK Remark 4.3, Barge–Kwapisz
Fact 7.2 and Minervino–Thuswaldner Lemma 9.1; Lemma Z is Akiyama–Lee
Lemma 4.3.

**Hypotheses that transfer, and those that do not.** (T) is affine algebra of
descendants, for every determinant. Lemma Z needs only an irreducible
`χ_M` (here with `d ≥ 2` and contraction data, which the standing class
supplies). (F) is Minervino–Thuswaldner's geometric property (F) in prefix
orientation (class note, Lemma 5), matching the left-closed zero slice.
Reversal invariance of (F) is **not** in the sources read (all state (F) in
prefix orientation); it is the repository's `propertyF_reverse_iff` and rests
on injectivity of `ℓ`. No measure, no unimodularity, no BBK is used.

**Negative controls known.** Barge–Diamond's `φ = (121, 221)`: by their final
paragraph it fails prefix SC; by inspection (here machine-checked) both
images end in the same letter, so suffix SC holds at level 1 — the two
orientations differ there, with `ℓ = (1, 1)` not injective, the eigenvalue
`1` (no contraction data), and (F) failing for `φ` and `φ^R`
(`bd_not_propertyF`, `bd_reverse_not_propertyF`). Thue–Morse fails both orientations. Akiyama–Lee
Examples 4.6, 4.7 (reducible) fail both. Failures of (F): Siegel–Thuswaldner
Example 4.8; CANT `τ = (2, 3, 12)`; 2,760 of the 4,554 corpus specimens. No
example with `ν_L ≠ ν_R` inside the primitive irreducible Pisot class was
found in the sources read.

**Decision: proceed, narrowed.** Prove the integer transfer in Lean; replace
the two rank hypotheses of `fc2_rank_transfer` by the one-sided
`IsMaximumSize (StateFamily s L) c`; prove or drop the stronger reflection of
arbitrary families (proved: Theorem O (5)); record Barge–Diamond's `φ` as a
counter-calibration, replayed exactly (here in Lean, not in Mojo).
**Novelty wording:** in the sources read we found no statement that, on
geometric property (F), the maximal families of letters pairwise not prefix-
and pairwise not suffix-coincident have the same size, and no integer-only
proof of it; for unit `σ` the rank-one case also follows from printed
results, and for it only a new elementary, determinant-free proof is
claimed.

## 2. Statements

Throughout, `σ` is a substitution on a finite nonempty alphabet `A`,
`d = |A|`, with incidence matrix `M` and a length row `ℓ > 0` with
`ℓM = βℓ`, `β > 0` (length data). *Contraction data* is the Pisot bound of
the class note's Lemma 3 (a subadditive even `ν` with `ν(Mv) ≤ ρ ν(v)`,
`ρ < 1`, proper together with `ℓ`). `S(σ)` denotes the maximum size of a
pairwise non-coincident family of states over `0`, when it exists; `ν_L`,
`ν_R` are the maximum sizes of letter families pairwise not left, resp. not
right, strongly coincident.

**Theorem O (orientation transfer).**

1. *(Embeddings; positivity of `ℓ` only.)* A family of `n` letters pairwise
   not left strongly coincident is a pairwise non-coincident family of `n`
   states over `0` of `σ` (the vertex states), and also of `σ^R`. A family of
   `n` letters pairwise not right strongly coincident is a pairwise
   non-coincident family of `n` states over `0` of `σ`, and also of `σ^R`
   (the vertex states).
2. *(Absorption.)* With contraction data and (F) for `σ`, a pairwise
   non-coincident family of `n` states over `0` of `σ` yields `n` letters
   pairwise not left strongly coincident (`PscVerif.GeometricFRank`).
3. *(Transfer.)* With contraction data: (F) for `σ` turns every right family
   into a left family of the same size; (F) for `σ^R` turns every left family
   into a right family of the same size.
4. *(Integer rank.)* With contraction data and (F) for both `σ` and `σ^R`,
   there is `r` with `1 ≤ r ≤ d` such that
   `S(σ) = S(σ^R) = ν_L = ν_R = r`. If `ℓ` is injective on `ℤ^d`, (F) for `σ`
   implies (F) for `σ^R`, so (F) for `σ` suffices.
5. *(Reflection of arbitrary families; no (F), no contraction.)* If `ℓ` is
   injective on `ℤ^d` and `d ≥ 2`, every pairwise non-coincident family of
   `n` states over `0` of `σ` gives one of `σ^R`, and conversely. Hence
   `IsMaximumSize (StateFamily (reverseSubstitution s) L) c` holds iff
   `IsMaximumSize (StateFamily s L) c` does, for every `c`.

**Lemma Z (the ℤ-kernel premise).** If `χ_M` is irreducible over `ℚ`,
`d ≥ 2`, `ℓ > 0` is a left eigen-row for `β > 0` and every other complex
root of `χ_M` has modulus `< 1`, then `ℓ·v = 0` for `v ∈ ℤ^d` only if `v = 0`.

**Corollary FC2-1s (FC2 with a one-sided input).** Let `σ ∈ PIP3`.
(1) If every pairwise non-coincident family of states over `0` of `σ` has
at most `cr(σ)` members (the bound half of BBK Remark 4.3 at `q = 0`, with
Def. 4.1 and Lemma 6), then `cr(σ) ≥ max(ν_L, ν_R)`. (2) If `cr(σ) = S(σ)`
(bound and attainment at `q = 0`) and `σ` has (F), then
`cr(σ) = ν_L = ν_R`, and with Barge–Diamond 2002 Theorem 1, `cr(σ) ≤ 2`.
Theorem FC2 of the class note is therefore unchanged as a statement; its
imports shrink (§5).

**Corollary E′ (elementary part of Corollary E).** For `σ` primitive on at
least two letters with `χ_M` irreducible over `ℚ`, `β` Pisot in root form
and (F): `σ` has a strict system ⟺ some pair of distinct letters is not
left strongly coincident ⟺ some pair of distinct letters is not right
strongly coincident. No rank and no spectral input.

## 3. Proofs

*(T) Translation.* If `σⁿ(a) = P b Q`, the descendant of `I(x + u, a)` at
that occurrence is `I(Mⁿx + p(P) + Mⁿu, b)`, the descendant of `I(x, a)`
shifted by `Mⁿu`. So `I(x + u, a)` and `I(y + u, b)` share a descendant at
level `n` iff `I(x, a)` and `I(y, b)` do; translating back by `−u` gives the
converse.

*(D) The shift.* Let `a₀` be a shortest letter and `u = e_{a₀}`. Then
`0 < ℓ·u ≤ ℓ_c` for every letter `c`, so `(c, e_c − u)` satisfies
`0 ≤ ℓ·(e_c − u) < ℓ_c`: it is a state over `0` (for `c = a₀` the vertex
state `(a₀, 0)`). Only the left-closed convention is used; no density of
`ℓ(ℤ^d)` and no injectivity of `ℓ`.

*Theorem O (1).* The left case is (St) of the class note: the vertex edges
`I(0, c)` are states over `0`, and two of them are coincident iff the letters
are left strongly coincident (`edgeCoincident_zero_iff`). For a right family
`c₁, …, c_n` of `σ`: the review's reflection `R I(x, a) = I(−x − e_a, a)`
conjugates descendants of `σ` to descendants of `σ^R`
(`edgeDescendant_reflect`), and a right witness of `σ` is a left witness of
`σ^R` (`vertexCoincident_reverse_iff`). So the vertex edges `I(0, c_i)` of
`σ^R` are pairwise non-coincident for `σ^R`; reflected, the right-anchored
edges `I(−e_{c_i}, c_i)` are pairwise non-coincident for `σ`; translated by
`u` (T), the edges `I(u − e_{c_i}, c_i)` are pairwise non-coincident for `σ`,
and by (D) they are the edges of the states `(c_i, e_{c_i} − u)` over `0`.
Applied to `σ^R` (whose reversal is `σ`), the same steps give the two
statements about `σ^R`.

*Theorem O (2)* is `leftLetterFamily_of_stateFamily` of
`PscVerif.GeometricFRank`: under (F) and contraction data every state reaches
a vertex state (class note, Lemma 3 (4)); at a common time the descendants
are vertex edges `I(0, c_i)`; a shared descendant of two of them would be a
shared descendant of the original states, so the `c_i` are pairwise not left
strongly coincident (and distinct, coincidence being reflexive).

*Theorem O (3).* A right family of `σ` of size `n` is, by (1), a family of
`n` states over `0` of `σ`; by (2) for `σ` it yields a left family of size
`n`. A left family of `σ` is, by (1), a family of states over `0` of `σ^R`;
by (2) for `σ^R` (length data and contraction data pass to `σ^R` unchanged:
`M` is the same) it yields a left family of `σ^R`, which is a right family of
`σ`.

*Theorem O (4).* Coincidence is reflexive (level `0`), so a family of
letters pairwise not coincident is injective and has at most `d` members;
`ν_L` exists, and `ν_L ≥ 1` (one letter). (F) for `σ^R` follows from (F)
for `σ` when `ℓ` is injective on `ℤ^d` (the review's §3;
`propertyF_reverse_iff`). By (3) `ν_R = ν_L`. By (1) `S(σ) ≥ ν_L`, and by (2) every family of states over `0`
of `σ` has size `≤ ν_L`; so `S(σ)` exists and equals `ν_L`. For `σ^R`: (1)
gives `S(σ^R) ≥ ν_L`; (2) for `σ^R` turns a family of states of `σ^R` into a
left family of `σ^R`, i.e. a right family of `σ`, of size `≤ ν_R = ν_L`. ∎

*Theorem O (5).* Let `(a_i, v_i)` be pairwise non-coincident states over `0`
of `σ`, with edges `I(−v_i, a_i)`. Reflection gives the edges
`I(v_i − e_{a_i}, a_i)` of `σ^R`, pairwise non-coincident; they run from
`ℓ`-height `ℓ·v_i − ℓ_{a_i} < 0` to `ℓ·v_i ≥ 0`, and the ones with `v_i = 0`
meet `E^s` only at their end point. Since `ℓ` is injective and `d ≥ 2`, the
group `ℓ(ℤ^d) ⊆ ℝ` is not cyclic (a generator `g` would give
`ℓ_a = k_a g`, `ℓ_b = k_b g` and `ℓ·(k_b e_a − k_a e_b) = 0` for two letters
`a ≠ b`), hence dense; pick `u ∈ ℤ^d` with
`0 < ℓ·u ≤ min_i (ℓ_{a_i} − ℓ·v_i)`. By (T) the edges
`I(v_i − e_{a_i} + u, a_i)` are pairwise non-coincident, and they are the
edges of the states `(a_i, e_{a_i} − v_i − u)` of `σ^R`:
`0 ≤ ℓ_{a_i} − ℓ·v_i − ℓ·u < ℓ_{a_i}`. The converse is the same statement for
`σ^R`. ∎ With BBK Remark 4.3 at `q = 0` for both `σ` and `σ^R` this gives
`cr(σ^R) = cr(σ)` at the integer level, which is what step (c) of the class
note proved with full strands; FC2 no longer needs it, and the review's
remark that the rank bound "also works whenever an attaining family of
states in each orientation reaches vertex states" goes through with (5) in
place of step (c).

*Lemma Z.* First `det M ≠ 0`: otherwise `χ_M(0) = ± det M = 0`, so `X`
divides `χ_M`; `χ_M` is irreducible and `X` is not a unit, so the cofactor is
a unit and `deg χ_M = 1 < d`. Contraction data exist under the hypotheses
(`GeometricFPisot.exists_contractionData_of_pisot`). Let `ℓ·v = 0`. Then
`ℓ·Mᵏv = βᵏ ℓ·v = 0` and `ν(Mᵏv) ≤ ρᵏ ν(v) ≤ ν(v)` for every `k`, so the
orbit lies in the finite set `{w : |ℓ·w| ≤ 0, ν(w) ≤ ν(v)}` (properness):
`Mⁱv = Mʲv` for some `i < j`. As `det Mⁱ ≠ 0`, `M^p v = v` with
`p = j − i ≥ 1`, hence `ν(v) ≤ ρ^p ν(v)` with `ρ^p < 1` and `ν(v) ≥ 0`:
`ν(v) = 0`. Then `ν(0) ≤ ν(v) + ν(−v) = 0` and, by subadditivity, `ν(kv) ≤ 0`
for every `k ∈ ℕ`, so all multiples `kv` lie in the finite set
`{|ℓ·w| ≤ 0, ν(w) ≤ 0}`: `iv = jv` for some `i < j`, `(j − i) v = 0`, `v = 0`.
∎ The class note's §2 (Lemma 1 (1), a cyclic-vector argument) and the
review's §1 prove the same statement from irreducibility directly; this route reuses the
machine-checked contraction data instead of a Galois argument.

*Corollary FC2-1s.* (1) By Theorem O (1), left and right families are
families of states over `0` of `σ`; by the hypothesis of (1) (the bound
half of Remark 4.3 at `q = 0`) they have at most `cr(σ)` members. (2) Theorem O (4) and the uniqueness of a maximum. The
bound `ν_L ≤ 2` is Barge–Diamond's Theorem 1 as in step (d) of the class
note. ∎

*Corollary E′.* (i) ⟺ (ii) is Theorem FC1 (`fc1_equivalence_of_primitive_pisot`).
(ii) ⟺ (iii): by Theorem O (4), `ν_L = ν_R`, and for a reflexive symmetric
relation the maximum family size is `1` iff all pairs of distinct letters
are related (`isMaximumSize_one_iff`). The hypotheses of Theorem O (4) hold
on the standing class by `fc1_hypotheses_of_primitive_pisot` and Lemma Z. ∎

## 4. The Lean map

All in `proof/PscVerif/PscVerif/GeometricFOrientation.lean`, namespace
`Psc.GeometricF`.

| Statement | Declaration | Hypotheses in Lean |
| --- | --- | --- |
| (T) | `edgeDescendant_translate`, `edgeCoincident_translate_iff` | none |
| reflexivity, symmetry | `edgeCoincident_refl`, `edgeCoincident_symm`, `rightStrongCoincidenceWitness_refl`, `rightStrongCoincidenceWitness_symm` | none |
| (D) | `exists_letter_shift` | `ℓ > 0` on letters, finite nonempty alphabet |
| density | `exists_small_length` | `ℓ > 0`, `L` injective, `|α| ≥ 2` |
| Theorem O (1) | `stateFamily_of_leftLetterFamily` (in `GeometricFRank`), `stateFamily_of_rightLetterFamily`, `stateFamily_reverse_of_leftLetterFamily`; the vertex states of `σ^R` for a right family: `rightLetterFamily_iff_reverse` with `stateFamily_of_leftLetterFamily` | `ℓ > 0` on letters, nonempty alphabet |
| Theorem O (2) | `leftLetterFamily_of_stateFamily` (in `GeometricFRank`) | `LengthData`, `ContractionData`, `PropertyF` |
| Theorem O (3) | `leftLetterFamily_of_rightLetterFamily`, `rightLetterFamily_of_leftLetterFamily` | as (2), with `PropertyF` of `σ`, resp. of `σ^R` |
| Theorem O (4) | `fc2_integer_rank_of_reverse`; `fc2_integer_rank` | `LengthData`, `ContractionData`, `PropertyF` of `σ` and of `σ^R`; resp. `PropertyF` of `σ` and `L` injective |
| Theorem O (5) | `stateFamily_reverse_of_stateFamily`, `stateFamily_reverse_iff`, `isMaximumSize_stateFamily_reverse_iff` | `ℓ > 0`, `L` injective, `|α| ≥ 2` |
| family lemmas | `LetterFamily.le_card`, `exists_isMaximumSize`, `IsMaximumSize.unique`, `isMaximumSize_one_iff` | a reflexive relation (and symmetric, nonempty alphabet, for `isMaximumSize_one_iff`) |
| Corollary FC2-1s, integer part | `fc2_rank_transfer_one_sided` (`fc2_rank_transfer` without `hRankRev`, plus a nonempty alphabet; it also concludes the `σ^R` realisation), `fc2_rank_lower_bounds_one_sided` | as `fc2_integer_rank`; resp. `ℓ > 0` only |
| Corollary E (ii) ⟺ (iii) | `leftAll_iff_rightAll` | as `fc2_integer_rank` |
| Lemma Z | `det_incZ_ne_zero_of_irreducible`, `eq_zero_of_length_eq_zero`, `lenHom_injective_of_pisot` | (I), `d ≥ 2`, (E), `β > 0`, (R) |
| standing class | `fc2_integer_rank_of_primitive_pisot`, `fc2_integer_rank_pip3`, `fc1_right_of_primitive_pisot` (Corollary E′) | (P), (I), (E), (R), (F) |
| Tribonacci | `trib_right_all`, `trib_integer_rank_one`; cross-check `trib_right_witness_01`, `_02`, `_12` | none left |
| Thue–Morse, rank two | `tm_integer_rank_two`; `tm_reverse_propertyF` via `propertyF_of_mulVec_state_eq_zero` | none left; not PIP3 |
| Barge–Diamond `φ` | `bd_left_two_right_one` (`bd_power`, `bd_not_left`, `bd_right`), `bd_lengthData`, `bd_not_contractionData`, `bd_not_propertyF`, `bd_reverse_not_propertyF` | none left; counter-calibration |

(P), (I), (E), (R), (F) are the hypothesis names of `PscVerif.GeometricFPisot`.
The Tribonacci cross-check is independent of the transfer: the right
witnesses are words, checked by `decide` (`σ⁴(0) = 01·0·2010010201` against
`σ⁴(1) = 0·1020100102`; `σ⁴(0) = 010201·0·010201` against
`σ⁴(2) = 0·102010`; `σ³(1) = 01·0·201` against `σ³(2) = 0·102`).

## 5. What FC2 now imports

| Step of FC2 | Before (class note §4.2; review §2–§3) | Now |
| --- | --- | --- |
| `cr ≥ ν_L` | BBK Remark 4.3 at `q = 0` | unchanged: one-sided input, Theorem O (1) |
| `cr ≥ ν_R` | reflection of full strands and `cr(σ^R) = cr(σ)` (class note (c)); or Remark 4.3 at a non-lattice point `q = [t]`, `t ∈ E^u` (review §3) | one-sided input at `q = 0`, Theorem O (1): the shifted right-anchored edges are states over `0` |
| `cr ≤ ν_L` on (F) | Remark 4.3 at `q = 0`, absorption | unchanged |
| `cr ≤ ν_R` on (F) | the same for `σ^R` with `cr(σ^R) = cr(σ)` | Theorem O (4): `ν_R = ν_L`, integer |
| `cr(σ^R) = cr(σ)` | reflection of full strands | not needed; its integer content at `q = 0` is Theorem O (5), with no (F) |
| `ℓ` injective on `ℤ³` | Lemma 1 (1) of the class note; review §1 | machine-checked: Lemma Z |
| `ν_L, ν_R ≤ 2` | Barge–Diamond 2002 Thm 1 | unchanged |
| (iv) ⟺ (v) of Corollary E | BBK Cor. 5.2 | unchanged |

So the one geometric input of FC2 is `cr(σ) = S(σ)`: BBK Def. 4.1 with
Remark 4.3 at the single point `q = 0`, which needs `Σ = ℤ³` (Lemma 6) to
identify BBK's states over `0` with the integer states. The reflection of
full strands (class note §4.2 (c)) is no longer used anywhere: a search of
`docs/` finds `cr(σ^R) = cr(σ)` only in that step and in its restatement in
the review's §3, and the adversarial
verifier of the geometric interface found no other consumer (Theorems P,
FC3, N, Fork, the rank-two note and round 3 use `cr(σ)` and the conclusions
of FC2 only). Both halves of Remark 4.3 at `q = 0` are still used for FC2 (2)
(the bound and the attainment); FC2 (1) uses the bound only. Barge–Diamond
Theorem 1 and BBK Cor. 5.2 are unchanged imports.

## 6. Negative controls

- **Thue–Morse `01/10`** (two letters; `χ = x(x − 2)`, reducible; not Pisot
  type; not PIP3). `ℓ = (1, 1)` is not injective on `ℤ²`, so
  `fc2_integer_rank` does not apply; but length data, contraction data
  (`ρ = 0`, `GeometricFStrict.tm_contractionData`) and (F) hold for `01/10`
  and for its reversal `10/01` (`M` kills every state vector), so
  `fc2_integer_rank_of_reverse` applies, and all four maxima are `2`
  (`tm_integer_rank_two`). This is the only rank-two instance in Lean; it
  shows Theorem O (4) is not vacuous at `r = 2` and that injectivity of `ℓ`
  is not necessary for it. It is not a PIP3 specimen and says nothing about
  `ν_L = 2` on PIP3.
- **Reflection without translation.** The review's control stands: the
  reflected vertex edge `I(−e_a, a)` is not a state over `0` (its only point
  on `E^s` is its end point; `reflect_left_vertex_not_state`). The shift by
  `e_{a₀}` is what makes it one; the shift by a vector of the unstable line
  (review §3) leaves the lattice and needs Remark 4.3 at another point.
- **The mixed predicate.** The review's logical control (sole left failure
  `{a, b}`, sole right failure `{a, c}` on three letters: both ranks two) is
  not excluded by Theorem O: equal ranks do not give equal failing pairs.
  Theorem O equates the two maxima, not the two relations.
- **Without (F).** Theorem O (1) gives `S(σ) ≥ max(ν_L, ν_R)` whenever `S(σ)`
  exists, and (5) gives `S(σ) = S(σ^R)` when `ℓ` is injective and `d ≥ 2`;
  nothing else. Whether `ν_L = ν_R`
  off (F) inside the irreducible Pisot class is not decided here, and no
  corpus census of `(ν_L, ν_R)` off (F) is pinned (§7, non-claims).
- **Barge–Diamond's `φ = 010/110`** (their `(121, 221)`; primitive,
  `M = [[2, 1], [1, 2]]`, eigenvalues `3, 1`; not Pisot type). `ν_L = 2` and
  `ν_R = 1` (`bd_left_two_right_one`): `φⁿ(0)` and `φⁿ(1)` differ only in their
  first letter (`bd_power`), so no prefix witness exists (`bd_not_left`), while
  both images end in `0` (`bd_right`). Length data exist (`bd_lengthData`,
  `ℓ = (1, 1)`, `β = 3`); contraction data do not (`bd_not_contractionData`:
  `M` fixes `(1, −1)`; stated for `β > 1`, and length data on `φ` force
  `β = 3`), (F) fails for `φ` and for `φ^R` (`(0; 1, −1)` is `f`-fixed:
  `bd_not_propertyF`, `bd_reverse_not_propertyF`), and `ℓ` is not injective.
  So the hypotheses of Theorem O (3), (4) cannot all be dropped, and the
  stronger "`ν_L = ν_R` for every primitive substitution" is false; the
  example does not isolate which hypothesis is needed.
- **Exploratory search.** A scratch search by the hypotheses verifier of §1
  found no substitution with (F) and `ν_L ≠ ν_R`. Its seeds, bounds and caps
  were not recorded, so it is not replayable and is not evidence for
  anything here; no figures from it are quoted.
- **Where (F) enters.** Only through absorption (Theorem O (2)); the
  direction left ⟹ right needs (F) for `σ^R`, which is (F) for `σ` only via
  injectivity of `ℓ`. Lemma Z supplies that on the standing class. On the
  control `01/12/021` (F) fails (`ctrl_not_propertyF`); it is PIP3 on paper,
  so only Theorem O (1), (5) and Lemma Z apply there.

## 7. Work shown

### Assumptions and hypotheses

Theorem O (1): a finite nonempty alphabet and positive tile lengths. Theorem
O (2), (3): length data (`ℓM = βℓ`, `β > 0`, `ℓ > 0`), contraction data, and
(F) for `σ`, resp. `σ^R`. Theorem O (4): length data, contraction data, and
(F) for both `σ` and `σ^R`, or (F) for `σ` with `ℓ` injective on `ℤ^d`.
Theorem O (5): `ℓ > 0`, `ℓ` injective on `ℤ^d`, `d ≥ 2`; no (F), no
contraction. Lemma Z: `χ_M` irreducible over `ℚ`, `d ≥ 2`, a positive left
eigen-row for `β > 0`, every other complex root of modulus `< 1`. Corollary
FC2-1s: for (1) the bound half of Remark 4.3 at `q = 0` (with BBK Def. 4.1
and Lemma 6), for (2) the identification `cr(σ) = S(σ)` (bound and
attainment), and Barge–Diamond 2002 Theorem 1. Corollary E′: (P), (I), (E), (R),
(F). Neither the determinant nor three letters are used outside the
specialisations `fc2_integer_rank_pip3` and the PIP3 reading of FC2.

### Derivation / reduction

§3: translation invariance of coincidence, the shift by a shortest letter,
the embeddings of left and right letter families into the zero slice, the
absorption under (F), the bookkeeping of maxima, and the reflection of
arbitrary families with a translation from the dense length group. Lemma Z
by the orbit of `v` in a finite set and `det M ≠ 0`. §5 lists which step of FC2 each piece
replaces.

### Evidence and replay

```sh
cd proof/PscVerif
lake build PscVerif
{ echo 'import PscVerif.GeometricFOrientation'
  grep -oP '^(theorem|def) \K\S+' PscVerif/GeometricFOrientation.lean |
    sed 's/^/#print axioms Psc.GeometricF./'; } > /tmp/FC2OrientationAudit.lean
lake env lean /tmp/FC2OrientationAudit.lean
cd ../..
python3 tools/make_proof_bank.py --check
python3 tools/make_ledger.py --check
python3 tools/check_markdown_source.py
PYTHONPATH=tools python3 -m claim_governance.cli --root .
```

The library was built with Lean `4.34.0-rc2` against the Mathlib revision of
`lake-manifest.json`, with the new module imported by the aggregator.
`#print axioms` on every declaration of the module (53) gives a subset of
`propext`, `Classical.choice`, `Quot.sound`; the file contains no `sorry`
and no `native_decide`. The proof bank was regenerated; the four checks
above pass. The isolated checker `tools/check_lean.sh` was not run.

### Negative controls

§6: Thue–Morse (injectivity fails; the other hypotheses and the conclusion
hold), the reflected vertex
edge (not a state without the shift), the mixed predicate (not excluded),
the non-(F) case (not decided), `01/12/021` ((F) fails), Barge–Diamond's
`φ` (`ν_L = 2 ≠ 1 = ν_R`; contraction, (F) on both sides and injectivity
fail; machine-checked). Thue–Morse is
also the rank-two non-vacuity instance (`tm_integer_rank_two`).

### Non-claims / remaining gaps

- `cr(σ) = S(σ)` is imported (BBK, Lemma 6), not machine-checked; the
  statements about `cr` are conditional on it. Nothing about BBK's strand
  space, its rank or its spectrum is formalised.
- `ν_L ≤ d − 1` (Barge–Diamond) is not machine-checked; in Lean only
  `r ≤ d`.
- Excluding `ν_L = 2` on (F) (the open statement of the class note §4.3 and
  the closure-attempt note §16.3 item 1) is untouched: Theorem O equates the
  two orientations and excludes nothing.
- (F) is machine-checked for Tribonacci only among three-letter specimens
  (also for the two-letter Fibonacci and Thue–Morse `01/10`, `10/01`). On
  the corpus `ν_L = ν_R = 1`
  on all 4,554 specimens, (F) or not, is already pinned without (F) or FC1:
  `ν_L = 1` by `kernel/tests/test_c4_standing_corpus.mojo` (every one of the
  13,662 pairs left strongly coincident), and `ν_R = 1` because the corpus is
  closed under reversal (`kernel/tests/test_seed_strength.mojo`, Lemma RC of
  the [seed-strength note](p1-seed-strength-2026-10-08.md)), so the suffix
  decisions are the prefix decisions permuted. The corpus therefore cannot
  test Theorem O, and no Mojo regression is added: a `(ν_L, ν_R)` table by
  (F) class would be a conjunction of existing pins (kernel scout of this
  round). A PIP3 specimen with `ν_L ≥ 2` or `ν_R ≥ 2` would have `cr ≥ 2`
  (FC2 (1), conditional on its import), i.e. no pure discrete spectrum.
- No novelty is claimed beyond "not found in the sources read" (§1); for
  unit `σ` the rank-one case also follows from printed results. Ito–Rao
  2006 was not read in the original.
- `ν_L = ν_R` off (F) is not claimed. Barge–Diamond's `φ` fails (F) for `φ`
  and `φ^R`, contraction data and injectivity of `ℓ` together and has
  `ν_L ≠ ν_R`: the hypotheses cannot all be dropped, and the example does not
  isolate which one is needed. No example inside the irreducible Pisot class
  is known either way.
- Universal C4, #138, #139, #84, G1 and PSC are open; no governed status
  changes.
