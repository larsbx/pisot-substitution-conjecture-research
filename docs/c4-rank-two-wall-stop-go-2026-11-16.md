# The coincidence-rank-two wall for C4: targeted stop/go — 2026-11-16

**Status:** targeted literature stop/go note (`AGENTS.md`, review gate) for
the statements of
[`c4-rank-two-wall-2026-11-16.md`](c4-rank-two-wall-2026-11-16.md).
**Decision: proceed with a narrowed target, and stop one route.** Universal
C4 remains open; nothing here changes a governed claim status (C4, #138,
#139, #84, G1 and PSC are unchanged); independent human review pending.
[Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).

## Timing, stated plainly

This is round 2 of the attempt recorded in
[`c4-closure-attempt-2026-11-16.md`](c4-closure-attempt-2026-11-16.md). One
route attacked the coincidence-rank-two wall of that note's §10; two
verifiers then attacked its record (a logic and counterexample lens, a
prior-art and scope lens). Nobody proved universal C4.

- The sources marked "attempt" in the table were read on 2026-11-16 by the
  prover and the two verifiers, before any repository text of this
  increment existed. Barge 2015, Barge–Diamond 2008, Baker–Barge–Kwapisz and
  Barge–Bruin–Jones–Sadun had been downloaded for round 1 (2026-11-15) and
  were re-read for the new use.
- Barge–Kellendonk–Schmieding 2012 was found by the prior-art verifier,
  after the prover had written a proof of the statement it contains
  (Lemma 9′), and was read by that verifier in a fetched HTML rendering. Its
  arXiv TeX source was read on 2026-11-16 while this note and the proof note
  were written.
- Anderson–Putnam 1998 and Mignotte 1984 were not read at any time. The two
  attributions rest on secondary sources, read by the prior-art verifier and
  again while writing.
- The executable part (`kernel/psc/fixed_point_count.mojo`, the extension of
  `kernel/psc/c4_geometric_f.mojo`, and their regressions) was written on
  2026-11-16 at about 15:25–15:35 UTC, after the verification of the route
  and before the text of this note (written after 16:25 UTC).

So, as in round 1, the order "sources first, then proof text and kernel
code" was kept for the reading and not for the gate: the decision below was
recorded after the proofs had been attempted and attacked and after the
executable part existed.

## Proposed claims

Standing class **PIP3**: a primitive substitution `σ` on `{0,1,2}` whose
incidence matrix `M` has an irreducible characteristic polynomial with a
Pisot Perron root `β`; `|det M| = 1` is not assumed. `cr` is the coincidence
rank, `g`, `g_R` the first- and last-letter maps, `Φ` the inflation on the
tiling space `Ω_σ`, `dim H¹ = dim H¹(Ω_σ; ℚ)`. A *bigon system* for `σ^P` is
a finite set `B` of ordered irreducible balanced pairs of legal words closed
under `σ^P`-children, with child matrix `N`; its *pair space* `Z ⊆ Ω_σ × Ω_σ`
is the set of pairs of tilings tiled by members of `B`, and the *top track*
is the first projection `π₁: Z → Ω_σ`. Exact statements, hypotheses and
proofs are in the proof note.

1. **Theorem FP.** For a primitive substitution on at least two letters and
   every `n ≥ 1`: `|Fix(Φⁿ)| = tr(Mⁿ) − #Fix(gⁿ) − #Fix(g_Rⁿ)` plus the
   number of legal two-letter words `ba` with `g_Rⁿ(b) = b`, `gⁿ(a) = a`.
2. **Lemma U.** For an irreducible Pisot cubic with roots `β, α₂, α₃` and
   integers `a + b + c ≠ 0`: `β^a α₂^b α₃^c` is a root of unity iff
   `a = b = c` and the constant term is `±1`.
3. **Theorem TT.** For `σ ∈ PIP3` and a primitive bigon system for `σ^P`:
   if the top track is injective on periodic points, `χ_N/χ_{M^P}` is a
   product of powers of `t` and cyclotomic polynomials.
4. **Theorem NI.** For a strict primitive bigon system with `B = swap(B)`
   and first defect degree `r`: if the top track is injective on periodic
   points then `|det M| = 1`, `3 | r` and the only first-defect weight is
   `(r/3, r/3, r/3)`; otherwise the number of fixed tilings with at least
   two fixed partners grows exponentially along a subsequence.
5. **Theorem W.** For `σ ∈ PIP3` with `cr(σ) = 2` and a strict system: the
   strict component is unique, swap- and `Φ × Φ`-invariant, carried by a
   primitive swap-symmetric strict bigon system for `σ` itself (W1); the top
   track is injective over two-point fibres (W2); the swap-odd part of `N`
   has spectral radius below `β`, so `r ≢ 1 (mod 3)` (W3); two partners of
   one tiling coincide on an open dense set (W4).
6. **Lemma S+, Theorem P+.** At `cr(σ) = 2` the eventual range of Barge's
   ordered-pair substitution is two disjoint fixed edges; hence
   `dim H¹ ≥ 3 + |d₂ − 1|`, `d₂ = 3 − ord_t(χ_M mod 2)`, and a divisor
   condition holds at every admissible `n`.
7. **Lemma 9′, Theorem H3.** For `σ ∈ PIP3` with `dim H¹ = 3`, every
   integral class of `H¹` is an eigenfunction class, for every determinant;
   hence `cr(σ) ≠ 2`.
8. **Corollaries FC3+, N+.** (F) and `dim H¹ = 3` give `cr = 1` for every
   determinant; a strict system with `dim H¹ = 3` forces `cr ≥ 3` and the
   failure of (F).
9. **Obstruction T.** At `cr = 2` the first-defect class of the strict
   component is not pulled back from `Ω_σ` unless its eigenvalue is a root
   of unity; the transport of that eigenvalue to Barge's quotient fails.

The executable part is an exact check of Theorem FP on eleven substitutions
and the class counts of items 6–8 over the 4,554-member corpus.

## Prior art and field terminology

- **Coincidence rank two.** Barge 2015 calls a pair of regionally proximal,
  never-coincident tilings an *rpd pair* and the partner of a tiling its
  *twin*; `≈_s` is "densely stably equivalent in one fibre"; the quotient
  `Ω/≈_s` is the tiling space of a substitution on *stacks*. His Theorem 22
  is "odd norm and `cr = 2` imply `dim H¹ ≥ 2d − 1`", and his Corollary 23
  is the Coincidence Rank Conjecture of Barge–Bruin–Jones–Sadun at
  `cr = 2`. A substitution with `dim H¹` equal to the degree of its dilation
  is *homological Pisot* in the latter paper.
- **Eventual range.** Barge–Diamond 2008: the transition graph `S`, its
  eventual range `ER`, the number `k` of components and the asymptotic-cycle
  rank `l`; the exact sequence `0 → G_0 → G_1 → G_2 → G_3 → 0`.
- **Counting periodic points.** The numbers `|Fix(Φⁿ)|` are the
  coefficients of the Artin–Mazur dynamical zeta function of the inflation;
  Anderson–Putnam express it by the action on the cochain (or cohomology)
  groups of their complex.
- **Eigenfunction classes.** Barge–Kellendonk–Schmieding study
  `π*: H¹(Ω_max) → H¹(Ω)` for the maximal equicontinuous factor; they use
  the Schwartzman winding number (the degree-one Ruelle–Sullivan map) and
  the Bruschlinsky group `[X, S¹]`.
- **On main.** The decomposition of the oriented double cover into `N` and
  the signed matrix `S`, and "the Parikh quotient is deck-even", are
  Proposition 1 and §3 of the
  [orientation-spectrum note](c4-orientation-spectrum.md); the signed
  first-defect intertwiner is the
  [lowest-defect note](c4-lowest-defect-intertwiner.md) and manuscript
  `thm:defect-intertwiner` (Lemma 0 of the
  [general-structure note](c4-general-structure-2026-11-06.md) on ordered
  pairs); `ρ(S) ≤ β` with its equality cases is manuscript `prop:cocycle`;
  the shape list of first-defect weights and "strict odd contraction forces
  `r ≡ 0, 2 (mod 3)`" are manuscript `thm:sieve`, the
  [multidegree sieve](c4-multidegree-spectral-sieve.md) §§2–5 and §8, and
  Corollary B of the [degree-four note](c4-degree4-free-lie.md), with Lean
  `no_strictComponent_deg4_of_hasBothSigns`; Lean covers the intertwiner
  and the sieve through `r = 5` (`Degree5Transport`, `Degree5Sieve`). The
  `dim H¹` stratification of the corpus, and the warning not to cite Barge's
  Corollary 25 for `l = 0`, are the
  [`dim H¹` census](c4-h1-census-2026-11-05.md). Round 1 supplied Lemma S,
  Theorem P, Lemmas 8–10 and Theorem Fork
  ([(F)-class note](c4-geometric-f-class-2026-11-16.md)) and Theorem FL
  (closure-attempt note). The retired derived-substitution route
  ([cut-attractor note](c4-cut-attractor-window-2026-11-05.md) §7) asked for
  a unique partner everywhere.

## Primary sources inspected

"Attempt" means: read on 2026-11-16 by the prover and re-read by the
verifier or verifiers named. "Writing" means: re-read while this note and
the proof note were written.

| Source | Exact result | Hypotheses and transfer boundary | Read |
| --- | --- | --- | --- |
| Barge, *Factors of Pisot tiling spaces and the Coincidence Rank Conjecture*, Bull. Soc. Math. France 143 (2015); arXiv:1301.7094 (numbering of the arXiv text) | Thm 4(1)–(5); §3 (`≈_s` is a closed equivalence relation; `{v : T − v ∼_s T′ − v}` is open); Thm 5; Thm 12 (stack substitution; `≈_s` trivial on the quotient; `g = g_s ∘ Σ`); Lemma 13 (`cr = 2`, `≈_s` trivial: a unique regionally proximal, disjoint partner) and its proof, whose first half (two such partners are `≈_s`-equivalent) does not use the triviality of `≈_s`; Lemma 14 (`Σ_op` is an isomorphism); Lemma 15 (`Ψ_p` is non-periodic, forces the border, `Ω_{Ψ_p} ≅ Ω_Ψ/∼_rpd`); Example 16 (Thue–Morse); Thm 17 (`Σ_p` is a 2-to-1 covering onto a pure discrete substitution tiling space); the proper version (§4); Prop. 19 (`Σ*` injective on `H¹`); Lemma 20; sequence (4.1), Lemma 21; Thm 22 and its proof (the ordered-pair substitution has exactly two periodic allowed bi-infinite words, both fixed); Cor. 23–25 | §2: primitive, non-periodic, FLC, Pisot dilation; no irreducibility, no unimodularity. Thm 22 needs odd norm, but only through Lemma 20: the chain Thm 12, Lemmas 13–15, Thm 17, Prop. 19 and the count of periodic words have no parity hypothesis, and that is what Lemma S+ and Theorem H3 use. **Cor. 25 is not the locator for "`dim H¹ = 3` excludes `cr = 2`"**: it reads "any counterexample to the Pisot Substitution Conjecture must have an asymptotic cycle or coincidence rank greater than two", it concerns the unimodular conjecture, and it passes from `G_3 ≠ 0` to an asymptotic cycle, while `l = 0` is not "no asymptotic cycle" (Fibonacci; census note). The locator for odd determinant is Thm 22 (`5 > 3`), equivalently Cor. 24 for units. For even determinant there is no printed statement. The record of the round cites the covering as "Theorem 15"; in the arXiv text it is Theorem 17 and item 15 is the Lemma. The proofs of Thm 4 are deferred there to other papers and were not followed; the rewriting references for the proper version were not read | attempt (TeX source, §§2–4 line by line; both verifiers); writing (PDF text, §§1–4) |
| Barge–Diamond, *Cohomology in one-dimensional substitution tiling spaces*, Proc. Amer. Math. Soc. 136 (2008) 2183–2191; arXiv:math/0702669 | The complex `K ⊇ S`, the map `g` with `g(e_{ab}) = e_{cd}`, `ER`, `k`, `l`; "if `φ` forces its border, then each component of `ER` is a single edge"; Theorem 4 and its proof (`v_C` fixed by a power of `g*`; the exact sequence, integral); Theorem 4′ (the vectors `w_i`) | primitive, aperiodic. Holds on PIP3, for Barge's ordered-pair substitution and for the child substitution of a strict primitive bigon system | attempt (TeX source; logic verifier); writing (§3) |
| Baker–Barge–Kwapisz, *Geometric realization and coincidence for reducible non-unimodular Pisot tiling spaces with an application to β-shifts*, Ann. Inst. Fourier 56 (2006) 2213–2248 | Prop. 2.3; (3.8)–(3.12), Def. 3.1 (`h_φ` into the inverse limit `𝕋_A`); Def. 4.1; Thm 4.2; (5.1)–(5.3) (the dual of `𝕋_A`, the characters `χ_u`); Thm 5.1; Cor. 5.2; Example 5.3 | primitive, translation-aperiodic, Pisot; non-unimodular allowed, which is what the nonunit statements need: for nonunit `σ` the factor is a solenoid and `h_φ` records a vertex class at every level | attempt (passages; logic verifier); writing (the passages listed) |
| Barge–Bruin–Jones–Sadun, *Homological Pisot substitutions and exact regularity*, Israel J. Math. 188 (2012); arXiv:1001.2027 | the theorem labelled `not2` in the arXiv source: a homological Pisot substitution with `d = 1` does not have coincidence rank 2, "regardless of the norm"; its proof for even `N` (after identifying strongly coincident letters the matrix is `[[A, B], [B, A]]` with even trace; the components of the eventual range come in symmetric pairs, so the eigenvalue 1 has odd multiplicity) | degree one only. It is the mechanism of Lemma S+ and Theorem P+, and for `d = 1`, even norm, it is the statement of Theorem H3. Used in no proof. The examples with `cr = 3` (round-1 gate) are covers by transpositions of `S₃`, without a free `ℤ/3` symmetry over the factor, according to the prior-art verifier; this was not re-checked | attempt (TeX source; logic verifier); writing (the statement and its proof) |
| Barge–Kellendonk–Schmieding, *Maximal equicontinuous factors and cohomology for tiling spaces*, Fund. Math. 218 (2012) 243–267; arXiv:1204.1432 (numbering of the arXiv source) | Theorem 1 (`H(Ê) ≅ ΛE`); §3.2 (`[X, S¹] ≅ H¹(X)`; the homomorphism `θ: E → [Ω, S¹]`, `θ(η) = [f_η]`; the winding number `τ`); Lemma 2 (`τ ∘ θ` is the inclusion); Corollary 3 (`π*` is injective in degree one); Lemma 4 (Krasinkiewicz: a class divisible by `k` has a `k`-th root); Theorem 5 (the cokernel of `π*` in degree one is torsion free); Corollary 6; in §5.1 a theorem quoted from Andress–Robinson (one-dimensional, common prefix, irreducible, Pisot: `coker θ = 0`) | an FLC tiling space with minimal `ℝⁿ`-action and an ergodic invariant measure; substitutions primitive, non-periodic, FLC. No Pisot hypothesis, no irreducibility. With `dim H¹ = 3` and three independent eigenvalues it gives Lemma 9′ on `Ω_σ`, and through Barge's Prop. 19 on the quotient `Ω_s`. **This supersedes a row of the round-1 gate** ("every class of `H¹(Ω; ℤ)` is an eigenfunction class: none in print") | prior-art verifier (fetched HTML rendering; statements, proofs paraphrased); writing (arXiv TeX source: statements and proofs of Thm 1 to Cor. 6). Andress–Robinson: not read |
| Anderson–Putnam, *Topological invariants for substitution tilings and their associated C\*-algebras*, Ergodic Theory Dynam. Systems 18 (1998) 509–537 | Thm 9.1 as quoted in Baake–Gähler–Grimm, arXiv:1211.5466 (the zeta function as an alternating product of `det(1 − zA^{(m)})` over the cochain groups) and arXiv:1201.1423 §6 (in dimension one `ζ(z) = det(1 − zA₀)/det(1 − zA₁)`) | substitution tiling spaces with a collared (border-forcing) complex. Theorem FP is that count written on the uncollared alphabet, with an elementary proof; the verifiers compared the two on 400 and on 15 substitutions (scratch) | **not read**; the two secondary sources: prior-art verifier, writing |
| Mignotte, *Sur les conjugués des nombres de Pisot*, C. R. Acad. Sci. Paris Sér. I Math. 298 (1984) 21 | as quoted in Dubickas–Hare–Jankauskas, arXiv:1410.1600, Lemma 1.1: `α₁^{k₁} ⋯ α_d^{k_d} = 1` for the conjugates of a Pisot number of degree `d` holds only if `k₁ = ⋯ = k_d` | any Pisot number. Lemma U is the case `d = 3` (take a power to pass from a root of unity to 1); its proof is kept because the source was not read | **not read**; the secondary source: prior-art verifier, writing |
| Kronecker's theorem (a monic integer polynomial with all roots in the closed unit disc has only the roots 0 and roots of unity) | — | standard; already used on main (Proposition Q(b) of the general-structure note) | **not read** |

Repository sources relied on: the notes linked in the previous section; the
[cut-pair note](c4-cut-pair-productivity-2026-11-04.md) (Theorem A, in Lean);
the round-1 gate
[`c4-geometric-f-class-literature-2026-11-16.md`](c4-geometric-f-class-literature-2026-11-16.md),
whose source table is not repeated. The side-notes ledger was read first
(entries of 2026-11-05 on coincidence rank two and the `dim H¹` census, of
2026-11-06 on the strict-system landscape, and of 2026-11-16 on round 1).

## Work shown

### Assumptions and hypotheses

Hypotheses that transfer to PIP3, nonunit included: primitivity,
aperiodicity and Pisot dilation (Barge 2015, Barge–Diamond 2008,
Baker–Barge–Kwapisz); finite local complexity, minimality and unique
ergodicity (Barge–Kellendonk–Schmieding), also for Barge's quotient `Ω_s`,
which is the tiling space of a primitive non-periodic substitution (his
Thm 12).

Hypotheses that do not transfer, and what replaces them:

| Needed | Source hypothesis | Replacement or restriction |
| --- | --- | --- |
| exclusion of `cr = 2` for even determinant | Barge Thm 22: odd norm, through Lemma 20 | the chain before Lemma 20 has no parity hypothesis; Lemma S+ determines the eventual range exactly, which gives a degree count in `𝔽₂[t]` for every determinant (Theorem P+) and, at `dim H¹ = 3`, Theorem H3 without any parity |
| every integral class is an eigenfunction class | Barge–Kellendonk–Schmieding give injectivity and a torsion-free cokernel, not surjectivity | surjectivity needs equal ranks: the hypothesis `dim H¹ = 3`, with three independent eigenvalues from Baker–Barge–Kwapisz |
| a unique partner | Barge Lemma 13: `cr = 2` and `≈_s` trivial, i.e. on the quotient `Ω_s` | on `Ω_σ` only almost everywhere (W2); two partners of one tiling are `≈_s`-equivalent (W4); by Theorem NI uniqueness fails unless `σ` is unit and `3` divides the first defect degree |
| the count of periodic points | Anderson–Putnam: on the collared complex | Theorem FP: an elementary proof on the alphabet, needing primitivity only |
| the mod-3 sieve for a strictly contracted odd sector | on main it is printed for three-state components and for `r = 4` | its argument uses only that the first-defect image is a quotient of the odd sector; it is applied to the unique component of (W1) |
| the first-defect eigenvalue as an eigenvalue of Barge's `X − Y` | the proposed transport | **fails** (Obstruction T) |
| `dim H¹ = d` excludes `cr = 2` for every Pisot substitution | — | not claimed; a remark marked literature-facing and unreviewed |

### Derivation / reduction

Theorem FP classifies fixed tilings as interior occurrences of a letter in
its own image or as periodic legal seams. Theorem TT compares the two counts
for a bigon system and for `σ` and applies a one-sided power-sum lemma and
Kronecker's theorem. Theorem NI adds the first-defect intertwiner and the
swap decomposition, both on main, and Lemma U. Theorem W uses a two-point
fibre (Baker–Barge–Kwapisz Thm 4.2) and the alignment of partners (Lemma 8
of the (F)-class note, valid for every determinant) to pin every strict
component to one minimal set; the rest follows from Perron–Frobenius, the
sieve on main and the first half of Barge's proof of Lemma 13. Lemma S+
reads the eventual range of Barge's ordered-pair substitution from his count
of periodic words and identifies the generator of `G_0` by Barge–Diamond's
proof; Theorem P+ is a degree count. Theorem H3 combines Lemma 9′ on `Ω_s`
with the twin involution and the argument of Lemma 10 of the (F)-class note
at `p = 2`. Obstruction T is the exact sequence of Barge–Diamond for the
child substitution against the spectrum of `Φ*` on `H¹(Ω_σ)`. What is prior
art and what is new is itemised in §11 of the proof note.

### Evidence and replay

```sh
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_fixed_point_count.mojo)
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_geometric_f.mojo)
```

The first regression compares the formula of Theorem FP with a literal
count for `n = 1, …, 6` on eleven substitutions. The second pins the class
counts: `dim H¹ = 3` on 3,102 corpus specimens, 1,362 of them with even
determinant; (F) and `dim H¹ = 3` on 1,350; of the 174 specimens with (F),
even determinant and two periodic letters on both sides, 42 have
`dim H¹ = 3` and 132 do not. Both were re-run on 2026-11-16 (exit 0). They
certify no coincidence rank, no strong coincidence and no spectrum. The
numbers are in the proof note, §12; figures that depend on the divisor
condition of Theorem P+ are scratch and are labelled there.

### Negative controls

From the literature: Thue–Morse has coincidence rank 2 (Barge Example 16)
and `dim H¹ = 2`, one more than the degree of its dilation, so the
hypothesis `l = 0` of Lemma 9′ and Theorem H3 cannot be dropped;
Baker–Barge–Kwapisz Example 5.3 (reducible, unit, `cr = 2`) shows that
irreducibility is needed; the Barge–Bruin–Jones–Sadun examples with
`cr = 3` and minimal cohomology bound what the argument of Lemma 10 can give
at `p = 3`; the substitution `a → aaaab, b → abbbb` (spectrum `{5, 3}`, a
coincidence at position 0) shows that an almost everywhere one-to-one factor
map can add an expanding eigenvalue to `H¹`, which is the phenomenon behind
Obstruction T. From the repository: the strict controls Thue–Morse,
`01/2/120`, `012/120/201`, `1/012/1`, `1/012/101`, `10/102/211` and its
reversal, C-D1 `011/120/2012`, C-D2 `010/1222/2012`, `1/0/22`, and the
productive PIP3 controls. The proof note states where each argument stops
on each of them. Two of them matter for the decision: on `10/102/211` the
conclusion of Theorem NI (a non-injective top track) is realised by an
actual strict system, so non-injectivity alone is no contradiction; on
`1/012/101` and C-D2 the top track is not injective although the cofactor
is neutral, so Theorem TT has no converse.

### Non-claims / remaining gaps

Universal C4; `cr ≠ 2` for `dim H¹ ≥ 4`; "at coincidence rank two `σ` is
unit and 3 divides the first defect degree"; "no strict system for nonunit
`σ` at coincidence rank two"; consistency of the necessary conditions with
each other; Theorem Fork for nonunit `σ` (expected, not proved); the
statement for general Pisot substitutions (a remark only); novelty relative
to the literature beyond "not found in the sources read". Anderson–Putnam
1998, Mignotte 1984 and Andress–Robinson were not read. The proofs of Barge
2015 Thm 4 were not followed, the rewriting references of its §4 were not
read, and the count of periodic words in the proof of its Thm 22 is used as
printed. The standard facts on line bundles, covering dimension and
`Ȟ¹ = [X, S¹]`, and the identification of the two coincidence ranks, were
not checked against a source on disk. The divisor condition of Theorem P+
is not implemented.

## Decision

**Proceed, narrowed; stop the transport route.**

- Record Theorem FP, Lemma U, Theorems TT, NI, W, Lemma S+, Theorem P+,
  Lemma 9′, Theorem H3 and Corollaries FC3+, N+ as written proofs
  conditional on the imports above, with the attributions of this note:
  Theorem FP to Anderson–Putnam, Lemma U to Mignotte, Lemma 9′ to
  Barge–Kellendonk–Schmieding, the parity mechanism to
  Barge–Bruin–Jones–Sadun, (W4) to Barge's proof of Lemma 13, the algebra
  of Theorem NI(1) and the sieve of (W3) to main. Claim novelty only as
  "not found in the sources read", and only for Theorem TT, Theorem NI(2)–(4),
  (W1), (W2), the link in (W3), and the even-determinant content of Lemma S+,
  Theorem P+ and Theorem H3.
- Record the exact fixed-point count and the class counts as canonical Mojo
  with regressions; cite no figure that depends on the unimplemented divisor
  condition.
- **Stop:** do not re-run the transport of the first-defect eigenvalue into
  Barge's `X − Y` (Obstruction T). Do not record "Lemma S and the defect
  intertwiner are jointly consistent".
- **Do not record** the generalisation of Theorem H3 to all homological
  Pisot substitutions beyond a remark; it would strengthen printed
  statements and needs its own gate and a second reader.
- Correct the two round-1 notes by dated updates: the row "none in print"
  of the round-1 gate, and the two sentences of §7 of the (F)-class note on
  unimodularity.
- Do not present any of this as a route to universal C4. What remains open
  at coincidence rank two is stated in §10 of the proof note; the cells with
  `dim H¹ ≥ 4` are untouched for even determinant, and the unit case with
  first-defect weights `(m, m, m)` is untouched by every tool of the round.
