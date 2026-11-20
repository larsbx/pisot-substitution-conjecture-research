# Review of the nonunit stack word rigidity, and what it gives at higher rank

**Status:** Independent check of the [stack word rigidity proof](c4-nonunit-stack-word-rigidity-2026-11-20.md)
(#633) against its imports, step by step. **No gap found**, with two clarifications on how
Barge's theorems are applied. The note then records a rank-free form of the core lemma and
the exact obligation it leaves in the nonunit case at coincidence rank three or more. This
is a written check by one reviewer. It is not machine-checked beyond the existing Lean
endpoints of #633, and it changes no claim status. Starting revision: `origin/main@4f32503`.

## Sources re-read

Barge, *Factors of Pisot tiling spaces and the coincidence rank conjecture*,
[arXiv:1301.7094](https://arxiv.org/abs/1301.7094), re-read for this review:

| Statement | Text (verbatim) | Used for |
| --- | --- | --- |
| Theorem 12, hypotheses | "Suppose that Φ is an n-dimensional Pisot family substitution that forces the border and has convex tiles. Suppose also that Ω_Φ does not have an almost automorphic sub action." | the stack substitution `Φ_s` with `Ω_{Φ_s} ≅ Ω_Φ/≈_s`, conjugating translation and substitution |
| §4, one dimension | "For one-dimensional substitutions, Ω_Φ has no almost automorphic sub action iff Ω_Φ does not have pure discrete spectrum." | the hypothesis holds whenever a strict system exists |
| §4, properness | "If ϕ is proper and Ω_Φ does not have pure discrete spectrum, ϕ_s is also proper." | the proper stack graph `S` |
| §4, the quotient map | "The natural map from X_ϕ to X_{ϕ_s}, taking the quotient by ≍_s, is induced by a morphism σ on letters" | `s : R → S` is a letter-to-word subdivision |
| Proposition 19 | "Suppose that ϕ is a proper Pisot substitution such that Ω_Φ does not have pure discrete spectrum. Then Σ* : H¹(Ω_{Φ_s}) → H¹(Ω_Φ) is injective." | stack spectrum inside the original spectrum |

None of these needs unimodularity, odd norm or coincidence rank two.

## Step audit of #633

| Step | Verdict |
| --- | --- |
| No pure discrete spectrum | Holds. A strict component projects onto `Ω`, so every tiling has a distinct fibre-mate. Then `cr ≥ 2`, which excludes pure discrete spectrum by Barge's Theorem 4(5). |
| Proper return presentation `R` and stack graph `S` | Holds, with clarification **C1**. Theorem 12 and §4 must be applied to the proper return substitution itself. It forces its border by properness, and §4 then gives a proper `ϕ_s` and a quotient induced by a morphism on letters. So `s` maps each return letter to a fixed stack word, independent of context. |
| Raw cuts in `R`; images in `S`; forward invariance | Holds. The letter morphism intertwines the inflations, so inflated inserted points are inserted points. Finitely many points are inserted, since `R` has finitely many subdivided vertices. |
| Edge spectra on `A`, `R`, `S` | Holds. The nonzero cycle spectrum equals the spectrum on rational `H¹` (wedge presentations; subdivision keeps the inverse limit). Barge–Diamond gives the eigenvalues of `M` and roots of unity for `Ω`. Proposition 19 puts the stack spectrum inside it. The vertex quotient carries only `0` and roots of unity. |
| Multiplicity of `β` and lengths in `ℓ(V)` | Holds. The left `β`-eigenspace of the stack edge operator is one-dimensional. A row over `K = ℚ(β₀)`, scaled by one raw letter length, puts every refined stack length in `ℓ(a)K = ℓ(V)`. |
| Graded lifts, Sylvester separation | Holds. A tensor eigenvalue of degree `j ≥ 2` has absolute norm `D^j`; edge eigenvalues have norm `0`, `1` or `D`, with `D > 1` exactly in the nonunit case. |
| Pullback uniqueness `ρ*g_A = g_R = s*g_S` | Holds. Uniqueness on `R` uses the same separation for `R`'s edge spectrum. |
| Equal stack image ⇒ equal raw products on `[a, b]` | Holds. The letter morphism makes the refined stack path over `[a, b]` a function of the stack tiling alone. |
| Equal products ⇒ equal words | Holds. The algebra map `X_a ↦ g_A(a) − 1` keeps the least nonzero homogeneous component of `E(u) − E(v)`. |
| Two distinct periodic partners | Holds, with clarification **C2**. Theorem NI(2) needs a swap-symmetric strict system. At rank two this is (W1). |
| (W4) and the final assembly | Holds, by `fixedTilings_eq_of_common_intervals`. |

**C1** and **C2** clarify how the imports are applied; they are not gaps. The Thue–Morse
and unit controls of #633 are confirmed: equal raw lengths, resp. a neutral tensor
eigenvalue, break exactly the separation steps above.

## Rank-free form

The core of #633 never uses the coincidence rank. Under its standing hypotheses
(primitive, irreducible Pisot cubic incidence, nonunit, not pure discrete), it proves:

**Lemma SR (stack rigidity).** Two tilings of `Ω` with the same image in `Ω/≈_s` agree
between any two common raw vertices.

**Corollary SR-P.** Two Φ-periodic fibre-mates whose eventual coincidence is dense are
equal.

*Proof.* Dense eventual coincidence of fibre-mates is the stack relation. Inflating two
coincidences, on either side of `0`, to a common multiple of the period gives common raw
vertices arbitrarily far in both directions. Lemma SR and
`fixedTilings_eq_of_common_intervals` finish. ∎

**Corollary (nonunit, any rank).** Suppose a nonunit PIP3 substitution has a strict system.
Then:
- some Φ-periodic tiling `T` has two distinct Φ-periodic partners `T′, T″`;
- every such pair of partners has a nonempty open interval of non-coincidence;
- the limit construction in the proof of (W4) then gives three pairwise strongly
  noncoincident fibre-mates, so `cr ≥ 3`.

*Proof.* A sink of the child graph is either swap-symmetric or disjoint from its swap.
Theorem NI(2), resp. NI(4), forces `|det M| = 1` when `π₁` is injective on periodic points.
In the nonunit case `π₁` is therefore not injective there. Partners are fibre-mates by (Z4).
Corollary SR-P rules out dense coincidence. The (W4) construction applies verbatim. ∎

For `cr = 2` this is #633's exclusion. For higher rank it isolates the obligation.

## The obligation at rank three or more

In the nonunit case a strict system is excluded once **two distinct periodic fibre-mates
with dense eventual coincidence** exist. At rank two, (W4) supplies them from any two
partners of one tiling. At rank `k ≥ 3` the (W4) argument yields only `k + 1` pairwise
noncoincident strands, which is no contradiction until `k + 1 > cr`. The next targets are:

1. **Density from multiplicity.** The zero fibre `F₀` is finite and periodic. If
   `|F₀| > cr`, two of its members share a tile (BBK Remark 4.3), and that coincidence set
   is open and invariant under `β^P`. Show that it is dense for some such pair. Corollary
   SR-P would then exclude every nonunit strict system with `|F₀| > cr`.
2. **The unit case at rank three or more** is untouched. Its Sylvester separation fails, as
   #633's unit control shows.

Neither target is attempted here.

## Non-claims

No new exclusion beyond #633 is claimed. Lemma SR and its corollaries rest on the written
graph and cohomology inputs of #633, now checked against Barge's text, and on one
reviewer's reading. Universal C4 and PSC remain open.
