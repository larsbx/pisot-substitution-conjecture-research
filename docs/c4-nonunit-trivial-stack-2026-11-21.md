# The stack relation is trivial for nonunit ternary Pisot hulls

**Status:** Written proof, single prover, no independent verifier, not machine-checked. It
builds on the written stack rigidity of [#633](c4-nonunit-stack-word-rigidity-2026-11-20.md),
as [reviewed](c4-stack-rigidity-review-2026-11-20.md), and on Barge's text re-read verbatim.
Barge's twin structure then applies to every nonunit rank-two hull, and the rank-two
carrier question reduces to whether twins share a vertex. No strict system is assumed
anywhere. No governed claim changes. Starting revision: `origin/main@4f32503`.

## Sources

Barge, *Factors of Pisot tiling spaces and the coincidence rank conjecture*,
[arXiv:1301.7094](https://arxiv.org/abs/1301.7094):

| Statement | Text (verbatim) |
| --- | --- |
| Definition of `≈_s` (§3) | "We will write T ≈_s T′, provided {v : T − v ∼_s T′ − v} is dense in ℝⁿ and g(T) = g(T′)." |
| Theorem 4(3) | "T ∼_s T′ if and only if there is k ∈ ℕ with B₀[Φᵏ(T)] = B₀[Φᵏ(T′)]." |
| Theorem 4(7) | "If T − v ∼_s T′ − v for all v ∈ ℝⁿ, then T = T′." |
| Theorem 12(3) | "Ω_{Φ_s} is homeomorphic with Ω_Φ/≈_s by a homeomorphism that conjugates both translation and substitution dynamics" |
| Lemma 13 | "Suppose that Ψ is an n-dimensional Pisot family substitution with cr(Ψ) = 2 and suppose that ≈_s is trivial on Ω_Ψ. Then for each T ∈ Ω_Ψ there is a unique T′ ∈ Ω_Ψ with the properties: T and T′ are regionally proximal and T ∩ T′ = ∅." Its proof gives `Ψˡ(T) ∩ Ψˡ(T′) = ∅` for all `l`. |
| Lemma 14 | "…with cr(Ψ) = 2 and suppose that ≈_s is trivial on Ω_Ψ. Then Σ_op : Ω_Ψ → Ω_{Ψ_op} is an isomorphism." |
| Theorem 17 | "Suppose that Ψ is an n-dimensional Pisot family substitution that forces the border with cr(Ψ) = 2 and suppose that ≈_s is trivial on Ω_Ψ. Then Σ_p : Ω_Ψ → Ω_{Ψ_p} is a 2-to-1 covering map that semi-conjugates the dynamics, Ω_{Ψ_p} is a Pisot family substitution tiling space whose ℝⁿ-action has pure discrete spectrum…" |

The repository input is Lemma SR of the review: under #633's standing hypotheses, two
tilings with the same image in `Ω/≈_s` agree between any two common vertices.

## Work shown

### Assumptions and hypotheses

`σ` is a primitive substitution on three letters whose incidence matrix has an irreducible
Pisot characteristic polynomial and determinant other than `±1`. Its hull `Ω` does not have
pure discrete spectrum, equivalently `cr(σ) ≥ 2` (Barge, Theorem 4(5)). The proper return
presentation forces the border, so Theorem 12 applies. Lemma SR is used as written in #633.
It rests on Barge's Theorem 12, the §4 letter morphism and Proposition 19.

### Derivation / reduction

**Theorem T (trivial stack relation).** Under these hypotheses `≈_s` is trivial on `Ω`. So
`Ω/≈_s = Ω`, and `Ω` is its own stack substitution space.

*Proof.* Let `T ≈_s T′`. For `k ≥ 0` put

```text
J_k = { v : Φᵏ(T) and Φᵏ(T′) have the same tiles at βᵏ v }.
```

1. **Density.** By the definition and Theorem 4(3), `⋃_k J_k ⊇ D`, where
   `D = {v : T − v ∼_s T′ − v}` is dense. Indeed `Φᵏ(T − v) = Φᵏ(T) − βᵏv`.
2. **Monotonicity.** Inflating a common tile gives a common patch, so `J_k ⊆ J_{k+1}`.
3. **Convexity.** `Φᵏ(T)` and `Φᵏ(T′)` have the same stack image, by the conjugacy of
   Theorem 12(3). Let `v₁ < v₂` be in `J_k`. The tiles at `βᵏv₁` and `βᵏv₂` are common, so
   their outer endpoints are common vertices. Lemma SR makes `Φᵏ(T)` and `Φᵏ(T′)` agree
   between them, so `[v₁, v₂] ⊆ J_k`. Each `J_k` is an interval.
4. **Exhaustion.** An increasing union of intervals is an interval, and an interval
   containing a dense subset of ℝ is ℝ. So every `v` lies in some `J_k`, which means
   `T − v ∼_s T′ − v` for all `v`.
5. Theorem 4(7) gives `T = T′`. ∎

Step 3 is the only use of the nonunit hypothesis, through Lemma SR's spectral separation.

**Corollary T2 (twins at rank two).** If moreover `cr(σ) = 2`:

- every `T ∈ Ω` has a unique twin `ι(T)`, regionally proximal to `T`, with
  `Φˡ(T) ∩ Φˡ(ι(T)) = ∅` for all `l` (Lemma 13);
- `T ↦ (T, ι(T))` is an isomorphism onto the ordered overlap tiling space `Ω_op` of
  finitely many overlap tiles (Lemma 14);
- `Ω → Ω_p` is a two-sheeted covering onto a hull with pure discrete spectrum, and `ι` is
  its deck involution (Theorem 17).

No strict system is assumed. The rank-two structure that #619 and #633 derived from a
strict system holds for every nonunit rank-two hull.

**Proposition V (twins share a vertex ⇒ a finite strict system).** Under Corollary T2,
suppose some `T` and `ι(T)` have a common vertex. Then `σ` has a finite strict system.

*Proof.*
1. A common vertex is a point that is a vertex of both coordinates of the overlap tiling
   `(T, ι(T))`, so it is visible in a finite overlap patch.
2. `Ω_op ≅ Ω` is minimal with finite local complexity, hence repetitive. Common vertices
   therefore recur along `(T, ι(T))` with bounded gaps, and likewise in every pair
   `(U, ι(U))`.
3. Let `C` be the set of word pairs read between consecutive common vertices of pairs
   `(U, ι(U))`.
   - Each is balanced: both words have the same length, and the length map is injective on
     ℚ³ for irreducible incidence.
   - Each is irreducible: a balanced interior cut is an equal-length position, hence a
     common vertex.
   - Each is noncoincident, by Lemma 13.
   - `C` is finite, by bounded gaps and finite local complexity.
   - `C` is closed under children, because `ι` commutes with `Φ` and the blocks of
     `(σu, σv)` are read between consecutive common vertices of `(Φ(U), ι(Φ(U)))`.

So `C` is a strict system. ∎

**Corollary V.** For nonunit `σ` with `cr(σ) = 2`, twins never share a vertex. Otherwise
Proposition V gives a strict system, which the written rank-two exclusions rule out: #633
for every nonunit determinant, and #617 at odd determinant.

So the nonunit rank-two case, **without assuming a strict system**, reduces to one
geometric statement: show that some tiling and its twin share a vertex. A natural place to
look is the zero fibre. `ι` permutes `F₀`, and by Corollary V it would send every
vertex-type member, with a vertex at the origin, to an interior-type member.

### Evidence and replay

This is a written argument with no new executable or formal component. Its formal anchors
are those of #633 (`PeriodicPartnerStackWordRigidity`) and the existing strict-system
modules. Barge's statements above were read from the arXiv PDF. Replay of the repository
checks:

```sh
python3 tools/make_proof_bank.py --check
PYTHONPATH=tools python3 -m claim_governance.cli --root .
```

### Negative controls

- **Thue–Morse** is not irreducible (equal tile lengths). Its stack relation is trivial and
  its twins share every vertex, since complementary tilings have the same cuts. Proposition
  V's strict system `{(01,10),(10,01)}` exists there. Theorem T and Corollary V need
  irreducible incidence: Lemma SR, and balancedness from equal length, both use it.
- **Unimodular cubics** fall outside Lemma SR's spectral separation (#633's unit control).
  Theorem T is not claimed for them.

### Non-claims / remaining gaps

1. **Twin vertices.** Whether a twin pair can be vertex-disjoint in a nonunit rank-two hull
   is open. Showing that some pair shares a vertex would complete the nonunit rank-two case
   of PSC on three letters, conditionally on the written inputs.
2. **Higher rank.** Theorem T holds at every rank, but Barge's twin structure (Lemmas
   13–14, Theorem 17) is specific to `cr = 2`. A trivial stack relation at `cr ≥ 3` yields
   no exclusion here.
3. **Unit determinant.** Not covered.
4. **Review.** Every step inherits #633's written graph and cohomology inputs. Universal
   C4 and PSC remain open.
