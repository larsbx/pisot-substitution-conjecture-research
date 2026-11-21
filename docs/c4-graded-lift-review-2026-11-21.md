# Review of the graded lift and word separation in the nonunit stack argument

**Status.** Second-pass check of the [nonunit stack word rigidity](c4-nonunit-stack-word-rigidity-2026-11-20.md)
(#633) at the five points left as written mathematics after the
[text review](c4-stack-rigidity-review-2026-11-20.md) and the
[graph-spectrum review](c4-graph-spectrum-review-2026-11-21.md): the original letter
cuts, the literal path maps, the spectrum transfer, the existence of the correction at
each finite degree, and the compatibility of truncations. **No gap found.** Two of the
five points move from prose to Lean: the graded step and the word separation. The
argument needs one finite truncation per interval and no inverse limit. No claim status
changes: #633 stays a written proof with partial Lean support, independent human review
pending. Starting revision: `origin/main@8bbc05b`.

## Source decision

The proposed Lean increment is finite algebra: one step of a graded lift, and
injectivity of an ordered product on positive words.

- Barge (2015), §2 and §4, re-read for the hypotheses on the return substitution.
  "Pisot substitution" there means a self-similar substitution whose expansion is a
  Pisot number; irreducibility is a separate adjective. The "proper version" of §4 is
  the return-word recoding at a seam `b|a` with `φⁿ(a) = a…`, `φⁿ(b) = …b`. So
  Proposition 19 applies to the proper return substitution although its matrix is
  reducible. Its proof maps the eventual range of `(f_φ)_*` on `H₁(X_φ)` onto that of
  `(f_{φ_s})_*`. [Barge, arXiv:1301.7094](https://arxiv.org/abs/1301.7094)
- The ordered expansion `a ↦ 1 + X_a` and its injectivity are classical (Magnus).
  The coefficient of a word `x` in `∏(1 + X_{w_i})` is the number of occurrences of `x`
  as a scattered subword of `w`. [Fenn–Sjerve, §4](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/D2D3FEEB1C2D7AE1A7EB6B9BD792CAF7/S0008414X00022501a.pdf/basic-commutators-and-minimal-massey-products.pdf);
  Lothaire, *Combinatorics on Words*, Chapter 6 (subwords, binomial coefficients of
  words, Magnus transformation).
- Sylvester's equation with disjoint spectra: Horn–Johnson, Theorem 2.4.4.1, as in #633.

**Decision.** Proceed. Nothing here is new mathematics; the novelty stays with #633's
specialization. The increment is restricted to the step and the separation, stated so
that no completed graded object is needed.

## Work shown

### Assumptions and hypotheses

Those of #633: `σ` primitive on three letters, irreducible Pisot cubic incidence `M₀`,
`|det M₀| ≥ 2`, coincidence rank two, a strict system assumed. `M = M₀ᵖ`, `β = β₀ᵖ`,
`V = ℚ³` with letter basis `X_a`, `ℓ : V → ℝ` the injective length map. `A`, `R`, `S`
are the raw wedge, the refined proper return graph and the refined stack graph, with
edge operators `B_A = M`, `B_R`, `B_S`, and edge-path maps `ρ : R → A`, `s : R → S`.
Imports: Barge's Theorem 12, §4 and Proposition 19; Barge–Diamond's exact sequence;
(W1), (W4) and NI(2) of the [rank-two wall note](c4-rank-two-wall-2026-11-16.md).

### Derivation / reduction

**R1. Original letter cuts.** `U_R` is the return vertex together with every raw letter
boundary inside a return petal. It is finite. `f_R(U_R) ⊂ U_R` because the image of a
raw letter is a raw word and the return parsing cuts only at raw boundaries. A refined
edge of `R` is one raw letter occurrence, so `ρ` is a map of edges to edges and
`ρ(f_R(e)) = σᵖ(ρ(e))` as lists. `U_S = V(S₀) ∪ s(U_R)` is finite and
`f_S(s(u)) = s(f_R(u))` puts it in `U_S` again. Both checks hold.

**R2. Literal path maps.** Barge's quotient is induced by a morphism `σ_s` on return
letters, and `Σ ∘ Φ = Φ_s ∘ Σ` on tilings. For a tiling with a return tile `r` on
`[0, ω_r]`, both `σ_s(φ(r))` and `φ_s(σ_s(r))` tile `[0, βω_r]` in the same stack
tiling, so the two words are equal, not merely conjugate. Hence
`s ∘ f_R = f_S ∘ s` as monotone maps of the wedges. A monotone path between points of
`U_S` has exactly one refined edge list, so the identity holds on edge lists. This is
the hypothesis `hcomm` of `pullback_equivariant`. For common raw vertices `a < b` of
`T, T′`, the point `a` is the image of a point of `U_R` in either lift, so it is a mark
of `q(T) = q(T′)`. The refined edge list of the marked stack tiling on `[a, b]` is a
function of the stack tiling and the two endpoints. Both return paths map to it. This
is the hypothesis `h` of `same_stack_interval_products_eq`.

**R3. Spectrum transfer.** The argument uses the *sets* of edge eigenvalues, three
times: existence on `A` (`M` against `M^⊗j`), existence on `S`, uniqueness on `R`.
Multiplicity is used once, for `β` on `S`, to put stack lengths in `ℓ(V)`. With
`edge_charpoly_factor`, an edge eigenvalue is a cycle eigenvalue or a vertex
eigenvalue, the latter `0` or a root of unity. Nonzero cycle eigenvalues of `R` are
those of inflation on `H¹(Ω; ℚ)`, which Barge–Diamond gives as eigenvalues of `M`
and `1`. The surjection of eventual ranges in the proof of Proposition 19 is
`(f_σ)_*`, which intertwines `(f_φ)_*` and `(f_{φ_s})_*`; so every nonzero cycle
eigenvalue of `S` is one of `R`. The Pisot hypothesis of Proposition 19 is on the
dilation alone and holds for the return substitution. The transfer holds.

**R4. The correction at each finite degree.** Fix `r ≥ 1` and labels `g_r` on the edges
of a graph `G ∈ {A, R, S}` in `T≤r(V)`, with constant term one, satisfying
`g_r(f(e)) = T≤r(M) g_r(e)`. Read them in `T≤r+1(V)` with zero top component. Let
`j : V^⊗(r+1) → T≤r+1(V)` be the inclusion of the top layer. Then

| Hypothesis of `graded_step_exists_unique` | Source |
| --- | --- |
| `base a · j t = j t = j t · base a` | constant term one; positive degrees annihilate the top layer |
| `j s · j t = 0` | `2(r+1) > r+1` |
| `F (j t) = j (D t)` with `D = M^⊗(r+1)` | `T(M)` is graded |
| `pathProduct base (f e) + j(res e) = F(base e)` | the equation holds in degrees `≤ r`, so its defect is in the top layer |
| `p(B) = 0`, `p(D)` injective | `p = χ_B` by Cayley–Hamilton; `χ_B` and `χ_D` are coprime by `tensor_norm_separates`, so Bézout inverts `χ_B(D)` |

The theorem returns exactly one top-layer correction `d` with
`g_{r+1} = g_r + j ∘ d` equivariant. Induction on `r` gives existence and uniqueness
at every finite degree, given the degree-one labels.

Degree one is not a Sylvester step. There `D₁ = M` and `B` share `β`, and on `A` the
homogeneous equation `MC − CM = 0` has `C = I` as a solution. The degree-one labels
are supplied by the lengths and are prescribed to agree under `ρ` and `s` by
injectivity of `ℓ`. Uniqueness in `ρ* g_A = g_R = s* g_S` is uniqueness of the higher
components over those fixed labels. #633 states this; it is the one place where the
construction is geometric rather than spectral.

**R5. Truncations.** `g_{r+1}` restricts to `g_r` by construction: the correction lies
in the kernel of `T≤r+1 → T≤r` (`step_truncates`). So the labels at different levels
are compatible, and uniqueness at each level makes the choice canonical. No inverse
limit of the `T≤r` is formed anywhere. For an interval `[a, b]` with raw words `u, v`,
put `N = max(|u|, |v|)`. The labels `g_N` on `A`, `R`, `S` are finitely many rational
tensors. R2 gives `g_N(u) = g_N(v)` in `T≤N(V)`. `word_separation` then gives `u = v`:
for labels `1 + X_a + (degree ≥ 2)`, the coefficient of a word `x` in the product
along `w` is the number of occurrences of `x` as a scattered subword of `w`, plus a
term determined by the occurrence counts of strictly shorter words. Strong induction
on `|x| ≤ N` equates all counts for `u` and `v`; the counts of `u` and of `v`
themselves make each a scattered subword of the other. `pathProduct_congr_above`
shows that coefficients of degree at most `N` depend only on the labels to degree
`N`, so computing in the free algebra with any representatives is computing in
`T≤N(V)`. `N` depends on the interval. No uniform truncation is needed, because each
interval is handled separately and `fixedTilings_eq_of_common_intervals` assembles
them.

### Evidence and replay

New module [PeriodicPartnerGradedLift](../proof/PscVerif/PscVerif/PeriodicPartnerGradedLift.lean).

| Lean endpoint | Checked step |
| --- | --- |
| `step_iff`, `constr_sylvester` | With lower labels fixed, the top-layer inflation equation is `D(d e) − Σ_{e′ ∈ f(e)} d(e′) = −res(e)`, the Sylvester equation for the edge operator `edgeOp` |
| `graded_step_exists_unique` | Exactly one top-layer correction, under the hypotheses tabulated in R4 |
| `step_truncates` | The corrected labels restrict to the lower labels under any ring map killing the top layer |
| `pathProduct_one_add`, `pathProduct_leading`, `coeff_pathProduct` | Expansion over scattered subwords; the product of nonconstant parts along `m` is `m` plus higher degree |
| `pathProduct_congr_above` | Changing labels above degree `N` changes products only above degree `N` |
| `word_separation` | Agreement of all coefficients of degree `≤ N`, with both words of length `≤ N`, forces equal words |
| `degree_two_control` | `abba` and `baab` have equal scattered-subword counts through length two |

The word model is `MonoidAlgebra ℚ (FreeMonoid α)`, the free associative algebra on the
letters. Axioms: `propext`, `Classical.choice`, `Quot.sound`.

```sh
cd proof/PscVerif
lake build PscVerif.PeriodicPartnerGradedLift
lake env lean PeriodicPartnerAudit.lean
cd ../..
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
```

### Negative controls

| Control | Result |
| --- | --- |
| `degree_two_control` | Truncation at degree two does not separate `abba` from `baab`. The truncation must reach the first differing scattered-subword count; `N = |u|` always suffices. |
| Degree one on the raw graph | `MC − CM = 0` has `C = I`. The Sylvester step cannot produce or pin the degree-one labels; without the length map the lift is not unique. |
| `equal_letter_labels_control` (#633) | With equal degree-one labels the hypothesis `Above 2 (k a − X_a)` fails and `01`, `10` have equal products (Thue–Morse). |
| Unit cubic (#633, #637) | `χ_B(D_j)` is singular in degree three or six, resp. four or seven on raw edges, so the hypothesis `p(D)` injective fails. |

### Non-claims / remaining gaps

Still written, not in Lean: that `T≤r+1(V)` with `T(M)` satisfies the tabulated
hypotheses; that coprime characteristic polynomials make `χ_B(D)` injective; the
graphs, cuts and path identities of R1–R2; the cohomology spectrum of R3 and its
imports; the Galois-norm identification; (W1), (W4), NI(2) and their upstream inputs.
This note is one reviewer's reading and does not replace independent human review.

Scope is unchanged from #633: finite strict systems at nonunit coincidence rank two,
including even determinant. Higher coincidence rank, the unit case, and the extraction
of a finite strict carrier from an arbitrary failure of pure discreteness are outside
it. The balanced-pair route does not depend on any of this.

## Reporting

Report the even-determinant rank-two residue as: *excluded by a written proof (#633)
whose finite algebra, path bookkeeping, graded step and word separation are checked in
Lean; graph construction, cohomology spectrum, norm identification and assembly
written and twice re-read; independent human review pending.* It is not a completed
formal theorem and must not be reported as one.
