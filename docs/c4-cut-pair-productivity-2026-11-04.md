# C4 productivity: cut pairs, strong coincidence and a positive-measure subtile overlap

**Status:** repository-proved combinatorial reduction (Theorem A) and measure
reductions (Theorems B, C) resting on the fixed-lattice box count, which has a
written proof in §8 (automated adversarial audits of 2026-11-04: holds); human
review pending for all of them. The one-pair subtile statement in §4 is proved there
(Lemma P, unimodular case); the all-pair statement is cited from Arnoux–Ito
Thm 2. No change to C4, BH (#139), A1′ (#138), G1 or PSC status.
[Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
Baseline `main@ad164fc` (merged #476).

## 1. Stop/go literature check

*Proposed claim.* A strict C4 component of a PIP substitution forces a
Lebesgue-positive overlap `λ(R_c ∩ R_c') > 0` of two Rauzy subtiles, for a
letter pair `{c,c'}` that labels its balanced cuts.

*Prior art.*
- [Arnoux–Ito 2001](https://projecteuclid.org/journals/bulletin-of-the-belgian-mathematical-society-simon-stevin/volume-8/issue-2/Pisot-substitutions-and-Rauzy-fractals/10.36045/bbms/1102714169.pdf):
  strong coincidence on **all letter pairs** makes both subtile families
  measure-disjoint (unit case, Thm 2). A single positive (prefix) strong
  coincidence pair already nulls the overlap of the **primed** pair, and the
  primed family is the positive-prefix `R_c` used here, up to sign (§4,
  Lemma P). The paper records as open whether a unit Pisot substitution
  fails strong coincidence.
- [Minervino–Thuswaldner 2014](https://arxiv.org/abs/1402.2002): the same
  result for non-unit substitutions, on the adelic representation space.
- [Akiyama–Lee](https://ar5iv.arxiv.org/html/1403.0377): overlap coincidence
  implies strong coincidence when the height group is trivial.
- [Barge–Diamond 2002](https://www.numdam.org/item/BSMF_2002__130_4_619_0/):
  some letter pair is always coincident; all pairs are coincident on two
  letters.
- Model-set uniform distribution (Moody, *Uniform distribution in model sets*,
  Canad. Math. Bull. 45 (2002)) is background only. The fixed-origin
  regular-box count actually used in §3 is proved in §8.

*What transfers.* Measure-disjointness is known under strong coincidence.
Unconditional measure-disjointness of the subtiles was not found in any of
these sources.

*Decision.* **Proceed, narrowed.** The density argument behind Theorem B is
the standard "noncoincidence gives double covering" mechanism, specialised to
the *aligned* overlaps that sit at balanced cuts. Novelty is claimed only for
that specialisation and its quantitative bound, not for the mechanism.

## 2. Theorem A — a strict system has no strong coincidence on its cut pairs (with a conditional finite-sink converse)

Let `σ` be nonerasing on `{0,1,2}`. Items 1–5 below use only this and the
definition of a strict system; the arithmetic hypotheses on `ℓ` enter from
Theorem B on. Let `C` be a finite nonempty set of ordered irreducible noncoincident balanced
pairs, strictly child-closed: every factor of the complete balanced
factorisation of `σ(S)`, for `S ∈ C`, lies in `C`. Define the **cut-pair set**

```text
A(C) = { {u_0, v_0} : (u,v) ∈ C }   (unordered letter pairs).
```

**Theorem A.**
1. Every state has `u_0 ≠ v_0`. Hence `A(C)` is a nonempty set of off-diagonal pairs.
2. Every **proper** balanced cut of every inflation `σ^n(S)`, `S ∈ C`,
   is followed by the two letters of a pair in `A(C)`.
3. `(g×g)(A(C)) ⊆ A(C)` and `g(c) ≠ g(c')` on `A(C)`, where `g(a)` is the
   first letter of `σ(a)`.
4. No pair of `A(C)` is left strongly coincident.
5. Conditional finite-sink realisation. Suppose `σ` has a balanced pair `T` that never produces a
   coincident factor in any inflation, and suppose the set of irreducible
   factors reachable from `T` is finite. Then a strict `C` exists. This is a
   **conditional finite-sink converse**, not an equivalence between absence
   of pairwise strong coincidence and nonproductivity.

*Proof.*
1. If `u_0 = v_0`, the prefixes of length one balance, so irreducibility
   forces `|u| = 1`. Then `(u,v)` is a coincidence, which is excluded.
2. By induction on `n`, the complete factorisation of `σ^n(S)` is the
   concatenation of the factorisations of the `σ`-images of the factors of
   `σ^{n-1}(S)`. A balanced factorisation of a concatenation of balanced words
   is the concatenation of their factorisations. So every factor lies in `C`,
   and the letters after a cut are the first letters of a state.
3. The first factor of `σ(u,v)` is a state of `C` by strict closure and
   begins with `(g(u_0), g(v_0))`; by (1) these letters differ, and the pair
   lies in `A(C)`.
4. A *left strong-coincidence witness* for `{c,c'}` is `σ^n(c) = P x Q`,
   `σ^n(c') = P' x Q'` with `p(P) = p(P')`; this forces `|P| = |P'|`. Take a
   state `(u,v)` and, after a track swap, `u_0 = c`, `v_0 = c'`. In
   `σ^n(u,v)`, the index `|P|` (possibly 0) is balanced on both tracks, and so
   is `|P|+1`. They bracket the factor `(x,x)`, which lies in `C` by the
   factor-closure induction in the proof of (2). This contradicts
   strictness.
5. The irreducible factors of all inflations of `T` form a finite set `F`.
   By the concatenation lemma in (2), `F` is closed under children, and it
   has no coincidence, so `F` is already strict. In particular every sink
   strongly connected component of its child graph is strict. ∎

Items 1–4 are in the repository already, implicitly: the aligned branch of
the bad-SCC dichotomy, and the enclosure note's "carrier with aligned first
pairs". This note isolates them as a single interface, because it is where
Theorem B attaches.

## 3. Theorem B — a strict system forces a positive-measure subtile overlap

Assume in addition that `σ` is primitive with irreducible Pisot incidence,
positive Perron lengths `ℓ` (`ℓM = βℓ`, `β > 1`; the entries of `ℓ` are
ℚ-independent). Let `E^s` be the contracting plane and `π` the projection onto
it along the Perron line.

*Powers.* Strict closure passes to `σ^q` and `A(C)` is unchanged; Theorem A(3)
then holds with `g^q`. Left strong coincidence is power-invariant, because a
witness persists under further inflation. A strict system exists for `σ` iff
one exists for `σ^q` (take the factors of `σ^r(C)`, `r < q`). So we may replace
`σ` by a power `σ^q` with a one-sided fixed point `w`; below `β` and `M` denote
those of the power where it matters, and Step 1 does not depend on the choice
of `(q, w)`. Define

```text
R_c = closure { π p(P) : P c is a prefix of w } ⊂ E^s   (compact),
Z_A = ⋃_{ {c,c'} ∈ A(C) } (R_c ∩ R_c').
```

Fix Lebesgue measure `λ` on `E^s` in a chosen basis. Let `Φ(y) = (ℓ·y, π y)`
and let `κ = |det Φ|`, the covolume of `Φ(Z³)` for `dt ⊗ λ`, computed in that
same basis of `E^s`. Let `L_max` be the largest
physical length `ℓ·p(u)` of a state in `C`.

**Theorem B.** `λ(Z_A) ≥ κ / L_max > 0`. In particular `λ(R_c ∩ R_c') > 0` for
some cut pair `{c,c'}` of `C`.

*Proof.* Fix `S = (u,v) ∈ C` and write `L = ℓ·p(u)`.

*Step 1 — cuts project near both subtiles.* Let `x ∈ Z³` be the common Parikh
prefix at a cut of `σ^n(S)`, followed by `c` on top and `c'` on the bottom.
Write `x = p(σ^n(u[:k])) + p(Q)`, where `Q c` is a prefix of `σ^n(u_k)`. Every
letter `d` occurs in `w` after some fixed prefix `Y_d`, so `σ^n(Y_d) Q c` is a
prefix of `w`. Therefore

```text
dist(π x, R_c) ≤ ‖M_s^n‖ · |π(p(u[:k]) − p(Y_d))| ≤ ε_n,
ε_n := ‖M_s^n‖ · max{ |π(p(z[:k]) − p(Y_d))| : S ∈ C, z ∈ {u_S, v_S}, 0 ≤ k < |z|, d ∈ {0,1,2} },
```

a finite maximum, so the bound is uniform over all cuts, and `‖M_s^n‖ → 0`
because `ρ(M_s) < 1` (Pisot). (The previous display bounded the difference by
the larger of the two norms, which is false in general.) The same argument on the bottom track
gives `dist(π x, R_c') ≤ ε_n`. By Theorem A(1,2), `{c,c'} ∈ A(C)`.

*Step 2 — counting.* Distinct cuts have distinct `x`, since `ℓ·x` increases
strictly, and `0 ≤ ℓ·x < β^n L`. Every factor has length at most `L_max`, so
the number of cuts is `r_n ≥ β^n L / L_max`.

*Step 3 — the measure bound.* `Z_A` is compact. Take any open `U ⊃ Z_A` that
is a finite union of boxes. By compactness, for large `n` the `ε_n`-
neighbourhoods of `R_c` and `R_c'` meet only inside `U`, for every pair in
`A(C)`. So every cut has `π x ∈ U` and `ℓ·x ∈ [0, β^n L)`. `Φ(Z³)` is a
lattice. `π` is injective on `Z³` with dense image, because `χ_M` is
irreducible. Uniform distribution for this cut-and-project scheme then gives

```text
#{ y ∈ Z³ : π y ∈ U, 0 ≤ ℓ·y < X } = X λ(U)/κ + o(X).
```

Hence `L/L_max ≤ L λ(U)/κ`. The infimum of `λ(U)` over such `U` equals
`λ(Z_A)`, by outer regularity of a compact set. ∎

Unimodularity was not used. When `|det M| ≥ 2`, however, the Euclidean
subtiles are expected (heuristically; not proved here) to overlap with
positive measure anyway, so Theorem B remains valid but is likely
non-exclusionary there. The natural
replacement is the adelic representation space of Minervino–Thuswaldner. That
version is **not** proved here.

Let `N_{T,S}` be the number of occurrences of `T` in the complete
factorisation of `σ(S)` (with multiplicity) and `P` the matrix of state Parikh
columns. `PN = MP` gives `L^T N = β L^T` with `L_S = ℓ·p(u_S)`, so `β` is the
Perron root of `N`. When `N` is primitive with right Perron vector `z`,
`r_n/β^n → L/L̄` with `L̄ = (ℓPz)/(1^T z)` the Perron-weighted mean state
length, giving the sharper bound `λ(Z_A) ≥ κ/L̄` (for irreducible `N` use
Cesàro averages).

**Corollary B′ (productivity from disjointness).** If the subtiles of the
pairs in `A(C)` are pairwise measure-disjoint, `C` cannot exist. In particular:
if `R_c, R_c'` are measure-disjoint for every pair `{c,c'}`, then `σ` has no
strict C4 system.

## 3a. Theorem C — a strict system can occupy at most half of each subtile's lattice

Keep the hypotheses of Theorem B. Let `f` be the letter-frequency probability
vector, so `f` is the Perron right vector of `M` normalized to `|f|₁ = 1`.
Let `ℓ̄ = ℓ·f` be the mean letter length. Define the **occupancy** of letter `c`:

```text
θ_c = κ f_c / (ℓ̄ λ(R_c))  ∈ (0, 1].
```

The same count as below, applied to the `c`-vertices of prefixes of `w` (which
lie in `R_c` itself), gives `λ(R_c) ≥ κ f_c/ℓ̄ > 0` unconditionally, so `θ_c` is
well defined and `θ_c ≤ 1`. `θ_c` is a lower bound for the liminf of the
fraction of lattice points over `R_c` that are `c`-vertices of the fixed point;
the two agree when `λ(∂R_c) = 0`.

**Theorem C.** If a strict system `C` exists, then `θ_c ≤ 1/2` for every
letter `c`. Contrapositively, `θ_c > 1/2` for a single letter excludes every
strict C4 system of `σ`.

*Proof.* Fix `S = (u,v) ∈ C`, `L = ℓ·p(u)`, and a letter `c`.
1. Every occurrence of `c` on the top track `σⁿ(u)`, at index `i`, gives the
   lattice point `y = p(σⁿ(u)[:i])`, with `ℓ·y ∈ [0, βⁿL)`. Step 1 of
   Theorem B applies verbatim to any prefix, not just to cuts. So `πy` lies
   within `ε_n` of `R_c`. The same holds on the bottom track.
2. Within one track the points are distinct.
3. Across tracks they are distinct too. A shared point has the same index
   `i = |y|₁` (possibly 0) and the same Parikh vector on both tracks, so `i` is
   balanced and followed by `(c,c)`. Then `i` and `i+1` are both balanced, so
   `σⁿ(S)` has the coincident factor `(c,c)`, contradicting strictness (every
   factor lies in `C`).
4. This gives `2·#_c(σⁿ(u))` distinct lattice points in the cylinder over
   `N_{ε_n}(R_c)`. Their count satisfies `#_c(σⁿ(u)) / βⁿL → f_c / ℓ̄`, by
   Perron–Frobenius for `M`.
5. Take an open box-union `U ⊃ R_c` with `λ(U) < λ(R_c) + δ`. The
   fixed-lattice regular-box count of §8, as used in Theorem B, gives `2 f_c/ℓ̄ ≤ (λ(R_c) + δ)/κ` for every
   `δ > 0`. ∎

*Dependencies.* Theorem A(1) together with the factor closure from the proof
of A(2), including the cut at index 0; Theorem B Step 1; Perron–Frobenius
asymptotics for `M`; passage to `σ^q`; the §8 count. Theorem C imports nothing
from Arnoux–Ito and inherits the review status of §8.

*Reading.* Unimodularity is not used. The strict system is used only to make
the two tracks' `c`-vertex sets disjoint. This is the classical
"noncoincidence gives double covering" mechanism; the novelty claimed is only
its appearance as a two-line consequence of Theorem A(1).

*Unit case.* By the equality step in the proof of Lemma P (§4),
`λ(R_c) = s f_c` for some `s > 0`, so `θ_c = κ/(ℓ̄ s)` does not depend on `c`:
"for a single letter" means "for every letter". Conditionally on imports,
`d_cov = ℓ̄ s/κ`, `θ_c = 1/d_cov` and `θ_c > 1/2 ⇔ d_cov = 1 ⇔ PDS`, where
`d_cov` is the covering degree. The imports are the self-replicating multiple
tiling of degree `d_cov` (Siegel–Thuswaldner 2009 Prop. 3.7;
Minervino–Thuswaldner 2014 Thm 9.2), the regular-model-set density of its
type-`c` translations, and tiling ⇔ super coincidence ⇔ PDS
(Siegel–Thuswaldner Thm 3.20; Akiyama–Barge–Berthé–Lee–Siegel 2015 Thm 5.2).
None is reproved here. All of these were reported by the 2026-11-04 audit
workflow and **not read** for this note; Ito–Rao 2006 and Barge–Kwapisz 2006
were read by no one.
Under those imports the contrapositive of Theorem C is exactly "PDS ⇒ no strict
system", which is already available from Theorem A(4) and Akiyama–Lee 2014
Cor. 4.5 (abstract and statement read, proof not). The novelty is limited to the elementary two-track proof, and the
occupancy route is **retired as a C4 attack** in the unit case (it has PDS
strength). Model-set statements hold up to a density-zero set.

## 4. Source-audited subtile comparison (convention corrected 2026-11-04)

*Convention dictionary.* Arnoux–Ito (2001, Def. 6, Lemma 1) build the primed
domains `D_n(i)'` from `E1*(σ)^n(0, e_i*)` and the unprimed `D_n(i)` from
`E1*(σ)^n(−e_i, e_i*)`. Iterating Lemma 1,
`E1*(σ)(x, e_i*) = Σ_{j,k: W_k^{(j)} = i} (M^{-1}(x − f(P_k^{(j)})), e_j*)`,
shows that the faces of `E1*(σ)^n(0, e_i*)` have base points `−M^{-n} f(Q)`, one
for each occurrence `σ^n(l) = Q i S`. Renormalising by `M^n` gives, as
Hausdorff limits,

    X(i)' = −R_i,      X(i) = −(R_i + π e_i)   (the suffix family).

So the positive-prefix `R_c` of §3 is, up to the measure-preserving map
`x ↦ −x`, the Arnoux–Ito **primed** family. The previous revision of this
section called `R_c` "unprimed"; that label was wrong, and the withdrawal it
motivated is reversed below **in the unimodular case only**.

**Lemma P (unimodular, one pair).** Let `σ` be primitive with irreducible Pisot
incidence and `|det M| = 1`; here `M` and `β` are those of `σ` itself, and `q`
is the power with fixed point `w` from §3. If `{c,c'}` has a left strong-coincidence witness
`σ^n(c) = PxQ`, `σ^n(c') = P'xQ'`, `p(P) = p(P')`, then `λ(R_c ∩ R_c') = 0`.
A right witness `p(Q) = p(Q')` gives instead
`λ((R_c + πe_c) ∩ (R_c' + πe_c')) = 0`.

*Proof.* Let `τ = σ^m` with `m ≥ n` a multiple of `q`, so `τ(w) = w`. Applying
`σ^{m−n}`, the witness persists to level `m`: `σ^m(c)` and `σ^m(c')` begin with
`σ^{m−n}(P)` and `σ^{m−n}(P')`, which have equal Parikh vectors, followed by the
same letter `y = g^{m−n}(x)`. If `Wy` is a prefix of `w`, then `W = τ(V)p` with
`Vd` a prefix of `w` and `τ(d) = pys`; conversely each such `τ(V)py` is a prefix
of `w`. Taking closures of finitely many affine images of compact sets,

    R_y = ⋃_{(d,p): τ(d) = p y s} ( M_s^m R_d + π p(p) ).

Unimodularity gives `|det M_s| = 1/β`, and `y` occurs `(M^m)_{yd}` times in
`τ(d)`, so `v := (λ(R_d))_d` satisfies `β^m v ≤ M^m v` componentwise. Pairing
with `ℓ > 0` (`ℓM^m = β^m ℓ`) forces equality in every coordinate. Hence the
measure of each union is the sum of the measures of its pieces, and distinct
pieces meet in null sets. The index pairs `(c, σ^{m−n}P)` and `(c', σ^{m−n}P')`
are distinct (different source letters) with the same translation. Therefore
`λ(M_s^m(R_c ∩ R_c')) = 0`, that is, `λ(R_c ∩ R_c') = 0`. For a right witness,
`p(P) − p(P') = M^n(e_c − e_c')`, so the two translations differ by
`M_s^m π(e_c − e_c')`, and the same argument applies to the translates
`R + πe`. ∎

The equality step also gives `(λ(R_c))_c = s·f`, with `s > 0` by the
unconditional bound `λ(R_c) ≥ κ f_c/ℓ̄` of §3a. This is Arnoux–Ito Cor. 2 (the
pieces of the set equation are pairwise measure-disjoint) together with the
second sentence of the proof of their Thm 2 ("The corollary 2 shows that, if σ
has a positive strong coincidence of order 1 for i, j, X(i)'∩X(j)' is of
measure 0"), read through the dictionary; both read in the published text.
Compare Siegel–Thuswaldner, Mém. SMF 118 (2009), Thm 2.6 (measure-disjoint
set equation; reported by the audit, not read here). Unimodularity is essential:
for `|det M| ≥ 2` the inequality reads `M^m v ≥ (β/|det M|)^m v` and forces
nothing. The non-unit analogue belongs to the adelic space
(Minervino–Thuswaldner 2014) and is **not** proved here.

(Arnoux–Ito's all-pair hypothesis in Thm 2 is used only to make all primed
pairs disjoint and transfer this to the unprimed family; the one-pair
statement needs no all-pair hypothesis.)

Valid implications (unit case):

    left SC(c,c'), one pair            => λ(R_c ∩ R_c') = 0       [Lemma P]
    left SC on all pairs               => both families disjoint  [Arnoux–Ito Thm 2]
    R_c, R_c' disjoint on all of A(C)  => no strict C             [Theorem B]
    strict C                           => no left SC on A(C)      [Theorem A(4)]

So `SC(A(C)) ⇒ disjoint(A(C)) ⇒ no strict C` holds in the unit case, but it is
no stronger than Theorem A(4), which needs no geometry. "Strictly between"
stays withdrawn: no separating example is known. Measure-disjointness of
`R_c, R_c'` for a pair **without** a left SC witness is open (Arnoux–Ito §6;
conjectural in Siegel–Thuswaldner 2009). It is the only input under which
Theorem B excludes more than Theorem A(4) does. Neither Nakaishi
arXiv:1610.03146 (withdrawn) nor arXiv:2401.07771 (see
`nakaishi-2024-first-entry-audit-2026-10-13.md`) may be cited for it.

**Density scope:** The lattice-point equality in §3 is the
fixed-origin *regular-window* count proved in §8 (human review
pending), applied **only to bounded Jordan-measurable windows
such as finite box unions**. Moody's general measurable-window
"almost every translate" theorem must not be read as an
all-translates count for arbitrary fractal overlaps. The
proof deliberately takes an open box cover of the compact
overlap set, counts in those regular boxes at the fixed
lattice translate, and then uses outer regularity. The
Rauzy overlap `Z_A` is **not** assumed regular itself.
Theorem B therefore carries exactly the status of §8
(repository-proved, human review pending); the bounded
Mojo tests do not validate measure theory.

In the **non-unit** case, Euclidean projection is not a
substitute for the natural adelic representation space.
No adelic version, nor general positive-measure-subtile
disjointness, is proved here.

## 5. Exact controls

| System | Arithmetic | `A(C)` | `g×g` image | SC witness on `A(C)` within budget |
| --- | --- | --- | --- | --- |
| `012/120/201`, ordered 3-cycle `(012,120),(120,201),(201,012)` | all-ones matrix; not Pisot | all three pairs | all three | none (level ≤ 6) |
| `10/102/211`, the four strict states (#459) | primitive, nonsingular, reducible | `{{1,2}}` only | `{{1,2}}` | none (level ≤ 8) |
| `01/121/012` (#476, k=1) | PIP, det 2 | — | — | every pair is coincident by level 2; each candidate `(01,10),(12,21),(02,20)` meets a coincident factor by depth 3 and is refused |

In the second row the good edge `{0,1}` has a level-1 witness, and `g`
collapses it (`g(0) = g(1) = 1`). A state cut on it is refused.
`{0,2}` has no witness within level 8; this is an exhausted budget, not a
verdict. It is not a cut pair of the component.

The earlier fixture listed `{(012,120),(012,201),(120,201)}`, which is closed
only up to track swap: `σ(012) = 012120201` and `σ(120) = 120201012` factor into
`(012,120),(120,201),(201,012)`. The ordered 3-cycle is genuinely closed; the
conclusions about `A(C)` are unchanged.

The transient control: the closure of `(02,20)` under `10/102/211` is a
6-state strict system with `A(C) = {{0,2},{1,2}}`. Its sink SCC is the four
strict states of row 2, which carry only `{1,2}`. Theorem A applies to the
whole system; the per-pair frequency of the #482 note covers only pairs
carried by a strongly connected component.

The unit PIP `01/12/021` (det 1) has left strong-coincidence witnesses on all
three pairs: `{0,2}` at level 1 (index 0), `{0,1}` at level 4 (index 16,
letter 0, prefix Parikh `(4,7,5)`) and `{1,2}` at level 4 (index 10, letter 1,
prefix Parikh `(3,4,3)`). So by Theorem A(4) it has no strict system, and by
Lemma P all three overlaps `R_c ∩ R_c'` are null.

None of the three strict controls (uniform, row 2, transient) is PIP, so Rauzy subtiles are not defined for them.
They calibrate Theorem A only. In particular, `|A(C)| = 1` occurs outside
PIP.

```sh
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_cut_pair_reduction.mojo)
```

The audit (`kernel/psc/c4_cut_pair_reduction.mojo`) checks only the
*necessary* conditions of Theorem A, on supplied words at a stated depth. It
fails closed on:
- a coincident factor;
- a reducible or unbalanced state;
- a cut pair outside `A(C)`;
- a collapsing initial-letter map.

It does not certify full child closure; the strict birth atlas does that.
A missing strong-coincidence witness is reported as an exhausted budget.

## 6. Non-claims and the remaining gap

- Theorem C's occupancy `θ_c` is not computed exactly for any specimen here.
  Its identification with `1/d_cov` for the covering degree `d_cov` holds only
  under the §3a imports.
- No strict PIP system has been exhibited or excluded. C4, BH, A1′, G1 and PSC
  stay open.
- Unconditional measure-disjointness of Rauzy subtiles is **not** proved and
  appears open. On pairs with a left SC witness it holds in the unit case
  (Lemma P), where Theorem A(4) already excludes them. Theorem B therefore
  adds exclusion power only on cut pairs **without** an SC witness, and only
  through that open disjointness question.
- The adelic (non-unit) form of Theorem B is not proved.
- The graph-directed IFS comparison proposed here earlier (cut-point sets
  `K(G)` with matrix `N^T` inside the subtiles with matrix `M^T`, common
  contraction `M_s`) is **retired at the measure level**. The 2026-11-04 audit
  workflow reported (derivation **not reproduced in the repository**) that the
  two embeddings plus noncoincidence are consistent for every covering degree
  `d_cov ≥ 2`. A contradiction would then need `Σ_c λ(R_c) < 2κ/ℓ̄`, which,
  conditionally on the §3a imports (multiple tiling of degree `d_cov`;
  tiling ⇔ PDS), is equivalent to `d_cov = 1`, i.e. to PDS.
- 2026-11-05: the [cut-attractor note](c4-cut-attractor-window-2026-11-05.md)
  shows that a strict system forces `int(R_c ∩ R_c')` nonempty on a cut pair
  (Lemma G, no determinant hypothesis), that a strict system is exactly an
  A1′ configuration plus bounded common-vertex gaps (Proposition 3), and
  that at coincidence rank 2 the open-overlap condition is *equivalent* to
  the existence of a strict system (Proposition R, conditional). The next
  open quantifier is sharpened there: at `cr = 2` it is equivalent to C4.
- Next open quantifier: for unit PIP `σ` and every cut pair `{c,c'}` with no
  left SC witness at any level, bound `λ(R_c ∩ R_c')` below `κ δ_{c,c'}(C)`
  (`δ` as in the #482 note)
  by an argument not routed through PDS. Its hypothesis class is empty on every
  computed domain (SC_all on the standing census), where C4 already follows
  from Theorem A(4).

## 7. Independent source and acceptance audit — 2026-11-04

The original "Theorem A productivity is exactly strong coincidence" wording
is sharpened to the *necessary* absence of a cut-pair witness for every
strict component and the *conditional* finite-reachable-sink converse.
Absence of a witness on an arbitrary selected first-letter pair does **not**
itself imply the existence of a nonproductive closed system. The executable's
bounded `-1` result is an exhausted search, not a proof of absence.

Theorem B is a written density reduction with an explicit compact-window
lattice-count step, proved in §8 and found sound by the automated audits of
2026-11-04 (human review pending). It is **not** checked by the finite Mojo
audit, and its validity is not inferred from the finite fixtures.
§4 now records `R_c = −X(c)'`; one left SC pair gives `λ(R_c ∩ R_c') = 0`
in the unit case (Lemma P). No non-unit or suffix-to-prefix transfer may enter
the C4 proof ledger.

The actual remaining challenge in Issue #461 is unchanged: establish
productivity in the genuine irreducible Pisot strict-carrier setting,
without assuming subtile measure-disjointness or an unproved adelic
analogue. Do not promote C4, BH, A1′, G1 or PSC based on this note.

### Additional fail-closed diagnostic obligation

The native audit now rejects a **positive** finite strong-coincidence
witness on any pair in `A(C)`, even when the user requests a
shallower cut-factor scan. The explicit control `01/121/012`
with source `(01,10)` has no diagonal at **depth zero**,
but its initial pair `{0,1}` has a genuine level-two
equal-prefix/next-letter witness. Such an input cannot be
reported as a valid strict-system audit simply because
`depth=0`; it must refuse. A **missing** witness at
`max_level<=12`, in contrast, remains a bounded search
exhaustion and not a general noncoincidence verdict.

The canonical checker refuses negative or excessive
witness levels and inflation depths, invalid letters,
empty substitution images, and predicted word expansion
beyond a fixed 100,000-letter budget. These are
executable resource guards, not new hypotheses of
Theorem A. The independent Python reference separately
reconstructs both complete strict non-Pisot controls,
all real PIP common-prefix witnesses, and budget refusal.
Only a complete strict-derived-system builder can certify
**all actual child closure**; these bounded cut-pair
necessity tests do not replace that constructor.


## 8. Fixed-lattice regular-box density: a self-contained sublemma

The density argument of §3 needs an asymptotic for the
**specific, unshifted lattice**, not the almost-every-translate
version for arbitrary measurable windows in Moody (2002).
This is the classical density theorem for regular model sets,
valid for every translate; it is reproved here for
self-containment, in exactly the form used.

**Fixed-lattice box lemma (scoped).** Let
`Phi: R^3 -> R x E^s` be the invertible map
`Phi(y)=(ell.y, pi y)`, and let
`Lambda=Phi(Z^3)`, with covolume `kappa>0`.
Since `χ_M` is irreducible over ℚ, no nonzero integer
row `m` satisfies `m·v = 0` for the Perron right
eigenvector `v` (proved below); equivalently `π(Z³)`
is dense in `E^s` and the physical flow on the torus
is totally irrational. For any bounded Jordan-measurable
`U ⊂ E^s` (for example a finite union of boxes),

~~~text
N_U(X) = # {y in Z^3 : 0 <= ell.y < X, pi y in U}
       = X * lambda(U) / kappa + o(X) as X -> infinity.
~~~

This is the exact form needed in §3; it makes
**no** density assertion for the potentially
non-regular fractal overlap `Z_A` itself.

**Proof of nonresonance.** Suppose that a nonzero
integer row `m` annihilates a Perron right
eigenvector `v`. Because `M v = beta v`,
all rows `m, mM, mM²` annihilate `v`.
But irreducibility of the degree-three
characteristic polynomial implies every
nonzero rational row is cyclic for `M^T`;
the three displayed rows form a rational
basis. They cannot have a nonzero common
annihilated column. Contradiction. Hence
no nonzero rational row annihilates the
Perron line.

**Proof of lattice density.** View the
physical direction as `e_t=(1,0)` in
`R x E^s` and the compact torus as
`T=(R x E^s)/Lambda`. A nonzero dual-lattice
character with zero frequency along the
physical translation flow `t -> [t e_t]`
would be a functional `(0,eta)` whose
pullback `m=Phi^T(0,eta)` is a nonzero
integer row. This row annihilates the
Perron eigenline because `pi v=0`,
contradicting nonresonance. Therefore the
physical flow is totally irrational on
`T`. Its time averages on continuous
functions equal Haar averages: check
characters explicitly (each nontrivial
frequency contributes an averaged
exponential tending to zero), then
approximate continuous functions by
finite trigonometric sums.

Define the `Lambda`-periodic function

~~~text
F_U([xi]) = sum_{lambda in Lambda}
  1_[0,1)((lambda+xi)_physical)
  * 1_U((lambda+xi)_internal).
~~~

The sum is finite on a fundamental
domain because `[0,1] x closure(U)`
is compact (`[0,1) x U` is only
relatively compact). `F_U` is bounded
and Riemann-integrable on the torus:
its discontinuities lie in the locally
finite union of `Lambda`-translates of
`∂([0,1) x U) ⊆ ({0,1} x closure(U)) ∪
([0,1] x ∂U)`, which has Haar measure 0
because `λ(∂U) = 0` (Jordan
measurability), so continuous
`g ≤ F_U ≤ h` with `∫(h−g) < ε` exist. Continuous
upper/lower approximations therefore
extend the character argument to
`F_U`, giving

~~~text
(1/X) integral_0^X F_U([-t e_t]) dt
    -> integral_T F_U = lambda(U) / kappa.
~~~

The right-hand identity is obtained
by unfolding over a fundamental
domain of `Lambda` (counting
each lattice translate exactly once).

Integrating in `t` counts every
lattice point with physical coordinate
in `[1,X]` and internal coordinate in
`U` with weight exactly one.
Only the two physical endpoint strips
of width one contribute a discrepancy.
Each strip contains at most a
**uniform finite** number of lattice
points with internal coordinate in
bounded `U`, by discreteness of
`Lambda` and boundedness of
`[0,2] x closure(U)` under translation.
Thus the integral differs from
`N_U(X)` by `O_U(1)`, proving the
claimed asymptotic. QED.

**Application.** In §3 the sets
`R_c` are compact, their pairwise
intersection union `Z_A` is compact,
and the cut projections are within
`epsilon_n -> 0` of both relevant
subtiles. For each fixed *regular*
open box union `U` covering
`Z_A`, compactness forces all
large-n cut projections inside
`U`. Apply the scoped lemma with
`X=beta^n L` and the physical
cut-count lower bound, then
take the infimum over regular box
covers by outer regularity.
No non-regular or almost-sure
model-set density statement is
silently imported.

**Verification boundary.** This
supplies the previously unstated
fixed-origin regular-window argument.
It does *not* prove subtile
measure disjointness, its non-unit
adelic analogue, or any productivity
conclusion beyond the stated
conditional strict-carrier obstruction.
The argument is a written proof;
there is no numerical Mojo
certificate for a Lebesgue-measure
or torus-unique-ergodicity statement.
Human mathematical review remains
pending and governed claim statuses
remain unchanged.

## 9. Non-unit follow-up: exact residue bounds and a compact lift

The [non-unit occupancy certificate](c4-nonunit-residue-occupancy-2026-11-04.md)
independently establishes the below-half Euclidean occupancy conclusion for
`1/021/001` using a complete depth-two residue table and exact algebraic
upper bounds. It does not validate the historical scratch program or compute
exact fractal areas. Literal strong-coincidence witnesses exclude a strict
system for this specimen, so low Euclidean occupancy is not a converse to
Theorem C.

The [compact M-adic counting bridge](c4-nonunit-madic-counting-bridge-2026-11-04.md)
proves counterparts of Theorems B and C in the explicitly constructed
space `E^s x lim_q Z^3/M^q Z^3`, and gives a finite-cylinder upper-certificate
target. Its one-pair null-overlap statement concerns lifted sets, not their
Euclidean projections. These are separate written scoped proofs, human
review pending; identifying the compact construction with a particular
localized adelic model remains a distinct task if needed downstream.
