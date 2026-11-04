# C4 productivity: cut pairs, strong coincidence and a positive-measure subtile overlap

**Status:** Repository-proved reduction (Theorem A) and a repository-proved
measure obstruction (Theorem B) for a *supplied* strict C4 system. One import
(Arnoux–Ito pairwise disjointness, §4) is cited and not reproved. No change
to C4, BH (#139), A1′ (#138), G1 or PSC status.
[Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
Baseline `main@ad164fc` (merged #476).

## 1. Stop/go literature check

*Proposed claim.* A strict C4 component of a PIP substitution forces a
Lebesgue-positive overlap `λ(R_c ∩ R_c') > 0` of two Rauzy subtiles, for a
letter pair `{c,c'}` that labels its balanced cuts.

*Prior art.*
- [Arnoux–Ito 2001](https://projecteuclid.org/journals/bulletin-of-the-belgian-mathematical-society-simon-stevin/volume-8/issue-2/Pisot-substitutions-and-Rauzy-fractals/10.36045/bbms/1102714169.pdf):
  the strong coincidence condition makes the subtiles measure-disjoint (unit
  case). The paper records as open whether any unit Pisot substitution fails
  strong coincidence.
- [Minervino–Thuswaldner 2014](https://arxiv.org/abs/1402.2002): the same
  result for non-unit substitutions, on the adelic representation space.
- [Akiyama–Lee](https://ar5iv.arxiv.org/html/1403.0377): overlap coincidence
  implies strong coincidence when the height group is trivial.
- [Barge–Diamond 2002](https://www.numdam.org/item/BSMF_2002__130_4_619_0/):
  some letter pair is always coincident; all pairs are coincident on two
  letters.
- Model-set uniform distribution (Moody, *Uniform distribution in model sets*,
  Canad. Math. Bull. 45 (2002)) supplies the lattice-point count in §3.

*What transfers.* Measure-disjointness is known under strong coincidence.
Unconditional measure-disjointness of the subtiles was not found in any of
these sources.

*Decision.* **Proceed, narrowed.** The density argument behind Theorem B is
the standard "noncoincidence gives double covering" mechanism, specialised to
the *aligned* overlaps that sit at balanced cuts. Novelty is claimed only for
that specialisation and its quantitative bound, not for the mechanism.

## 2. Theorem A — productivity is strong coincidence on the cut pairs

Let `σ` be primitive and nonerasing on `{0,1,2}`, with positive letter lengths
`ℓ`, `ℓM = βℓ`, `β > 1`, and `ℓ` having ℚ-independent entries (true for PIP).
Let `C` be a finite nonempty set of ordered irreducible noncoincident balanced
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
5. Conversely, suppose `σ` has a balanced pair `T` that never produces a
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
3. The first factor of `σ(u,v)` begins with `(g(u_0), g(v_0))`. By (1) and
   (2) this pair is off-diagonal and lies in `A(C)`.
4. Suppose `σ^n(c) = P x Q` and `σ^n(c') = P' x Q'` with `p(P) = p(P')`. Take a
   state `(u,v)` with `{u_0,v_0} = {c,c'}`. In `σ^n(u,v)`, the positions `|P|`
   on both tracks have equal Parikh prefixes, so they form a balanced cut.
   The positions `|P|+1` also do. The factor between them is `(x,x)`, a
   coincident factor, which contradicts strictness.
5. The irreducible factors of all inflations of `T` form a finite set closed
   under children with no coincidence. Any sink strongly connected component
   of its child graph is a strict `C`. ∎

Items 1–4 are in the repository already, implicitly: the aligned branch of
the bad-SCC dichotomy, and the enclosure note's "carrier with aligned first
pairs". This note isolates them as a single interface, because it is where
Theorem B attaches.

## 3. Theorem B — a strict system forces a positive-measure subtile overlap

Assume in addition that `σ` is irreducible Pisot. Let `E^s` be the
contracting plane and `π` the projection onto it along the Perron line.
Replace `σ` by a power with a one-sided fixed point `w`; the original `C` is
still strictly closed under that power. Define

```text
R_c = closure { π p(P) : P c is a prefix of w } ⊂ E^s   (compact),
Z_A = ⋃_{ {c,c'} ∈ A(C) } (R_c ∩ R_c').
```

Fix Lebesgue measure `λ` on `E^s`. Let `Φ(y) = (ℓ·y, π y)` and let
`κ = |det Φ|`, the covolume of `Φ(Z³)` in `R × E^s`. Let `L_max` be the largest
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
dist(π x, R_c) ≤ ‖M_s^n‖ · max( |π p(u[:k])|, |π p(Y_d)| ) =: ε_n → 0,
```

where `M_s = M|E^s` is a contraction. The same argument on the bottom track
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
subtiles typically overlap with positive measure anyway, so the hypothesis of
Corollary B′ below fails and Theorem B carries no content there. The natural
replacement is the adelic representation space of Minervino–Thuswaldner. That
version is **not** proved here.

When `N` (the child matrix of `C`) is primitive, `r_n ~ β^n L / L̄`, where
`L̄ = ℓPz / 1·z` is the Perron-weighted mean state length. This gives the
sharper bound `λ(Z_A) ≥ κ/L̄`.

**Corollary B′ (productivity from disjointness).** If the subtiles of the
pairs in `A(C)` are pairwise measure-disjoint, `C` cannot exist. Equivalently:
if `R_c, R_c'` are measure-disjoint for every pair `{c,c'}`, then `σ` has no
strict C4 system.

## 4. Source-audited subtile comparison (corrected scope)

This section distinguishes the **positive-prefix** and **negative/suffix**
Rauzy subtiles of Arnoux–Ito. The stronger claim in the previous revision
that a positive strong-coincidence witness for *just one* pair implies
`λ(R_c ∩ R_c')=0` for the **unprimed positive-prefix subtiles** is
**NOT** supplied by the cited theorem, and is withdrawn as an import.
It must not be used in any proof dependency.

Arnoux–Ito (2001), Corollary 2 and Theorem 2, show:

- A positive strong coincidence on **one pair** `(c,c')`
  gives measure-zero overlap of the corresponding **primed** subtiles
  `X(c)' ∩ X(c')'` in their notation, by measure-disjointness
  of the set-equation pieces.
- If positive strong coincidence holds for **every pair of letters**,
  then **all** unprimed subtiles `X(c)` are pairwise measure-disjoint
  (Theorem 2, in the unimodular primitive Pisot setting).
  Passing from primed pairwise disjointness to the unprimed
  conclusion uses the global partition / union construction.
  The source does not give the unprimed statement for one
  arbitrary positively coincident pair alone.

This is not a minor notational distinction: Theorem B's
`R_c` were explicitly defined from **positive prefixes** of
a fixed point, and cannot be silently replaced by the primed
family without reworking the projection and density proof.

The logically valid implications are therefore:

~~~text
SC(c,c') for one pair   => primed pair overlap is null     [Arnoux–Ito]
SC on ALL letter pairs  => ALL unprimed subtiles disjoint  [Arnoux–Ito]
disjoint unprimed R_c/R_c' for every pair of A(C)
                        => no strict C                     [Theorem B]
strict C                => no SC on A(C)                   [Theorem A]
strict C                => positive unprimed overlap
                           on at least one pair of A(C)   [Theorem B]
~~~

**No pairwise `SC(c,c') => λ(R_c∩R_c')=0` claim is
retained.** Theorem B itself uses only the compact
positive-prefix subtiles and elementary lattice density;
it does *not* import any Arnoux–Ito strong-coincidence
implication. Thus this correction changes attribution
and a proposed "between" ordering, not the standalone
density argument.

**Density scope:** The lattice-point equality in §3 uses
the *regular-window* case of cut-and-project uniform density,
applied **only to finite unions of bounded boxes with
measure-zero boundaries**. Moody's general measurable-window
"almost every translate" theorem must not be read as an
all-translates count for arbitrary fractal overlaps. The
proof deliberately takes an open box cover of the compact
overlap set, counts in those regular boxes at the fixed
lattice translate, and then uses outer regularity. The
Rauzy overlap `Z_A` is **not** assumed regular itself.
If the physical/internal cut-and-project density hypotheses
are not verified, Theorem B must remain conditional on the
stated counting lemma; the bounded Mojo tests do not
validate measure theory.

In the **non-unit** case, Euclidean projection is not a
substitute for the natural adelic representation space.
No adelic version, nor general positive-measure-subtile
disjointness, is proved here.

## 5. Exact controls

| System | Arithmetic | `A(C)` | `g×g` image | SC witness on `A(C)` within budget |
| --- | --- | --- | --- | --- |
| `012/120/201`, the three image pairs | all-ones matrix; not Pisot | all three pairs | all three | none (level ≤ 6) |
| `10/102/211`, the four strict states (#459) | primitive, nonsingular, reducible | `{{1,2}}` only | `{{1,2}}` | none (level ≤ 8) |
| `01/121/012` (#476, k=1) | PIP, det 2 | — | — | every pair is coincident by level 2; each candidate `(01,10),(12,21),(02,20)` meets a coincident factor by depth 3 and is refused |

In the second row the good edge `{0,1}` has a level-1 witness, and `g`
collapses it (`g(0) = g(1) = 1`). A state cut on it is refused.
`{0,2}` has no witness within level 8; this is an exhausted budget, not a
verdict. It is not a cut pair of the component.

Neither strict control is PIP, so Rauzy subtiles are not defined for them.
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

- No strict PIP system has been exhibited or excluded. C4, BH, A1′, G1 and PSC
  stay open.
- Unconditional measure-disjointness of Rauzy subtiles is **not** proved and
  appears open. Theorem B turns productivity into that question on the cut
  pairs. This is a redirection of the problem, not a resolution of it.
- The adelic (non-unit) form of Theorem B is not proved.
- The next concrete step is to use the self-affine structure. The cut-point
  sets `K_S` of the inflations of `S` form a graph-directed family. It has
  contraction `M_s`, matrix `N` and positive measure, and it lies inside
  `Z_A`. The question is whether `K_S ⊆ R_c ∩ R_c'`, combined with the two set
  equations (subtiles via `M^T`, carrier via `N`, sharing the eigenvalue `β`),
  is inconsistent for an irreducible cubic. That is a finite-algebra question
  about two graph-directed IFS with a common contraction, and the place where
  the Pisot spectrum would have to enter.

## 7. Independent source and acceptance audit — 2026-11-04

The original "Theorem A productivity is exactly strong coincidence" wording
is sharpened to the *necessary* absence of a cut-pair witness for every
strict component and the *conditional* finite-reachable-sink converse.
Absence of a witness on an arbitrary selected first-letter pair does **not**
itself imply the existence of a nonproductive closed system. The executable's
bounded `-1` result is an exhausted search, not a proof of absence.

Theorem B is a proposed mathematical density reduction with an explicit
compact-window lattice-count step. It is **not** checked by the finite Mojo
audit. In particular its quantitative measure lower bound requires review
of the ambient lattice covolume normalization and the regular-box counting
lemma, as opposed to inferring validity from the three finite fixtures.
The Arnoux–Ito pairwise **primed** versus global **unprimed** result is
corrected in §4; no arbitrary pairwise strong-coincidence-to-unprimed-measure
implication may enter the C4 proof ledger.

The actual remaining challenge in Issue #461 is unchanged: establish
productivity in the genuine irreducible Pisot strict-carrier setting,
without assuming subtile measure-disjointness or an unproved adelic
analogue. Do not promote C4, BH, A1′, G1 or PSC based on this note.
