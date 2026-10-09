# P1b: why seed graphs grow at the Pisot edges — edge progressions, 2026-10-09

**Status:** research note. Lemma EP (§2) is proved here, and its proof is
elementary. §3 is exact data from the kernel (scratch probes through
`build_seed_overlap_graph_from_tables`). §4 states a conjecture and a plan.
§6 is the progression certificate and Theorem P: the class A slope-1 line
`(n + 1, n, n + 1)`, certified for every `n` (computer-assisted). No ledger
node or manuscript statement changes. #139 and PSC stay open.

## 1. The question

Every certificate so far (Theorems L, L′, L″, W and C) works one bounded
graph at a time. It stops where the seed graphs stop being bounded:

- class B near slope 3;
- class C past `d ≈ q/4`;
- class A at slope 1.

A uniform argument has to work there. Near those places the graph size grows
like `1/(1 − |β₂|)`. In class C at `q = 96`, `size × (1 − |β₂|)` is 342, 276,
269, 264 for `d = 44, 46, 47, 48`. This note identifies the growth exactly.

**Sectors.** Away from the edges, normalise `ℓ_y = 1`. For class C with
`d = δq`, `q → ∞`, this gives `ℓ_x → (1+δ)/(1−δ)` and `ℓ_c → 1/(1−δ)`. The
observed plateau boundaries are lines `aℓ_x + bℓ_c + c = 0` with small
integer coefficients:

- `ℓ_x + ℓ_c = 3` at `d = 25/26`;
- `ℓ_x − ℓ_c = 1/2` at `32/33`;
- `ℓ_x = 2` at `33/34`;
- `ℓ_x + ℓ_c = 4` at `40/41`.

Each is a rational `δ`. They accumulate only at Lemma P1's edge `δ = 1/2`,
where `f(−1) → 0` and `β₂ → −1`.

## 2. Lemma EP (edge progressions)

Let `M` be the incidence matrix of a member of Theorem E's normal form
`σ(x) = x y^p s_x, σ(c) = c y^q s_c, σ(y) = t y^r s_y`, with
`f(t) = det(tI − M)`. Put

    u₊ = adj(M + I) e_y,     u₋ = adj(M − I) e_y.

1. `u₊` and `u₋` do not depend on `(p, q, r)`.
2. `M u₊ = −u₊ − f(−1) e_y` and `M u₋ = u₋ − f(1) e_y`.
3. `⟨ℓ, u₊⟩ = −f(−1)ℓ_y/(β + 1)` and
   `⟨ℓ, u₋⟩ = −f(1)ℓ_y/(β − 1)`.

*Proof.*

1. The parameters occur only in the `y`-row of `M`. The `y`-column of an
   adjugate consists of the cofactors of the `y`-row, which delete that row.
2. `(M ± I) adj(M ± I) = det(M ± I) I`, with `det(M + I) = −f(−1)` and
   `det(M − I) = −f(1)`.
3. Pair item 2 with the left Perron vector: `ℓM = βℓ`. `square`

Lemma P1 says that PIP forces `f(±1) < 0`. So `k₊ = −f(−1) ≥ 1` and
`k₋ = −f(1) ≥ 1`, and both are small exactly near the corresponding edge.
Normalize `ℓ_y = 1` for the estimates below. Then
`⟨ℓ, u_±⟩ = k_±/(β ± 1)` is tiny. A translate of an overlap by `j·u_±`
moves `t = ⟨ℓ, w⟩` by only `j k_±/(β ± 1)`, so whole progressions
`w₀ + j·u_±` stay real, with `|j|` up to about `β/k_±`. **That is the growth.**

*Corollary EP′ (index dynamics).* Choose a coordinate functional `φ` with
`φ(u_±) = 1` and `φ(e_y) = 0`. For instance `φ = w_x` when `(u_±)_x = 1`.
Write `w = w₀ + j u_±` with `j = φ(w)`. A child `w′ = Mw + δ` (`δ` its
prefix and run digits) then has

    j′ = ∓j + φ(Mw₀ + δ),

so `j` is reflected (`u₊`) or translated (`u₋`) by a constant that depends
only on the edge's skeleton data. *Proof:* apply `φ` to item 2. `square`

The vectors, for the three classes met:

| class | edge | vector | dynamics |
| --- | --- | --- | --- |
| C | `f(−1)` (`d → q/2`) | `u₊ = (2, −6, 6) = 2·(1, −3, 3)` | reflection |
| B | `f(−1)` (`p → 3q`) | `u₊ = (−1, −3, 6)` | reflection |
| A | `f(1)` (slope 1, `p − q` fixed) | `u₋ = (1, −1, 0)` | translation |

For an integer index, the implementation may use a primitive vector `u`
with `u_± = g u`. Then `M u = ∓u + k e_y` with
`k = −f(∓1)/g`, rather than the unscaled `k_± = −f(∓1)`.
In class C the primitive vector is `(1,−3,3)` and `g = 2`.
The certificate requires a unit coordinate off `y` so its coordinate
functional gives an integer index for every integer overlap, and it checks
the residual identity and positive constant `k` directly.

## 3. Data (exact kernel, scratch probes)

Write each vertex `(a, b, w)` as `skeleton (a, b, w₀)` × `index j`.

| member | vertices | dominant difference | skeleton | edge types | edges with `j′ ± j` constant |
| --- | --- | --- | --- | --- | --- |
| C, `q = 96`, `d = 48` (`k = 6`) | 1,127 | `(1,−3,3)` ×926 | 180 | 1,974 | 1,974 |
| C, `q = 192`, `d = 96` (`k = 6`) | 2,087 | | **180, the same set** | 1,974 | 1,974 |
| C, `q = 192`, `k = 4, 8, 10, 14` | 3,181 … 956 | | 220, 192, 174, 170 | | all |
| A, `(n+1, n, n+1)`, `n = 20` | 915 | `(1,−1,0)` ×826 | 75 | 588 | 588 |
| A, same line, `n = 40` | 1,715 | `(1,−1,0)` ×1,626 | **75, the same set** | 588 | 588 |
| B, `p = 3q + 10`, `r = q + 1`, `q = 20` | 2,075 | `(1,3,−6)` ×1,772 | 270 | 3,135 | 3,135 |
| B, same line, `q = 30` | 2,635 | `(1,3,−6)` ×2,332 | **270, the same set** | 3,135 | 3,135 |

The class B vector was **predicted** from Lemma EP before any class B data
was examined. The index window is `|j| ≲ (β + 1)/k`: at `q = 192`,
`j_max · k` is 100–112. On a line of fixed `k`, the skeleton is independent
of `q`. As `k` varies, a common core persists: 161 states are shared by
`k = 6, 8, 10, 14`, and `k = 4` is the most special.

## 4. What this suggests, and what it does not establish

**Conjecture EP.** Near each Lemma P1 edge, on a line of fixed `k_±`:

- the seed graph is a finite, `q`-independent skeleton crossed with the
  index `j`;
- `j` is exactly reflected or translated along every edge;
- `j` lies in a window whose ends are affine in `q`.

The skeleton and its drifts would then be fixed data, but the validity
guards and index sets still matter. A reflection cycle of odd length acts
as `j ↦ C − j`; it fixes an integer index only when `2j = C`. A reflection
cycle of even length, or any translation cycle, acts as `j ↦ j + D`.
Repeating it returns to the same lifted vertex only when `D = 0`, while
nonzero drift may yield valid finite paths of length growing with `q`.
These affine identities do not by themselves decide boundary hitting or
prove that the parameter-uniform closure terminates; §6 gives one
sufficient certificate and §7 specifies the next closure experiment.

Lemma EP and Corollary EP′ already prove the dynamics. What remains is to
prove that the skeleton is finite and independent of `q`. That is: the run
position `m` chosen by realness cancels `jk` up to a bounded amount, so
`w₀′ = Mw₀ + δ − (j + j′)u + (jk + m)e_y` stays in a bounded set.

**Why it matters.** It explains the only places where every bounded-graph
method fails, by one parameter-free vector per edge. That turns the
unbounded part of each Theorem E class into finitely many skeletons. Class D
is already settled (Corollary W2). Its edge lines (`m = 0, 1` and so on) were
exactly where the graphs grew slowly.

**Not established by §§2–4.** The skeleton
finiteness is shown by data only, on the lines listed. How the skeleton
depends on `k` is only partly mapped. The sectors between the edges are
finite in any compact range of `δ`, but this is not proved.

## 5. Next

1. **A progression certificate for one edge line.** Vertices `(s, j)` with
   `j ∈ [L_s(q), U_s(q)]`, with ends fitted and certified like run
   positions. Edges `j′ = ∓j + c_e`. Hitting is decided on the skeleton by
   the drift argument. First target: class A `(n + 1, n, n ± 1)`, which the
   line method could not reach (translation, the simpler dynamics). Then
   class C at `k = 6`.
2. **The `k`-dependence** of the skeleton, aiming at finitely many skeleton
   types for `k ≥ k₀`. Together with the sectors, that would cover class C
   uniformly.
3. **Lemma EP for the families outside Theorem E** (the swap family,
   Proposition Y, Theorem K's family). Their parameters also sit in one row,
   or not, and that decides whether the vectors stay parameter-free.

## 6. The progression certificate (Theorem P)

`kernel/psc/progression_line.mojo` implements §5.1. The driver runs it as

    symbolic_line_certificate.mojo progression CLASS AP BP AQ BQ AR BR U0 U1 U2 S

**Data.** A *state* is `(a, b, w₀)` with `φ(w₀) = 0`. Its members are
`w₀ + j u` for `j` in a finite union of integer intervals whose ends are
affine in the line parameter. An *edge* carries a constant drift `c` and a
validity set `V` of the source's `j`. For every `j ∈ V` the child exists and
has index `c + s j`. Every decision is a sign read of the line engine
(`SymbolicClosure` and its `Eventual`), so each holds for every parameter
above one certified threshold `q₀`.

**Edges.** Lemma EP gives `M(w₀ + j u) = M w₀ + j(s u + k e_y)`.

- A non-run child `B₀ + j(s u + k e_y)` is real for a window of `j` whose
  width is constant. The certificate checks that the width is constant. Each
  `j` in the window gives its own state.
- A run child at run position `m` becomes the state `(a′, b′, base₀ + m′e_y)`
  with `m′ = m + jk`.
- `m′` is pinned to a constant-width window. For `s = +1`, child − parent
  `= t(B₀) − t(w₀) + m′ℓ_y` lies in `(−ℓ_{b′} − ℓ_a, ℓ_{a′} + ℓ_b)`. For
  `s = −1`, child + parent `= t(B₀) + t(w₀) + m′ℓ_y` lies in
  `(−ℓ_{b′} − ℓ_b, ℓ_{a′} + ℓ_a)`.
- Within the window, `V` is the child's realness, taken back to the
  parent's `j`, intersected with the run bounds `r_lo ≤ m′ − jk ≤ r_hi`
  and with the parent's realness.

Every child of every member is therefore an edge.

**Members.** States and index sets are closed together from the seeds. A
state is expanded once it has a member. After four changes a state's set is
widened to its realness interval. The result is a superset of the
seed-reachable overlaps, and each element is a real overlap.

**Hitting.** The steps are the edges for `s = +1`. For `s = −1` they are the
composites of two edges (`σ²`): `j ↦ j + (c₂ − c₁)`, valid on
`{j ∈ V₁ : c₁ − j ∈ V₂}`. Let `d` be the largest step drift and
`j₀ = max(1, ⌊d/2⌋)`; this is the least `j₀ ≥ 1` with `2(j₀ + 1) > d`.

- Every member with `|j| > j₀` has a step that strictly lowers `|j|`, or a
  drift-0 step to a member already ranked. The second clause is a monotone
  fixed point.
- The members with `|j| ≤ j₀` are finitely many explicit vertices. Each
  reaches offset zero inside the core.

A path along ranked steps lowers `(|j|, rank)` until it enters the core, and
the core hits. Any failure raises. So does a run bound that `k` does not divide,
a non-constant drift, or a window that grows with the parameter.

**Theorem P.** On the class A line `(p, q, r) = (n + 1, n, n + 1)`, with
`u = u₋ = (1, −1, 0)` and `s = +1`, every PIP member has every seed-reachable
strict-zipper overlap reaching offset zero. Each member therefore has pure
discrete spectrum and a finite BPA (Corollary E2: `|det M| = 2`).

- For `n ≥ 12`: 287 states and 3,722 edges. Every member with `|j| ≥ 2` is
  ranked, and the 279 core members hit inside the core.
- For `n < 12`: 12 PIP members, decided exactly, all hitting.
- Pinned in `certified_progressions()` and re-run by the evidence workflow.

This is the first line the bounded-graph method could not reach: its seed
graphs have `40n + 115` vertices.

**Cross-check against an independent computation.** The exact seed graphs
(`build_seed_overlap_graph_from_tables`) at `n = 20, 30, 40, 50` have 915,
1,315, 1,715 and 2,115 vertices on 75 skeleton states. Every one of them is
a member of the symbolic sets; 0 are missing. The symbolic sets are
3,583 … 8,413 (287 states). The surplus is the widening, and it is sound
because the certificate proves hitting for the whole superset. The driver
repeats this containment check at `q₀` and `q₀ + 5` on every run.

**Not established.** Theorem P is computer-assisted and unreviewed. It rests
on Theorem E, the line engine's soundness (Lemma S) and the imported
Barge–Štimac–Williams theorem. The reflection case (`s = −1`, class C, §4)
is implemented but not yet certified on any line. For `k > 1` the run
bounds become `⌈(m′ − r_hi)/k⌉ ≤ j ≤ ⌊(m′ − r_lo)/k⌋`. These are affine
when `k` divides their parameter coefficient; otherwise the certificate
refuses, and the line must be restricted to a sublattice. That path is
implemented but not yet exercised.

## 7. Closure handoff and guarded cycle acceleration

**Current implementation.** The pinned Theorem P computation still uses
the full-realness widening in §6. The endpoint-only experiment described
in the session handoff is an uncommitted build; it is not evidence for
this tree, and no pin has been updated from it.

The handoff reports 7,000-second timeouts on class A
`(n + 1, n, n − 1)` and class C `(3n + 1, 2n + 1, n)`, followed by growth
under traced widening. Its last reported sizes are 1,085 states / 22,971
edges and 1,483 states / 27,473 edges, respectively. The claimed 225-state
exact skeleton for the latter is a handoff observation, not an archived
replay here. These bounded runs establish neither nontermination nor a
counterexample to hitting. They justify investigating the overapproximation
before spending another long run on a widening threshold.

**Literature stop/go, 2026-10-09.** Proposed experiment: replace the member
widening with exact iteration of witnessed guarded cycles while retaining
the existing edge construction, eventual sign decisions and hitting check.
Three primary sources delimit the transfer:

| Source | Relevant result | Transfer boundary |
| --- | --- | --- |
| [Cousot–Cousot (1977), §9](https://cs.nyu.edu/~pcousot/COUSOTpapers/POPL77.shtml) | Sound approximations of fixpoints may enlarge the represented set. | Full-realness widening can remain sound for hitting over the entire resulting superset; its size says nothing about exact seed reachability. |
| [Bardin–Finkel–Leroux–Schnoebelen (2005), §§3–5](https://www.labri.fr/perso/leroux/papiers/BFLS05-atva.pdf) | Acceleration computes the iteration of selected control paths; their exact symbolic framework requires exact unions and images. | An interval hull that loses a cycle's residue constraint cannot be described as exact acceleration. |
| [Leroux–Sutre (2006), §3, Theorem 3.4](https://drops.dagstuhl.de/storage/16dagstuhl-seminar-proceedings/dsp-vol06081/DagSemProc.06081.4/DagSemProc.06081.4.pdf) | Terminating exact accelerated reachability returns the reachable set; termination requires additional flatness conditions and a suitable strategy. | PSC skeleton finiteness, a suitable finite symbolic representation and termination have not been established for the two failed lines. |

**Decision: proceed with a narrowed experiment.** Guarded cycle iteration
is standard prior art. Only its exact specialization and independently
replayed PSC receipts would be new evidence. No general termination claim
or new class A/C certificate is made.

**Cycle contract.** For a witnessed closed path `e₀,…,e_{m−1}`, let
`F₀(j) = j` and `F_{r+1}(j) = c_{e_r} + s_{e_r} F_r(j)`, with
`s_{e_r} ∈ {−1,+1}`. Its one-traversal source guard is

    D(q) = ⋂_{r=0}^{m−1} F_r⁻¹(V_{e_r}(q)).

The preimages are essential: guards expressed at different states cannot
be intersected in their local coordinates. For a translation cycle with
`F_m(j) = j + d`, the exact accelerated returns from a known reachable
source set `X(q)` are

    {j + h d : j ∈ X(q), h ∈ ℕ,
               j + t d ∈ D(q) for every 0 ≤ t < h}.

This condition checks every traversal and includes zero traversals. The
last returned endpoint need not lie in `D`: for `j = 0`, `d = 2` and
`D = [0,4]`, the returns are `{0,2,4,6}`. A single traversal may leave the
repeatable-source domain while remaining a valid path. Intermediate
states on every repeated traversal must also be added or reached by the
ordinary edge propagation before asserting full closure.

Preserve `j mod |d|` for nonzero drift, using residue-restricted intervals
or an equivalent exact representation. The hull `[0,6]` in the example
adds unreachable odd indices. A zero-drift cycle adds no new return
indices. An odd reflection cycle has map `j ↦ C − j`, whose square is
the identity, with two-traversal source guard
`D ∩ {j : C − j ∈ D}`; a nonzero-drift translation arises from an even
reflection cycle, including two distinct reflection edges.

**Review and replay obligations.** Before replacing the pinned algorithm,
add canonical Mojo guard-composition and exact acceleration tests for
both drift signs, zero drift, odd reflection, disjoint validity domains,
residue gaps and the final valid endpoint beyond the source guard. Compare
cycle iterates with independent literal integer replay. Exactness for
each selected cycle does not imply exactness or termination of the whole
worklist: retain all seeds and ordinary edges, add only witnessed reachable
members, and verify seed containment and edge closure at the final fixed
point. Resource caps remain inconclusive outcomes. Reproduce Theorem P's
entire verdict, including its exact finite part, before changing a pin;
account for #247's shared `psc/param_poly` imports when integrating.

**Constructor review.** The residual identity alone allowed `s = 0`,
`u = (0,−1,1)` on Theorem P's line: `M u = e_y`. The later interval map
and reflection composition assume `s = ±1`. The constructor now refuses
unsupported signs and vectors of the wrong dimension explicitly, and
`test_unsupported_index_sign_is_refused` guards the concrete accepted-before
case. This repairs input refusal; it does not change the valid pinned
progression or claim that an incorrect theorem verdict was produced.
