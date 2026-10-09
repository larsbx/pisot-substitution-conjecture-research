# P1b: why seed graphs grow at the Pisot edges — edge progressions, 2026-10-09

**Status:** research note. Lemma EP (§2) is proved here, and its proof is
elementary. §3 is exact data from the kernel (scratch probes through
`build_seed_overlap_graph_from_tables`). §4 states a conjecture and a plan.
No ledger node or manuscript statement changes. #139 and PSC stay open.

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
3. `⟨ℓ, u₊⟩ = −f(−1)/(β + 1)` and `⟨ℓ, u₋⟩ = −f(1)/(β − 1)`.

*Proof.*

1. The parameters occur only in the `y`-row of `M`. The `y`-column of an
   adjugate consists of the cofactors of the `y`-row, which delete that row.
2. `(M ± I) adj(M ± I) = det(M ± I) I`, with `det(M + I) = −f(−1)` and
   `det(M − I) = −f(1)`.
3. Pair item 2 with the left Perron vector: `ℓM = βℓ`. `square`

Lemma P1 says that PIP forces `f(±1) < 0`. So `k₊ = −f(−1) ≥ 1` and
`k₋ = −f(1) ≥ 1`, and both are small exactly near the corresponding edge.
There `⟨ℓ, u_±⟩ = k_±/(β ± 1)` is tiny. A translate of an overlap by `j·u_±`
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

If so, boundary hitting along the whole line is a **finite skeleton
condition**, uniform in `q`:

- an odd cycle fixes `j`;
- an even cycle (reflection), or any cycle (translation), must have zero
  net drift;
- the skeleton and its drifts are fixed data.

Lemma EP and Corollary EP′ already prove the dynamics. What remains is to
prove that the skeleton is finite and independent of `q`. That is: the run
position `m` chosen by realness cancels `jk` up to a bounded amount, so
`w₀′ = Mw₀ + δ − (j + j′)u + (jk + m)e_y` stays in a bounded set.

**Why it matters.** It explains the only places where every bounded-graph
method fails, by one parameter-free vector per edge. That turns the
unbounded part of each Theorem E class into finitely many skeletons. Class D
is already settled (Corollary W2). Its edge lines (`m = 0, 1` and so on) were
exactly where the graphs grew slowly.

**Not established.** No new member is certified by this note. The skeleton
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
