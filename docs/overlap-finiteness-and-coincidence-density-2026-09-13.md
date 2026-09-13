# The seed-patch overlap automaton is finite, and Level 3 without G1

**Status:** theorems with complete proofs (Sections 2–4), an exact finite
census (Section 5), and one precisely stated open bridge (Section 6). Nothing
here proves G1, SCC Producer, or PSC. The results reorganise the programme:
the geometric (overlap) form of Level 3 no longer depends on Hypothesis G1.

Notation follows `manuscripts/PSC_balanced_pair_state_2026-09-13.tex`
("the manuscript"): `sigma` is PIP on `A`, `|A| = d`, `M` its incidence
matrix, `beta` the Perron root, `l > 0` the left Perron eigenvector
(`l^T M = beta l^T`), `g(w) = <l, pi(w)>` the geometric length of a word, so
`g(sigma(w)) = beta g(w)`. A word `w` tiles `[0, g(w))` by the intervals
`[g(w[k]), g(w[k+1]))` of type `w_{k+1}`; a vertex is an endpoint of a tile.
`D_sigma` is the constant of the manuscript's Theorem 4.4 (bounded
discrepancy): the swap walk `Delta(j) = pi(sigma^N(ab)[j]) - pi(sigma^N(ba)[j])`
satisfies `||Delta(j)||_inf <= D_sigma` for all seeds, levels and `j`.

## 1. The seed-patch overlap graph

Fix a seed `(ab, ba)` and a level `N >= 0`. Put `U = sigma^N(ab)`,
`V = sigma^N(ba)`; both tile `[0, L_N)`, `L_N = beta^N (l_a + l_b)`. An
*overlap at level N* is a pair (top tile of `U`, bottom tile of `V`) whose
interiors intersect; its *type* is `(i, j, t)` with `i, j` the tile types
and `t` = start of the bottom tile minus start of the top tile. Inflating
both tiles and keeping the overlapping pairs of their sub-tiles gives the
*children* of an overlap; the type of a child is `(i', j', beta t + q - p)`
with `p, q` the prefix translations of the chosen sub-tiles. A *coincidence*
is a type `(i, i, 0)`; coincidences are terminal.

The *seed-patch overlap graph* `O_sigma` (manuscript Computation 6.7;
canonical implementation `mojo/psc/overlap_seed_patch.mojo`) is the graph on
the types reachable from the level-0 overlaps of the three seeds under the
child relation.

**Lemma 1.1 (occurrence).** Every vertex of `O_sigma` is the type of an
overlap occurring at some level of some swap pair, and every occurring
non-coincidence overlap type is a vertex. (The occurring coincidences that
`O_sigma` omits are exactly the descendants of coincidences, since
coincidences are terminal and every descendant of a coincidence is a
coincidence.)

*Proof.* Level-0 overlaps are the seeds. If an overlap occurs at level `N`,
its children are overlaps at level `N+1` (they are pairs of sub-tiles of the
two inflated tiles). Conversely an overlap at level `N+1` has as parent the
overlap of the level-`N` supertiles containing its two tiles, which overlap
because their sub-tiles do; if the overlap is not a coincidence, neither is
any ancestor, so it descends from a seed through non-coincidence vertices. ∎

## 2. Finiteness

**Theorem 2.1 (finiteness of the seed-patch overlap graph).** Let `sigma` be
primitive with every non-Perron eigenvalue of `M` inside the unit circle
(true for PIP). Every overlap type `(i, j, t)` occurring in a swap pair has
`t = <l, w>` for an integer vector `w` with

```text
||w||_inf <= B_sigma := D_sigma + (l_max + ||l||_1 D_sigma) / l_min .
```

Consequently there are at most `d^2 (2 B_sigma + 1)^d` occurring types, and
`O_sigma` has at most that many vertices, for every such `sigma`, with no
finiteness hypothesis.

*Proof.* Let the overlap consist of the top tile starting at `x = g(U[i])`
(the `i`-th vertex of the `U`-tiling) and the bottom tile starting at
`y = g(V[j])`. Then `t = y - x = <l, w>` with `w := pi(V[j]) - pi(U[i])`,
an integer vector. Write `w = (pi(V[j]) - pi(V[i])) - Delta(i)`. The second
term has `||Delta(i)||_inf <= D_sigma`. For the first, the `i`-th vertex of
the `V`-tiling is at `y_i = g(V[i]) = x - <l, Delta(i)>`, so
`|x - y_i| <= ||l||_1 D_sigma`; interior overlap gives `|x - y| < l_max`;
hence `|y - y_i| < l_max + ||l||_1 D_sigma`. Between the `i`-th and `j`-th
vertices of the `V`-tiling lie `|j - i|` tiles of length at least `l_min`,
so `|j - i| < (l_max + ||l||_1 D_sigma) / l_min`, and
`||pi(V[j]) - pi(V[i])||_inf <= |j - i|`. Adding the two bounds gives the
claim; the vertex count follows from Lemma 1.1 since `i, j` range over `A`
and `w` over a box. ∎

*Remarks.* (i) Only primitivity and the Pisot spectrum enter, through
`D_sigma`; unimodularity, irreducibility and legality of `ab` are not used.
(ii) The manuscript's Section 4.7 obtained finiteness of *realized* overlaps
of two tilings in one fibre from finite local complexity and the Meyer
property; Theorem 2.1 gives it for the seed-patch graph directly and
elementarily, and it removes the theorem target "finite-type consequence"
(item 5) of `docs/p1b-overlap-realization-bridge.md`. (iii) The state cap
in the canonical implementation is now only a fail-closed guard; it can never
bind for a correct implementation, and the census of Section 5 confirms it
never does on the corpus.

## 3. Geometry of coincidence

The following two lemmas are the dictionary between blocks and tiles. They use
the manuscript's Lemma 2.3 (`Q`-independence of the `l_a`, which needs
irreducibility of `chi_M`).

**Lemma 3.1 (zero returns are common vertices).** Let `(u, v)` be a balanced
pair, both words tiling `[0, g(u))`. A point is a vertex of both tilings if
and only if it equals `g(u[k]) = g(v[k])` for a zero return `k` of `(u, v)`.

*Proof.* If `g(u[i]) = g(v[j])` then `<l, pi(u[i]) - pi(v[j])> = 0` with an
integer vector, so `pi(u[i]) = pi(v[j])` by `Q`-independence; applying
`<1, .>` gives `i = j`, and then `D(i) = 0`. The converse is immediate. ∎

**Lemma 3.2 (common tiles are coincidence blocks).** A tile belongs to both
tilings of a balanced pair `(u, v)` if and only if it is the tile of a
coincidence block `(c, c)` of `red(u, v)`.

*Proof.* A common tile `[x, x + l_c)` has both endpoints common vertices,
hence (Lemma 3.1) zero returns `k, k+1` with `u_{k+1} = v_{k+1} = c`, i.e. a
block `(c, c)`. Conversely a coincidence block is a common tile. ∎

By the manuscript's Lemma 2.12 the depth-`m` descendants of a state
`T = (u, v)` are the blocks of `red(sigma^m(u), sigma^m(v))`, and they tile
`[0, beta^m g(T))`. Hence: **`T` is productive iff for some `m` the tilings by
`sigma^m(u)` and `sigma^m(v)` share a tile; `T` is nonproductive iff they
never do.**

## 4. Coincidence density and Level 3 without G1

For a balanced pair `T = (u, v)` and `m >= 0` let `C_m(T)` be the total
length of the common tiles of the tilings by `sigma^m(u)` and `sigma^m(v)`,
and `f_m(T) := C_m(T) / (beta^m g(T))` the *common fraction*. For a reachable
state `T` its *overlaps* are the overlaps of the pair `(u, v)` (top tiles from
`u`); they are vertices of `O_sigma` (Lemma 1.1). An overlap is *productive*
if some descendant is a coincidence.

**Theorem 4.1.** Let `sigma` be PIP, `s` a swap seed and `T` a state
reachable from `s`.

1. (monotonicity) `f_{m+1}(T) >= f_m(T)`; the limit `delta(T) := lim f_m(T)`
   exists in `[0, 1]`.
2. (productivity) `T` is productive iff `delta(T) > 0` iff some overlap of
   `T` is productive.
3. (density one) If every vertex of `O_sigma` reachable from the seed
   overlaps of `s` is productive, then `delta(T) = 1` for every `T` reachable
   from `s`. Conversely, if `delta(s) = 1` then every such overlap is
   productive.
4. (Level 3 without G1) If `delta(s) = 1` then every state reachable from
   `s` is productive. In particular, if every vertex of `O_sigma` is
   productive then every reachable state of `B_sigma` is productive, whether
   or not `B_sigma` is finite.
5. (under finiteness) If the set of states reachable from `s` is finite, then
   `delta(s) = 1` iff every state reachable from `s` is productive iff the
   balanced-pair algorithm terminates with coincidence from `s`.

*Proof.* (1) A common tile of type `c` at level `m` inflates to the supertile
`sigma(c)` at level `m+1`, all of whose tiles are common; so
`C_{m+1} >= beta C_m`.

(2) By Lemma 3.2, `T` productive iff some level `m` has a common tile iff
`C_m > 0` for some `m` iff `delta > 0` (by (1)). A common tile at level `m`
inside `[0, beta^m g(T))` is a coincidence overlap; its ancestors at level 0
are the two level-0 tiles containing it, which overlap, so it descends from an
overlap of `T`. Conversely a coincidence descending from an overlap of `T` is
a common tile inside the interval of `T` at that level.

(3) Let `S` be the set of vertices of `O_sigma` reachable from the seed
overlaps of `s`; it is finite by Theorem 2.1. If all are productive there is
`K` such that every non-coincidence vertex of `S` has a coincidence
descendant within `K` levels. Fix a level and a non-common top tile `tau`
(length `l_tau`). Its interior is covered by bottom tiles, so `tau` belongs
to some overlap `O`, which is not a coincidence; `O` has a coincidence
descendant within `k <= K` levels, a common tile `c` inside `beta^k tau`, and
`K - k` further inflations make it a common supertile of length
`>= l_min` inside `beta^K tau`. So the non-common length inside `beta^K tau`
is at most `beta^K l_tau - l_min <= (1 - eps) beta^K l_tau` with
`eps := l_min / (beta^K l_max) > 0`. Non-common tiles at level `m + K` lie in
inflations of non-common tiles at level `m` (common tiles stay common), so
the non-common length `NC` satisfies `NC_{m+K} <= (1 - eps) beta^K NC_m`, and
`1 - f_{m+jK}(T) <= (1 - eps)^j (1 - f_m(T)) -> 0`. Conversely, let `O` be a
nonproductive overlap occurring at level `N` of `s`, with intersection of
length `lambda > 0`. At level `N + m`, no tile of `U` inside
`beta^m (top ∩ bottom)` is common: a common tile there would be a coincidence
overlap descending from `O`. Hence
`1 - f_{N+m}(s) >= (beta^m lambda - 2 l_max) / (beta^{N+m} g(s))`, whose limit
`lambda / (beta^N g(s))` is positive, so `delta(s) < 1`.

(4) If `T` is a nonproductive state at depth `j` below `s`, then at depth
`j + m` all top tiles inside the interval of `T` are non-common (Lemma 3.2),
so `1 - f_{j+m}(s) >= beta^m g(T) / (beta^{j+m} g(s)) = g(T) / (beta^j g(s))`
for all `m`, and `delta(s) < 1`. The second sentence combines this with (3).

(5) By (4), `delta(s) = 1` forces productivity of all reachable states. If
the reachable set is finite and every state is productive, there are `K` and
`eps > 0` such that every noncoincident state has, among its depth-`K`
descendants, coincidence blocks of total length `>= eps beta^K g(T)` (finitely
many states, each with a coincidence descendant at some depth `<= K`, whose
inflation to depth `K` has length `>= l_min`). Then `NC_{m+K} <= (1 - eps)
beta^K NC_m` as in (3) and `delta(s) = 1`. Termination with coincidence is,
by definition, finiteness plus productivity of all reachable states. ∎

**Corollary 4.2 (mass balance on overlaps).** For an overlap `O` of type
`(i, j, t)`, `t = <l, w>`, the intersection length is `lambda(O) = <l, v(O)>`
with `v(O) in {e_i, e_j, e_j + w, e_i - w}` (top inside bottom, bottom inside
top, bottom starts before the top, top starts before the bottom). The
geometric children of `O` (all overlapping pairs of sub-tiles; for a
non-coincidence these are its children in `O_sigma`) partition the inflated
intersection, so `sum v(child) = M v(O)` over them (by `Q`-independence).
Hence for any nonempty set `S` of non-coincidence overlaps closed under
children, the child-count matrix
`N_S` satisfies `N_S lambda_S = beta lambda_S` with `lambda_S > 0`, so
`rho(N_S) = beta`, and `N_S V_S = V_S M^T` for the matrix `V_S` with rows
`v(O)^T`. This is the overlap analogue of the manuscript's Theorem 5.2.

**Corollary 4.3 (sink reduction on overlaps).** Since `O_sigma` is finite,
some overlap is nonproductive iff `O_sigma` contains a closed nonproductive
strongly connected component (the manuscript's Theorem 5.1 applied verbatim
to the finite graph `O_sigma`).

## 5. Exact census (finite evidence)

Canonical run `mojo/swap_overlap_census.mojo` (exact Sturm-sequence PIP
screening; shifts in `Z[beta]`; every sign decided exactly), independent
Python oracle `scripts/swap_overlap_census.py` (`src/psc_research/overlap_graph.py`,
elements of `Q(beta)` as polynomials modulo the irreducible cubic, signs by
certified interval refinement):

| quantity | value |
| --- | --- |
| PIP specimens (images of length `<= 3`) | 4,554 |
| seed-patch overlap graphs built / capped (cap 20,000) / failed | 4,554 / 0 / 0 |
| largest seed-patch overlap graph | 2,640 vertices |
| total vertices over the corpus | 1,118,850 |
| specimens with a nonproductive overlap | 0 |

By Theorem 4.1(5) and the automaton census (every `B_sigma` in the corpus is
finite and productive), `delta(s) = 1` for every seed of every specimen, so
by Theorem 4.1(3) every overlap must be productive; the census confirms this
independently. Exact common fractions (common tiles over all tiles, a
normalisation-free surrogate for `f_m`) for the seed `(12, 21)` at levels
`0..10`: Tribonacci `0/2, 1/4, 3/7, 7/13, 16/24, 33/44, 65/81, 127/149,
244/274, 461/504, 867/927`; the non-unimodular example `tau` of the
manuscript `0/2, 1/4, 4/10, 11/22, 26/50, 62/114, 145/258, 335/586,
775/1330, 1799/3018, 4166/6850`. None of this is evidence about substitutions
outside the corpus.

## 6. Consequences for the programme, and the one open bridge

1. **Level 3 in G1-free form.** Define *Level 3'*: every vertex of `O_sigma`
   is productive. By Theorem 4.1(4), Level 3' implies that every reachable
   state of `B_sigma` is productive, hence SCC Producer, with no finiteness
   hypothesis; under G1 the two are equivalent (Theorem 4.1(3),(5)). The
   block-level tools of the manuscript (Parikh intertwiner, orientation
   cocycle, defect sieves) presuppose a finite strict component; Level 3'
   asks the same question on a graph that is finite unconditionally
   (Theorem 2.1), with the mass balance of Corollary 4.2 available.
2. **G1 is exactly bounded chain length.** A reachable state of length `n` is
   a chain of between `n` and `2n - 1` consecutive overlaps with no common
   vertex inside. Theorem 2.1 bounds the number of overlap *types*; G1 asks
   that only finitely many *chains* occur, i.e. that common vertices are
   uniformly relatively dense in every swap pair (the swap-pair form of the
   manuscript's Conjecture 4.21).
3. **The bridge.** The manuscript's Imported Theorem 2.16 gives PDS from
   *termination* (finiteness plus productivity) for a legal seed. The open
   question that would remove G1 from the route to PDS is:

   > **Question 6.1.** Let `sigma` be PIP and `ab` a legal factor. Does
   > `delta((ab, ba)) = 1` (equivalently, productivity of every overlap
   > reachable from the seed overlaps of `(ab, ba)`) imply pure discrete
   > spectrum, without assuming that `B_sigma` is finite?

   The natural sources are the overlap-coincidence criterion of Solomyak
   (`Solomyak97`, with Akiyama–Lee `AL`) and the coincidence-density
   formulations of Sirvent–Solomyak `SS` and Barge–Kwapisz; the missing step
   is the identification of the seed-patch overlaps with realized overlaps of
   two tilings (items 1–4 of `docs/p1b-overlap-realization-bridge.md`), which
   this note does not supply. If Question 6.1 has a positive answer then PDS
   follows from Level 3' for one legal seed with no finiteness hypothesis.
   That would not settle G1: the converse of Imported Theorem 2.16 (PDS
   implies termination for a legal seed) is only recorded in the literature
   and not used here, and G1 concerns all seeds, legal or not (the
   manuscript's Open Problem 4.24). The bridge would change the role of G1
   in the route to PDS, not its status.

In the manuscript these results are Theorem 4.22 (finiteness), Lemmas 5.30–5.31, Theorem 5.32 (coincidence density), Corollary 5.33, and Open Problems 5.34 (overlap productivity) and 5.35 (density bridge).

Nothing in this note proves Level 3', G1, or PSC.
