# P1b: PeriodicPairVertexCoincidence is decidable per substitution — 2026-10-02

**Status:** research note for issue #139, proved here and not yet reviewed.
Proposition V reduces PeriodicPairVertexCoincidence, for one substitution and
**every** `r` at once, to a property of one finite graph, and
`mojo/psc/vertex_coincidence.mojo` decides it exactly. The general statement,
for every PIP substitution, is **not** proved. §5 explains why it carries the
weight of an open problem. Nothing here is promoted to the ledger or the
manuscript.

Dependencies: `p1b-strict-zipper-periodic-pair-2026-10-02.md` (Lemma C,
Theorem B, Corollary B′); manuscript Theorem 4.22, Lemma 5.45 and Proposition
5.47.

## 1. The statement

*PeriodicPairVertexCoincidence for `sigma`* (PPVC(`sigma`)). For every
`r >= 1` and every pair of interior occurrences `sigma^r(i) = P i U`,
`sigma^r(j) = Q j V` whose centre offset
`w_0 = (M^r − I)^{−1}(pi(P) − pi(Q))` is integral, the `Phi^r`-fixed tilings
`T(i, P)` and `T(j, Q) + <ell, w_0>` share a vertex. By Proposition F and
Theorem R of `p1b-periodic-pair-fibre-literature-gate-2026-10-02.md`, these
are exactly the pairs of `Phi^r`-fixed tilings in one fibre with a common
centre and integral offset.

By Corollary B′, PPVC(`sigma`) excludes strict zippers from every swap seed,
so by manuscript Proposition 5.47 it gives G1 for `sigma`.

## 2. Proposition V (the box graph)

Notation: overlaps `(i, j, t)` with `t = <ell, w>`, `w ∈ Z^3`, and children as
in the manuscript. `F` is the set of single-inflation increments
`c = <ell, pi(q) − pi(p)>`. For each contracting conjugate `sigma_k` (two real
ones, or one complex `varsigma` counted twice):

- `mu_k = |sigma_k(beta)| < 1`;
- `C_k = max_{c ∈ F} |sigma_k(c)|`;
- `B_k = C_k / (1 − mu_k)`.

Let `theta_0, theta_1, theta_2 ∈ Q(beta)` be the trace-dual basis of the tile
lengths, `Tr(theta_m ell_a) = delta_{ma}`. Let `R_m` be an integer with

`R_m >= |theta_m| ell_max + sum_k |sigma_k(theta_m)| B_k`.

*Proposition V.* Let `sigma` be PIP and let `𝔅` be the closure under
inflation of a finite set of overlaps that contains every overlap with
`|w_m| <= R_m` (`m = 0, 1, 2`). Then:

1. every overlap lying on a cycle of the overlap graph belongs to `𝔅`;
2. PPVC(`sigma`) holds iff every vertex of `𝔅` has an offset-zero descendant
   (the vertex itself included).

*Proof.*

1. **Cycle vertices are in the box.** Along a cycle
   `t_{s+1} = beta t_s + c_s` with `c_s ∈ F`, so
   `sigma_k(t_{s+1}) = sigma_k(beta) sigma_k(t_s) + sigma_k(c_s)`. The
   sequence is periodic, so
   `sigma_k(t_0) = sum_{n >= 0} sigma_k(beta)^n sigma_k(c_{−n−1})` (indices
   mod the period). Hence `|sigma_k(t_0)| <= B_k`. Also `|t_0| < ell_max`,
   since an overlap's tiles meet. Finally,
   `w_m = Tr(theta_m t) = sum_sigma sigma(theta_m) sigma(t)` over all three
   embeddings, which gives `|w_m| <= R_m`.
2. **(⇐).** Given `r` and a pair with integral `w_0`, Theorem B(2) puts
   `v_0 = (i, j, w_0)` on an `r`-cycle. By step 1, `v_0 ∈ 𝔅`, so `v_0` has
   an offset-zero descendant. By Theorem B(3), (a) fails, so (b) fails: the
   two tilings share a vertex.
3. **(⇒).** Let `Y` be the set of vertices of `𝔅` with no offset-zero
   descendant. A child of a vertex of `Y` is in `Y`, and `𝔅` is finite, so
   `Y` is a finite set closed under children. If `Y ≠ ∅`, Lemma C gives a
   cycle in `Y` with interior centre. The converse of Theorem B turns it into
   interior occurrences with integral `w_0` satisfying (a), hence (b): two
   tilings with no common vertex. So PPVC(`sigma`) fails.

`square`

**Remarks.**

- `𝔅` is finite. The offsets with `|w_m| <= R_m` are finitely many.
  Descendants keep `|t| < ell_max`, and by the recursion in step 1 their
  contracting conjugates stay bounded. The points of `Z^3` with all three
  embeddings bounded are finitely many, because the Minkowski image of
  `Z⟨ell⟩` is a lattice.
- A larger start set changes no verdict. Step 3 turns any offset-zero-free
  vertex reached from it into a genuine counterexample. So the start set
  needs only to contain the box, and the implementation enumerates a
  superset.
- The same graph gives a uniform depth. Among the vertices on cycles, let
  `K_V` be the largest first left-aligned depth. Every periodic pair of
  §1, for every `r`, shares a vertex within `K_V` levels of its common
  centre's overlap.
- The finite-graph principle is that of the Akiyama–Lee overlap algorithm.
  It decides overlap coincidence (hence pure discrete spectrum) on the
  overlaps of legal tilings. Proposition V applies the same principle to a
  weaker target, offset zero rather than coincidence. Its vertices are the
  integral offsets, and its equivalence with the periodic-pair statement goes
  through Theorem B. No new literature is relied on; see
  `p1b-strict-zipper-literature-gate-2026-09-21.md` §5 for Akiyama–Lee.

## 3. Exact certificate (`psc.vertex_coincidence`)

- **Radii.** Every bound is a rational upper bound of a real algebraic
  number, certified by exact sign tests at isolated roots of the
  characteristic polynomial (`psc.real_root_sign`):
  - at a real root, `|sigma_k(x)| < q` iff `q − x` and `q + x` are positive
    there;
  - for a complex pair, `|varsigma(x)|^2 = N(x)/x`, and `q^2 > N(x)/x` iff
    `q^2 x − N(x)` has the sign of `x` at `beta`.

  `mu_k` is refined until its bound is below 1, and the trace-dual basis is
  solved over `Q`.
- **Start set.** The two coordinates with the smaller radii are looped over.
  The third is solved for: `t` increases with it, so the slab
  `−ell_max < t < ell_max` is an integer interval, found by exact monotone
  sign scans. Each `(i, j)` is kept when the overlap is interior (exact
  test). No floating value is used anywhere.
- **Verdict.** The closure is `build_overlap_graph_from_seeds`, and offset-zero
  reachability is `first_left_aligned_depths`, both the exact kernels of
  `psc.overlap_seed_patch`. A capped closure is reported as capped.
- **Cross-check.** An uncommitted floating-point oracle builds the box from
  approximate eigenvectors with a different bound and start set. The
  recurrent part (non-coincidence vertices on cycles) and its deepest first
  left-aligned depth do not depend on the start set. They agree exactly with
  the Mojo values: Tribonacci 14 and 3, the cube specimen
  `0 -> 1, 1 -> 222, 2 -> 0222` 1,166 and 17, the golden pump
  `0 -> 1, 1 -> 021, 2 -> 001` 716 and 15. For the cube specimen `K_V = 17`
  equals the `K'` of its seed-patch graph.
- **Regression.** `mojo/tests/test_vertex_coincidence.mojo` pins these values.
  It also checks every integral centre offset of Tribonacci (`r <= 6`) and the
  golden pump (`r <= 4`) against the radii, which tests step 1 against
  Theorem B. It checks that every cycle vertex of the cube specimen's
  seed-patch graph lies in its box graph, and that a capped run gives no
  verdict.

## 4. Census

`mojo/vertex_coincidence_census.mojo` (pixi task `vertex-coincidence-census`)
runs the exact decision on every specimen. It folds in canonical order on
`parallel_fold`, so the result does not depend on the worker count.

| Domain | specimens | PPVC holds for every `r` | capped | largest box graph | recurrent vertices (max / total) | largest `K_V` |
| --- | --- | --- | --- | --- | --- | --- |
| standing corpus (images of length <= 3) | 4,554 | 4,554 | 0 | 249,385 (`6 11 13`) | 2,676 (`4 11 21`) / 1,174,788 | 17 (`1 23 21`) |
| total image length <= 8 | 24,486 | 24,486 | 0 | 1,342,201 (`1 38 56`) | 14,938 (`1 254 4`) / 7,891,548 | 25 (`1 38 56`) |

Wall-clock times on 4 workers were 7 and 49 minutes. The uncommitted
floating-point oracle of §3 reproduces the standing-corpus row
independently: no failure, 1,174,788 recurrent vertices in total, at most
2,676 per specimen, deepest recurrent depth 17.

*Finite-domain theorem.* For every PIP substitution on three letters with
images of length at most 3, or with total image length at most 8, and for
every `r >= 1`, any two `Phi^r`-fixed tilings with a common centre and
integral centre offset share a vertex. Hence no strict zipper is reachable
from any swap seed (Corollary B′). For the first domain the balanced-pair
builds already certify G1 directly; for the second domain Remark 3 of the
depth note already gives G1 through all-seed overlap productivity. What is new
is the periodic-pair statement for **all** `r`, not only the seed-reachable
part, and the uniform depth `K_V`.

## 5. What this does not establish

- PPVC is not proved for all PIP substitutions. For every PIP `sigma` it
  implies G1 for `sigma`, through Corollary B′ and Proposition 5.47. A proof
  for all PIP `sigma` would therefore settle balanced-pair finiteness for all
  three-letter Pisot substitutions. That is the ledger's open G1; in the
  literature it is known for two letters (Hollander–Solomyak) and open beyond.
- Proposition V is a decision procedure, not a uniform bound. Its radii and
  `K_V` depend on `sigma`. A uniform proof would need a reason why the box
  graph of every PIP substitution has no offset-zero-free closed set, which
  is the strict-zipper exclusion itself.
- The census is a finite-domain theorem about the specimens it covers, by
  exact certificate. It says nothing outside them.
