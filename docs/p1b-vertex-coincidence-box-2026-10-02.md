# P1b: PeriodicPairVertexCoincidence is decidable per substitution — 2026-10-02

**Status:** research note for issue #139, proved here and not yet reviewed.
Proposition V reduces PeriodicPairVertexCoincidence, for one substitution and
**every** `r` at once, to a property of one finite graph, and
`mojo/psc/vertex_coincidence.mojo` decides it exactly. The general statement,
for every PIP substitution, is **not** proved. §6 explains why it carries the
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
| images of length <= 4 | 135,990 | 135,990 | 0 | 1,432,357 (`25 84 41`) | 27,692 (`23 12 97`) / 75,080,616 | 26 (`13 57 12`) |

Wall-clock times on 4 workers were 7 and 49 minutes for the first two rows. The
third row ran in 28 resumable slices (`len4 START END`), 5.8 hours in total;
its labels index `image_words_up_to(4)`. Its deepest specimen,
`0 -> 001, 1 -> 0200, 2 -> 000` (`K_V = 26`), has `mu ≈ 0.9651`, well inside
Conjecture UH's `3.2 / log(1/mu) ≈ 90`. `K_V` by regime over this domain:
unimodular, two real conjugates 1:6 2:2118 3:6948 4:5820 5:2742 6:1410 7:324;
unimodular complex pair 1:48 2:3858 3:13266 4:9912 5:3822 6:960 7:252 8:30
9:36 14:12; `abs(det M) > 1` 2:72 3:2460 4:16332 5:19542 6:14574 7:7110
8:3540 9:2874 10:3744 11:5598 12:3648 13:1242 14:1098 15:1068 16:516 17:156
18:108 19:72 20:24 22:84 23:228 24:180 25:132 26:24. Unimodular specimens
still have `K_V <= 9`, apart from 12 at `K_V = 14`, matching the
plastic-number class of the standing corpus. The uncommitted
floating-point oracle of §3 reproduces the standing-corpus row
independently: no failure, 1,174,788 recurrent vertices in total, at most
2,676 per specimen, deepest recurrent depth 17.

*Guarding, row by row.* Each row is an exact run of the committed driver,
but they are not guarded equally:

- **Standing corpus: CI-pinned.** The `vertex-coincidence-census` job of
  `.github/workflows/ci.yml` reruns it and checks every summary line above
  exactly.
- **Two slices: regression-pinned.** `test_census_slices_are_pinned` in
  `mojo/tests/test_vertex_coincidence.mojo` pins the first 300 standing
  specimens and the first 100 specimens with images of length at most 4,
  without the parallel fold. Every one holds; the recurrent totals, `K_V` and
  box-graph sizes are pinned.
- **Total length at most 8, and images of length at most 4: recorded runs
  only.** Their wall-clock (49 minutes; 5.8 hours) puts them outside CI. They
  are reproducible with `pixi run vertex-coincidence-census total` and with
  the `len4 START END` slices, and they are not guarded by CI.

*Finite-domain statement.* On the standing corpus, as an exact certificate
guarded by CI: for every PIP substitution on three letters with images of
length at most 3 and every `r >= 1`, any two `Phi^r`-fixed tilings with a
common centre and integral centre offset share a vertex. Hence no strict
zipper is reachable from any swap seed (Corollary B′), and G1 holds by
manuscript Proposition 5.47; the balanced-pair builds already certify G1
there directly. The recorded runs give the same statement for total image
length at most 8, where Remark 3 of the depth note already gives G1, and for
images of length at most 4. In the last domain, 121,320 specimens lie in
neither of the other two (count by the uncommitted floating-point PIP
screen); for them the recorded run is, as far as this repository records,
the only evidence of G1, and it is not CI-guarded. Everywhere the census adds
the periodic-pair statement for **all** `r`, not only the seed-reachable
part, and the uniform depth `K_V`.

## 5. What the data says about a general proof

### 5.1 A sandwich (proved)

*Theorem S.* For PIP `sigma`: pure discrete spectrum ⇒ PPVC(`sigma`) ⇒ G1
for `sigma`.

*Proof.*

- **PDS ⇒ PPVC.** If PPVC(`sigma`) fails, Proposition V gives a pair
  `T(i, P)`, `T(j, Q) + <ell, w_0>` with no common vertex, hence no common
  tile. By Proposition F with Theorem R, the two tilings lie in one fibre of
  the maximal equicontinuous factor. Barge 2013, Theorem 4(3),(5) (from
  Barge–Kellendonk) then gives coincidence rank at least 2, hence no pure
  discrete spectrum.
- **PPVC ⇒ G1.** Corollary B′ with manuscript Proposition 5.47.

`square`

So a failure of PPVC, which Proposition V would detect in finite time, is a
counterexample to the Pisot conjecture for that `sigma`. PPVC holds wherever
pure discrete spectrum is known, for example Barge's class of substitutions
injective on initial letters and constant on final letters, and Pisot
`beta`-substitutions. Neither class adds anything to G1, which pure discrete
spectrum already implies there.

### 5.2 Mechanisms the data rules out (exploratory)

An uncommitted floating-point miner was run on the box graphs of the three
named specimens. It searched for a local reason why every vertex reaches
offset zero, because a provable local reason would close the problem. Three
candidates fail.

- **One-step descent of the contracting size.** Candidate: every
  non-offset-zero recurrent vertex has a child with smaller
  `sum_k |sigma_k(t)|^2` (or smaller `max_k |sigma_k(t)|/B_k`). This fails on
  234 of the 1,166 recurrent vertices of the cube specimen and on 140 of the
  716 of the golden pump. A smaller descendant always exists within 5 levels
  there, but that is implied by reaching offset zero and is no mechanism.
- **Endpoint hitting.** Candidate: the first common vertex is an endpoint of
  the vertex's region, i.e. it is reached along the leftmost or rightmost
  child chain. This holds for all 14 recurrent vertices of Tribonacci and for
  1,053 of the 1,166 of the cube specimen, but only for 8 of the 716 of the
  golden pump. The common vertex is in general interior, consistent with the
  six-edge affine pump on that specimen
  (`p1-overlap-affine-pump-2026-09-15.md`).
- **Magnitude plus a constant.** Candidate: the first-hit depth is at most
  the contracting lower bound `m_0(t)` of manuscript Proposition 5.42 plus a
  uniform constant. On the seed-patch graphs of the corpus the excess
  `b − m_0` already reaches 14
  (`overlap-finiteness-and-coincidence-density-2026-09-13.md`), so no small
  uniform constant is visible.

### 5.3 Where the depth sits (exact census)

`K_V` by specimen over the standing corpus, split by arithmetic regime
(`vertex_coincidence_census.mojo`):

| Regime | `K_V`: specimens |
| --- | --- |
| unimodular, two real conjugates | 2:108 3:198 4:234 5:102 6:6 |
| unimodular, complex pair | 2:210 3:612 4:588 5:336 6:120 7:84 8:18 14:12 |
| `abs(det M) > 1` | 4:24 5:138 6:252 7:288 8:360 9:228 10:192 11:120 12:36 13:48 14:72 15:120 16:36 17:12 |

Unimodular specimens have `K_V <= 8`, apart from one class of 12 with
`K_V = 14`. Non-unimodular specimens reach 17. A first reading put the extra
depth in the `M`-adic coordinates. §§5.4–5.5 show that the contraction rate
explains it better, in both regimes.

### 5.4 Excess over the contracting bound (exact census)

`vertex_excess_census.mojo` compares, on every non-coincidence cycle vertex
of every box graph, the first left-aligned depth `b` with the contracting
lower bound `m_0` of manuscript Proposition 5.42. It checks `m_0 <= b`
everywhere. Specimens by maximal excess `b − m_0`:

| Regime | largest `m_0` | maximal excess: specimens |
| --- | --- | --- |
| unimodular, two real conjugates | 4 | 0:6 1:120 2:270 3:198 4:54 |
| unimodular, complex pair | 3 | 1:246 2:600 3:576 4:324 5:126 6:78 7:18 12:6 13:6 |
| `abs(det M) > 1` | 9 | 2:12 3:108 4:240 5:354 6:432 7:264 8:168 9:108 10:78 11:96 12:42 13:18 14:6 |

The 12 unimodular specimens with excess 12–13, and `K_V = 14`, are one
relabelling and reversal class: `0 -> 1, 1 -> 2, 2 -> 01` and its images, with
characteristic polynomial `x^3 − x − 1`. Their Perron root is the plastic
number, the smallest Pisot number. Their complex conjugates have modulus
`mu ≈ 0.8688`, the slowest contraction in the unimodular corpus.

### 5.5 An empirical law: depth is set by the contraction rate

Let `mu = max_k |sigma_k(beta)|` be the slowest contraction. For a complex
pair, `mu^2 = abs(det M)/beta`, so a determinant above 1 slows contraction.
Over the standing corpus (uncommitted floating-point oracle, which reproduces
the exact `K_V` of every specimen):

- `K_V · log(1/mu)` lies in `[0.441, 3.164]`;
- the correlation of `K_V` with `1/log(1/mu)` is `0.923`;
- every specimen with `K_V >= 15` has `mu ≈ 0.9387`, and every specimen with
  `K_V <= 3` has `mu <= 0.802`.

So the first common vertex of every cycle vertex appears within about three
e-foldings of contraction, `K_V <= 3.2 / log(1/mu)`, in every regime. The
determinant matters only through `mu`, and the plastic-number class is the
unimodular extreme of the same law.

*Conjecture UH (uniform hitting scale).* There is an absolute constant `c`
such that for every PIP `sigma` on three letters,
`K_V(sigma) <= c / log(1/mu(sigma))`. The standing corpus is consistent with
`c = 3.2`.

UH implies PPVC, hence G1, and adds an explicit depth. It is stated so that
it can be refuted by one specimen. Its form says which kind of proof to look
for: a contracting-space argument at a fixed scale relative to the
contraction. Concretely, once a cycle vertex's contracting offset has shrunk
by a fixed factor `e^{−c}`, its region must contain a common vertex. That is
a uniform covering statement for the Rauzy-type sets of the box graph, at
one scale. It is not a statement about arbitrarily fine scales, which is
where the density arguments of the stop list fail.

### 5.5a Depth laws checked exactly on images of length at most 4

`vertex_coincidence_census.mojo len4 START END records` printed the exact
`K_V` of each of the 135,990 specimens with images of length at most 4, in 28
slices (every specimen holds, none capped). `vertex_depth_law.mojo FILE 4`
(kernel `psc.depth_law`) judges each record against a law
`K_V <= a + c / log(1/mu)`, exactly:

- `mu^2` is enclosed in a rational bracket: `abs(det M) / beta` for a complex
  pair, the larger squared real conjugate otherwise. Both come from
  isolating intervals of the characteristic polynomial, refined by exact
  bisection.
- For `K_V > a` the law is `(mu^2)^(K_V − a) >= (e^(−c))^2`, tested against a
  rational bracket of `e^(−c)`.
- A specimen not decided within 80 bisections is reported as undecided and
  counted as neither verdict.
- `tests/test_depth_law.mojo` pins a violator, two holding specimens and a
  hypothetical failure of the affine law.

Result (3 min 48 s):

| law | holds | violates | undecided |
| --- | --- | --- | --- |
| `K_V <= 3.2 / log(1/mu)` | 134,484 | 1,506 | 0 |
| `K_V <= 4 / log(1/mu)` | 135,918 | 72 | 0 |
| `K_V <= 7 + 1/log(1/mu)` | 135,990 | 0 | 0 |

*Reading.*

- Conjecture UH asserts that **some** absolute constant `c` works. These
  counts reject the standing-corpus calibration `c = 3.2` and also `c = 4`,
  but UH itself stays open: no finite domain can refute an existential
  constant.
- `tests/test_depth_law.mojo` pins `0 -> 2220, 1 -> 100, 2 -> 0012`, with
  `K_V = 6` and `mu ≈ 0.51`, as a violator of both ratio laws. Fast
  contraction with a depth floor is what defeats a pure ratio `c / log(1/mu)`.
- The affine form survives on this domain. *Empirical envelope E7*:
  `K_V <= 7 + 1/log(1/mu)` holds on all 135,990 specimens, exactly
  certified.
- E7 is recorded as an observation, **not** as a conjecture. Stating it as
  a universal invariant needs the targeted literature stop/go check of
  `AGENTS.md` first, which has not been done.
- An earlier draft of this section tabulated floating-point estimates of
  the envelope constant for each offset and extrapolated an equality beyond
  the offsets shown. Those estimates came from an uncommitted script and are
  withdrawn; the exact counts above replace them.

### 5.5b Targeted search where contraction is slowest (exploratory sample)

A strict zipper, and with it a counterexample to the Pisot substitution
conjecture for its substitution (Theorem S), is most plausible where `mu` is
close to 1. `vertex_coincidence_targeted.mojo 5 39 40 40` selects, exactly,
the PIP substitutions with images of length at most 5, a complex contracting
pair and `mu^2 = abs(det M)/beta > (39/40)^2`. There are 40,680 of them, and
none have `mu > 0.98`. It decides PPVC on a deterministic sample of every
40th candidate in canonical order, 1,017 specimens, with the state cap
4,000,000 per box graph:

```text
decided: 1017  holds for every r: 993  capped: 24  fails: 0
deepest K_V: 39 specimen 17 135 239  largest box graph: 3995093
```

(96 minutes on 4 workers.) No sampled specimen fails. The 24 capped
specimens are inconclusive at this state cap and are not verdicts. The
deepest specimen is `0 -> 012, 1 -> 00120, 2 -> 11102` (labels index
`image_words_up_to(5)`), with `K_V = 39`. `vertex_depth_law.mojo` certifies
exactly that it satisfies all three laws of §5.5a, envelope E7 included.

This is a sample, labelled as such, and not a census. It says nothing about
the other 39,663 candidates or about the 24 capped ones.

### 5.6 Working the argument: cancellation, not shrinkage

*Lemma D (discreteness, proved).* There is `epsilon_0(sigma) > 0` such that
an overlap `(i, j, t)` with `|sigma_k(t)| < epsilon_0` for every contracting
`k` has `t = 0`.

*Proof.* `|t| < ell_max` for every overlap. The Minkowski image of `Z⟨ell⟩` is
a lattice in `R^3`, so only finitely many offsets have all three embeddings
bounded. Take `epsilon_0` below the smallest nonzero contracting size among
them. `square`

So a vertex hits exactly when some descendant enters the
`epsilon_0`-ball in the contracting coordinates. Conjecture UH would follow if
contracting sizes shrank geometrically along some descendant path. That would
give depth about `L = log(B/epsilon_0) / log(1/mu)`, where `B` is the largest
contracting size on the recurrent part.

The data rules this mechanism out. On a stride-7 sample of 651 corpus
specimens (uncommitted oracle), `K_V − L` ranges from −33.75 to 5.00, and
`K_V / L` from 0.32 to 2.56. For example, `0 -> 22, 1 -> 001, 2 -> 10` has
`L ≈ 49.8` and `K_V = 16`. Hits happen long before the offset is small, by
**exact cancellation**: `beta^m t` lands on a prefix difference
`<ell, pi(q) − pi(p)>` while `|sigma_k(beta^m t)|` is still of order `B`.

The lattice form makes this precise. By Theorem B(3)(c), `(i, j, w)` hits at
depth `m` iff `M^m w ∈ P_m(i) − P_m(j)`. Equivalently, the staircase of
`sigma^m(j)`, translated by `M^m w`, shares a lattice vertex with the
staircase of `sigma^m(i)`. Both staircases lie in strips of `Z^3` along the
expanding line. Their contracting windows differ by
`sigma_k(M^m w) = lambda_k^m sigma_k(w) → 0`.

- **Under pure discrete spectrum.** Each staircase is, up to its boundary,
  every lattice point of its strip whose contracting coordinate lies in its
  window (the model-set property), so two staircases with overlapping
  windows must meet. This is the mechanism behind Theorem S.
- **Without it.** Each staircase is a proper subset of lattice density
  `1/p` inside the same model set, and meeting is a rigidity question about
  the substitutive hierarchy.

The census says this rigidity holds on every specimen surveyed, and holds
quickly: within about three e-foldings of contraction. A proof has to show
that two such staircases, produced by the same substitution from letters
`i` and `j` and shifted by an integral offset of a cycle vertex, cannot
interleave without a common vertex. That is the strict-zipper exclusion in
its sharpest lattice form. Lemma D and the sample above are what working the
argument has added: the obstruction is exact combinatorial interleaving, not
a size or scale effect.

### 5.6a The plastic-number class and the climb lemma

The 12-specimen outlier class of §5.4 is a model problem. Its box graph has
74 recurrent vertices, and the deepest are all same-letter self-overlaps with
offsets `±beta^{−k}`. For `0 -> 1, 1 -> 2, 2 -> 01`, `(0, 0, (1,1,−1))` has
`t = beta^{−2}` and depth 14, `(1, 1, (−1,0,1))` has `t = beta^{−1}` and depth
13, and `(2, 2, (1,0,0))` has `t = 1` and depth 12 (uncommitted oracle).

*Climb lemma (proved).* Let `(a, a, t)` be an overlap and let `c` be a letter
of `sigma(a)`. If `beta |t| < ell_c`, then `(c, c, beta t)` is a child: the
same child on both sides, offset increment `0`. So a same-letter vertex with
`beta^n |t| < ell_min` has a diagonal descendant `(c_n, c_n, beta^n t)`, and
its contracting coordinate is `sigma_k(beta)^n sigma_k(t)`, which shrinks.
Moreover `|N(t)| = |t| prod_k |sigma_k(t)|` takes values in a discrete subset
of `Q`, bounded below on nonzero `t` by some `nu > 0`. On a vertex of the box,
`|sigma_k(t)| <= B_k`, so `|t| >= nu / prod_k B_k`. Hence a same-letter
recurrent vertex climbs to tile scale within
`log(ell_min prod_k B_k / nu) / log beta + 1` levels. For a unimodular complex
pair `log beta = 2 log(1/mu)`, so this is exactly the form of Conjecture UH.
`square`

The climb lemma explains the plastic class: its deep vertices are pure
climbs. It does **not** explain the depth in general. On the stride-7 sample,
the vertex achieving `K_V` is same-letter in only 111 of 651 specimens. The
depth remaining after the climb (`depth − climb`, maximised over recurrent
vertices) has the same distribution as `K_V`. The deepest specimens have
climb 0 or 1, for example `0 -> 210, 1 -> 0, 2 -> 110` with `K_V = 17`. Their
depth comes from cancellation between different letters. So UH has two
parts: a climb part, which is proved, and a cross-letter cancellation part,
which is the open rigidity statement of §5.6.

### 5.6b The rigidity is not a one-tile question (exact census)

Every first common vertex `y` of a recurrent vertex is born in each tiling
at some level, `k_A` and `k_B`. Two cases:

- **catch-up** (`min(k_A, k_B) < max(k_A, k_B)`): one tiling's vertex is
  reached later by the other's subdivision. That is a one-tile question: is
  a given integral offset inside a tile an eventual subdivision boundary?
- **simultaneous birth** (`k_A = k_B`): a genuine two-tile cancellation.

If every recurrent vertex had *some* catch-up hit, at any depth and not
necessarily the first, the cross-letter rigidity of §5.6 would reduce to the
one-tile question (Q1).

*Lemma (catch-up locus, proved).* Take an edge `p -> u` into an offset-zero
child whose common vertex `y` is new. If the top child index is 0, `y` is the
start of `p`'s top tile, so `t_p <= 0` and `y` is `p`'s left region endpoint
(symmetrically for a bottom index 0). Both indices 0 would make `p` itself
offset zero, so `y` would not be new. So a catch-up hit is exactly a step of
`p`'s *leftmost chain* (the child whose region contains `p`'s left end) into
offset zero. With `CU` the set of vertices whose leftmost chain reaches offset
zero, a vertex can reach a catch-up hit iff it has a descendant in `CU`.
`square`

The leftmost chain is a function on vertices, so `CU` and the reachability
are exact finite computations on the box graph (`psc.one_tile`). Right
endpoints are the mirror case. Reversing every image word reverses both
tilings, so a right-endpoint catch-up of `sigma` is a left-endpoint catch-up
of the mirror substitution, read through the vertex map
`(a, b, t) -> (a, b, l_a − l_b − t)`. Mirroring maps edges to edges, so the
two recurrent parts correspond. The counts above exclude offset-zero
vertices, though, and mirroring exchanges left-aligned with right-aligned
vertices. Tribonacci has 14 recurrent vertices on both sides, but 6 of them
are right-aligned and become offset zero in the mirror, which leaves 8 there.
So `two_sided` checks per vertex rather than comparing the two counts.

**Census (exact, standing corpus, `pixi run one-tile-census`).**

| | count |
|---|---|
| specimens | 4554 |
| recurrent vertices (nonzero offset) | 1,154,040 |
| in `CU` | 561,624 |
| reach `CU` | 1,056,816 |
| specimens where Q1 fails | 360 |
| … with no recurrent vertex reaching `CU` | 210 |
| specimens where Q1 fails at both endpoints | 360 |
| … with no recurrent vertex reaching either | 210 |
| catch-up-free (Lemma P) | 210 |
| … of which Q1 fails totally | 210 |
| total failures not catch-up-free | 0 |
| failing vertices outside the catch-up-free class | 348 |
| … short periodic (nonzero closure ≤ 2) | 348 |
| P′ to depth 5 disagrees with catch-up-freeness | 0 |
| Proposition C shape disagrees with catch-up-freeness | 0 |
| … catch-up-free with one odd letter | 18 |

Right endpoints rescue nothing. On every failing specimen the per-vertex
left, right and either counts coincide (116,316 recurrent vertices, 19,092
reaching a catch-up). The first total failure in canonical order is
`0 -> 1, 1 -> 22, 2 -> 012` (label `1 11 17`): none of its 560 recurrent
vertices reaches a catch-up at either endpoint, yet PPVC holds there for
every `r` (§4). Every new common vertex reachable from its recurrent part is
a simultaneous birth. The pinned specimen `0 -> 1, 1 -> 012, 2 -> 010` is
the same (694 recurrent, none in `CU`, none reaching a catch-up at either
endpoint; PPVC holds with `K_V = 14`).
`0 -> 1, 1 -> 12, 2 -> 022` (label `1 8 20`) fails partially: 12 of its 14 recurrent vertices
reach a catch-up, at either endpoint. Both are pinned in
`tests/test_one_tile.mojo`.

*Lemma P (arithmetic catch-up obstruction, proved).* Write `ab(u)` for the
abelianisation of a word and `Λ = M Z^3`, a sublattice of index `|det M|`.
If no proper nonempty prefix `u` of an image `sigma(a)` has `ab(u) ∈ Λ`,
then no edge of the overlap graph is a catch-up hit, at either endpoint.
In particular no vertex of nonzero offset lies in `CU`, and Q1 fails on every
recurrent vertex.

*Proof.* Every vertex has an integral offset vector `w`, with
`t = ⟨ell, w⟩`. The child through indices `(i, j)` has offset vector
`M w + ab(P_b(j)) − ab(P_a(i))`, where `P_a(i)` is the length-`i` prefix of
`sigma(a)`. So the child has offset zero iff
`M w = ab(P_a(i)) − ab(P_b(j))`. For a catch-up one index is 0 and the other,
say `j`, satisfies `0 < j < |sigma(b)|`, so `ab(P_b(j)) ∈ Λ`. That is
excluded. For right endpoints, `ab(suffix) = M e_a − ab(prefix)` is in `Λ`
iff the prefix is. `square`

When `M` is unimodular, `Λ = Z^3`, so Lemma P never applies. When
`|det M| = 2` and every proper prefix lies in the nontrivial class of
`Z^3 / Λ ≅ Z/2`, every difference of two proper prefixes lies in `Λ`. Hits are
then possible, but only as simultaneous births.

*Proposition P′ (levels are arithmetic, proved).* Call a vertex of
`sigma^n(a)` of *exact level* `k` if it is a boundary of the level-`k`
supertiles but not of the level-`k + 1` ones, and place it at the
abelianisation `v` of the prefix before it. Then `sigma` is catch-up-free iff
every such vertex has `max{k' : v ∈ M^{k'} Z^3} = k`, for every `n` and `a`.
In other words, the level of a vertex is the M-adic valuation of its position.

*Proof.* (⇒) An exact-level-`k` vertex sits at `v = M^{k+1} u + M^k ab(p)`,
with `p` a proper nonempty prefix of an image. Since `M` is injective,
`v ∈ M^{k+1} Z^3` iff `ab(p) ∈ Λ`, which catch-up-freeness excludes, and
`v ∈ M^k Z^3` always. (⇐) A proper prefix `p` with `ab(p) ∈ Λ` gives a
level-0 vertex of valuation at least 1. `square`

So in the catch-up-free class the hierarchy is read off the non-Archimedean
coordinate of the position. This also gives a second proof that every hit
there is a simultaneous birth. By Theorem B(3)(c), a hit of `(i, j, w)` at
depth `m` is a vertex with position `v` in `sigma^m(i)` and `v − M^m w` in
`sigma^m(j)`. Both levels are below `m`, while `M^m w` has valuation at least
`m`. Since the lattices `M^k Z^3` are nested, the two valuations, which are
the two levels, are equal. The census checks P′ exactly to
depth 5 on every specimen: it holds on exactly the 210 catch-up-free ones.

*Proposition C (the class in words, proved).* Call a nonempty letter set `O`
*odd*. If every image is either a single letter outside `O`, or an `O`-letter,
then letters outside `O`, then an `O`-letter, then `sigma` is catch-up-free.
When `|det M| = 2` the converse holds, and `O` is unique.

*Proof.* Let `f(v) = sum_{c in O} v_c mod 2`. Under the shape, every column
has `f = 0`, so `Λ <= ker f`. Every proper nonempty prefix has `f = 1`, so it
is not in `Λ`. Conversely, if `|det M| = 2` then `Z^3 / Λ ≅ Z/2`, so
`Λ = ker f` for a unique nonzero `f`, which defines `O`. If every proper prefix
has `f = 1`, then in an image `x_1 ... x_L` with `L >= 2`, `f(x_1) = 1`. Each
`f(x_2), ..., f(x_{L−1})` is 0, as a difference of two odd prefixes. Then
`f(x_L) = 1`, because the column is even. An image of length 1 is a column,
so its letter is even. `square`

So in a catch-up-free tiling, odd tiles occur only as the first and last
tiles of level-1 supertiles. A vertex is a level-1 boundary exactly when an
even number of odd tiles separate it from a level-1 reference vertex, which
is P′ at level 1 in combinatorial form. The census finds a unique such `O` on
exactly the 210 catch-up-free specimens, and on no other. In 192 of them
`|O| = 2` (e.g. `0 -> 1, 1 -> 22, 2 -> 012` with `O = {0, 2}`), and in 18
`|O| = 1` (e.g. `0 -> 1, 1 -> 22, 2 -> 202` with `O = {2}`).

*Route check (2026-10-04).* I read the M-adic picture against Baker, Barge and
Kwapisz, *Geometric realization and coincidence for reducible
non-unimodular Pisot tiling spaces*, Ann. Inst. Fourier 56 (2006), §§1, 4
and 6. They realise the tiling flow of any Pisot substitution on the
inverse limit `T_A` of the torus under `A`. For `|det A| > 1` that limit
carries exactly the non-Archimedean coordinate in which P′ reads levels.
Their Geometric Coincidence Condition (Def. 4.1: `cr_phi = 1`, where
strands are coincident iff some `Phi^k` images share a labelled edge) is
decidable per substitution and equivalent to pure discrete spectrum
(Thms 4.2 and 5.1). Thm 6.1 is a criterion for it. It is proved
unconditionally only for a class of `beta`-substitutions (Thm 7.1). So the
paper gives the setting for case 3 below, but no unconditional argument. Its
coincidence is labelled-edge coincidence, which implies vertex coincidence,
and reaching it would be stronger than PPVC. Like the (W) check in §5.7,
this is a dictionary entry, not a route that bypasses pure discrete
spectrum. Lemma P and P′ themselves were not found there in this form.

On the standing corpus Lemma P is exact (`catch_up_free`, checked in the
census). It applies to precisely the 210 total failures, all of them with
`|det M| = 2`. Every total failure is catch-up-free, and the census checks
that no catch-up-free specimen has a vertex in `CU`. The converse, that a
total failure must be catch-up-free, is observed, not proved. The 150
partial failures, 102 of them unimodular, are not arithmetic: in each, some
prefix lies in `Λ`. They are instead degenerate. The census finds 348
failing recurrent vertices outside the catch-up-free class, and every one is
a *short periodic vertex*: its forward closure, offset-zero vertices
excluded, is the vertex itself (a fixed point of the inflation) or a 2-cycle.
Its other children all have offset zero, and since PPVC holds, it hits within
two levels. For example, in `0 -> 1, 1 -> 12, 2 -> 022` the two failing
vertices `(1, 2, (0, 2, −1))` and `(2, 1, (0, −2, 1))` each have one nonzero
child, themselves, and one simultaneous-birth child `(2, 2, 0)`. Lemma P also
explains the left–right coincidence for total failures. For partial failures
that coincidence remains unexplained.

So the one-tile reduction is false in general, at either endpoint. On the
corpus every recurrent vertex falls into one of three cases, decided exactly:

1. it reaches a catch-up hit (Q1), so a one-tile argument applies;
2. it is short periodic and hits within two levels;
3. its specimen is catch-up-free (Lemma P), so all of its hits are
   simultaneous births.

Cases 1 and 2 cover every specimen outside the arithmetic class. The
trichotomy is a census fact, not a theorem: nothing yet shows that a
non-short vertex of a non-catch-up-free substitution must reach `CU`. A
proof of PPVC along these lines needs that statement and the case-3
question below. Case 3 is the sharp form of §5.6's interleaving question:
two-tile cancellation, where both tilings acquire the common vertex at the
same level. For the catch-up-free class, the
interleaving question is exactly whether a simultaneous birth
`M w = ab(P_a(i)) − ab(P_b(j))`, with `i, j > 0`, is reachable from every
recurrent vertex.

### 5.7 The closing target, restated

The box graph is the carry automaton of the Dumont–Thomas numeration of
`sigma`: offsets are carries, children are digit pairs, and offset zero is a
resolved carry. PPVC(`sigma`) says every recurrent carry can be resolved.
This is the substitution analogue of Akiyama's weak finiteness property (W)
for `beta`-numeration, which Barge proved for every Pisot `beta` by
`beta`-specific monotonicity (`p1b-barge-diamond-configuration-gate-2026-10-02.md`).
The data above says a general proof cannot be one-step, cannot be
endpoint-based, and cannot use a size bound plus a constant number of levels.
It should instead show that carries resolve within a bounded number of
e-foldings of contraction (Conjecture UH). The determinant enters only
through the contraction rate. No such argument is given here.

*Route check (2026-10-03).* Barge's proof of (W) was read in Barge 2018,
§§1, 4 and the end of §5 (arXiv:1505.04408). Property (W) is Corollary 17
there, deduced from Theorem 15 (pure discrete spectrum for every
`beta`-substitution) through Akiyama's equivalence between (W) and pure
discrete spectrum and Barge's Proposition 31. So it is a consequence of pure
discrete spectrum, not an independent numeration argument. Theorem 15 rests
on the monotonicity Properties 1–3 of the `beta`-language, which the
Barge–Diamond gate already stopped. The (W) analogy therefore offers no route
to PPVC that bypasses pure discrete spectrum. It remains a useful dictionary,
not a proof strategy.

## 6. What this does not establish

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
