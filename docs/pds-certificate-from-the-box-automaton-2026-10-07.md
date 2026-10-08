# A per-specimen PDS certificate from one finite automaton — 2026-10-07

**Status:** research note. Lemma Ω1 and Theorem Ω are proved here from
elementary facts. Consequence (a) imports Lee–Moody–Solomyak 2003,
Lee–Solomyak 2012, Akiyama–Lee 2011 and Clark–Sadun 2003 (§7 records the
literature stop/go). Consequence (b)
uses manuscript Theorem 5.38. Consequence (c) uses Proposition 1 of
`bpa-termination-by-overlap-depth-2026-10-02.md`, which is re-derived in §6.
§6 also re-derives, independently, the October 4 necessity chain (Lemma C,
Theorem B, Proposition F, Theorem R, Theorem S). That re-derivation found no
error. It is one more internal review and does not replace the pending human
review. The finite-domain consequence of §5 is recorded in the claim ledger
as the finite-domain theorem `BoundedPureDiscreteSpectrum` (2026-10-08); no
proof-dependency (TLA+) node changes, and PSC stays open.

## 1. The point

The finite-domain statement of `strong-coincidence-census-2026-10-04.md` §4,
pure discrete spectrum on 145,806 specimens, was recorded as resting on
Proposition V and Theorem B. Both are unreviewed. One alternative would make
each specimen rest only on ABBLS Theorem 5.3, by certifying that the
balanced-pair algorithm terminates with coincidence. That route fails on the
120 cube-family specimens (`lost-depth-indexed-formulation-2026-10-01.md`
§7): their states grow towards about `10^10` letters, so a direct build is
out of reach.

This note shows that **neither is needed.** The object that decides every
specimen is the box automaton `𝔅` of Proposition V. Its vertices are
overlaps, not words, and it has at most 1.43 million of them on the surveyed
domains. The certificate runs one exact predicate on it: every vertex
reaches a coincidence. Two facts link that predicate to pure discrete
spectrum:

- **Elementary.** Step 1 of Proposition V says cycle vertices lie in the box.
  This is a geometric-series bound and does not use Theorem B.
- **Published.** The overlap-coincidence criterion of Lee–Moody–Solomyak.

The 120 are treated like every other specimen. For the cube specimen the
automaton has 85,287 vertices. The same certificate also gives termination
with coincidence from every swap seed, which is the statement the ABBLS route
wanted (consequence (c)), without building `B_sigma`.

## 2. Setting

`sigma` is primitive irreducible Pisot on `{0,1,2}`. It has incidence `M`,
Perron root `beta`, and tile lengths `ell` (`ell M = beta ell`) with
`Q`-independent coordinates.
Choose their common positive scale so that `ell ∈ Q(beta)^3`, as in the
kernel. The three lengths are then a rational basis of the cubic field.

- **Potential overlap.** A triple `x = (i, j, t)` with `t = <ell, w>`,
  `w ∈ Z^3`, and `−ell_j < t < ell_i`, so that the open tiles `(0, ell_i)`
  and `(t, t + ell_j)` meet.
- **Children of `x`.** The overlapping pairs of sub-tiles of `sigma(i)` and
  of `sigma(j)` shifted by `beta t`. Each child has offset `beta t + c`, with
  `c ∈ F = {<ell, pi(q) − pi(p)>}` (`p`, `q` proper prefixes of images).
- **Coincidence.** `(k, k, 0)`.
- **Productive.** Some descendant (depth 0 included) is a coincidence.
- **FP(`sigma`).** Every potential overlap is productive.

`𝔅` is the inflation closure of a finite start set. That set contains every
potential overlap with `|w_m| <= R_m`, where `R_m` are the radii of
Proposition V (`psc.vertex_coincidence.box_radii`, all bounds exact).

## 3. Lemma Ω1 (finite descent, and cycles in the box)

*Let `x` be a potential overlap.*

1. *`x` has finitely many descendants.*
2. *Every potential overlap that lies on a cycle of the overlap graph is a
   vertex of `𝔅`.*

*Proof.* Let `sigma_k` range over the contracting embeddings of `Q(beta)`.
Put `mu_k = |sigma_k(beta)| < 1`, `C_k = max_{c ∈ F} |sigma_k(c)|` and
`B_k = C_k / (1 − mu_k)`. The length lattice is stable under multiplication
by `beta`, since `beta <ell,w> = <ell,Mw>`. Along a path
`t_{n+1} = beta t_n + c_n` we have
`|sigma_k(t_{n+1})| <= mu_k |sigma_k(t_n)| + C_k`. Hence
`|sigma_k(t_n)| <= max(|sigma_k(t_0)|, B_k)` for every `n`, and
`|t_n| < ell_max` because the tiles meet.

1. Use the Minkowski embedding of `Q(beta)`: all three real embeddings,
   or the Perron embedding together with the real and imaginary parts of
   one complex embedding. Since the lengths are a rational basis, the
   embedding matrix is invertible over `R`. Its image of `Z^3` is therefore
   a full-rank lattice in `R^3`. Only finitely many `w` lie in the compact
   region bounded above. Injectivity alone would not imply discreteness.
2. On a cycle of period `p`, iterating the recursion gives
   `sigma_k(t_0) (1 − sigma_k(beta)^p) = sum_{n<p} sigma_k(beta)^n sigma_k(c_{p−1−n})`.
   Hence `|sigma_k(t_0)| <= B_k`. With `|t_0| < ell_max` and
   `w_m = Tr(theta_m t_0)` (trace-dual basis), this gives `|w_m| <= R_m`.
   So `t_0` lies in the start set, and therefore in `𝔅`. `square`

Part 2 is step 1 of Proposition V. Part 1 is item 5 of
`formal-overlap-carriers-2026-10-04.md` §2, restated for the box radii.
Neither uses Theorem B, Lemma C or any periodic-tiling construction. The
adversarial audit `audit-adversarial-prop-v-theorem-e-2026-10-07.md` checked
step 1 independently and found it sound. Its recomputed radii also leave every
enumerated integral centre offset at no more than 0.48 of its radius.

## 4. Theorem Ω (formal productivity is one automaton property)

*For PIP `sigma` the following are equivalent:*

- *(i) FP(`sigma`);*
- *(ii) every vertex of `𝔅` is productive.*

*Proof.* (i) ⇒ (ii): vertices of `𝔅` are potential overlaps.

(ii) ⇒ (i): let `x` be a nonproductive potential overlap.

- A non-coincidence overlap has at least one child, because inflated tiles
  that meet still meet.
- A child of a nonproductive overlap is nonproductive.

So `x` starts an infinite nonproductive path. By Lemma Ω1(1) the path stays
in a finite set, so it repeats a vertex. The repeated vertex `v` lies on a
nonproductive cycle, so `v ∈ 𝔅` by Lemma Ω1(2). That contradicts (ii).
`square`

The six aligned pairs `(i, j, 0)` have `w = 0`, so they lie in `𝔅`. Hence (ii)
contains SC_all, and `S(sigma)` can be read off `𝔅`
(`test_the_box_holds_every_aligned_pair`).

**Consequences.** Suppose (ii) holds for `sigma`.

- **(a) PDS by the literature only.** The overlaps of Lee–Moody–Solomyak are
  triples `(T, y, S)`. Here `T` and `S` are tiles of the self-similar tiling,
  `y ∈ Ξ` (translations between tiles of one type), and the supports of
  `y + T` and `S` meet in an interior point. Write their left endpoints as
  `u_i+y` and `u_j`. Anchoring the first at zero gives our signed offset
  `t = u_j-u_i-y`. Endpoint differences and same-type return translations
  are integer sums of tile lengths, so `t ∈ Z⟨ell⟩`. The classes are
  determined by these types and offset (LMS Lemma 6.8, proof); the published
  offset `u_i+y-u_j` is `-t`. Child offsets are exactly
  `beta t + prefix_bottom-prefix_top`, and coincidence is equal types with
  zero offset. Thus every realized overlap and its descendants are included
  in our formal overlap graph. No equality of the two whole graphs is needed.

  LMS requires a repetitive fixed tiling. Choose a power `sigma^p` admitting
  one: choose `sigma^p(a) = u a v` with both `u` and `v` nonempty, possible
  by primitivity and growth. With `Q = beta^p`, place the tile `a` at left
  endpoint `-x`, where `x = length(u)/(Q-1)` lies strictly inside that tile.
  Its substituted copy of `a` has the same endpoint, so inflation gives
  nested legal patches exhausting both directions. Primitivity supplies
  repetitivity, and finite tile types give FLC. This power step is needed
  for some named specimens; the first-letter map of the cube specimen is a
  three-cycle.
  Every coincidence persists under further substitution, so pad its witness
  depth to a multiple of `p`. The realized `sigma^p` overlap graph consequently
  satisfies LMS Lemma 6.9(iii). Its edges are length-`p` paths of geometric
  children, and its expansion is `beta^p`, still Pisot.
  - `Ξ` is Meyer because `beta^p` is Pisot (Akiyama–Lee 2011, Thm 2.7;
    Lee–Solomyak 2012, Thm 4.3 and Cor. 2.13 give the control-point form).
    In `d = 1` the scalar expansion is diagonalizable and its sole eigenvalue
    has multiplicity one, so the algebraic-conjugacy/multiplicity hypotheses hold.
  - LMS Lemma 6.9 with Theorem 4.7 (equivalently Akiyama–Lee 2011,
    Thm 2.5) then gives pure discrete spectrum of the tiling flow.

  Neither unimodularity nor irreducibility is needed for this tiling-flow
  conclusion beyond Pisot inflation.
  For the symbolic conclusion, use Clark–Sadun 2003, Thm 3.1 and Cor. 3.2:
  for a primitive aperiodic substitution with only one incidence eigenvalue
  of modulus at least one, its Perron-length flow is conjugate to a
  constant-roof suspension after rescaling. PIP has precisely that spectrum
  and is aperiodic: periodic letter frequencies would be rational and force
  a rational Perron root.
  The time-`c` map of a roof-`c` suspension is the subshift map times the
  identity on the roof coordinate. Functions depending only on the subshift
  coordinate form an invariant subspace of this pure-point unitary operator,
  so the subshift also has PDS. This bridge does use
  the full PIP spectral hypothesis, and assumes no unimodularity.
- **(b) PDS by the manuscript route.** Every overlap reachable from a swap
  seed is a potential overlap, so FP gives `OP_seed`. Theorem 5.38 (Lemma
  5.36 and the imported Barge–Štimac–Williams theorem) gives PDS. Routes (a)
  and (b) use different flow-level sufficiency theorems after FP.
- **(c) Termination with coincidence from every swap seed.** FP gives
  productivity of the whole seed-patch graph from every seed. Proposition 1
  of the depth note then bounds every state of `B_sigma` reached at level
  `n >= D` by `2 beta^D ell_max`, where `D` is the seed graph's largest
  first-coincidence depth. So `B_sigma` is finite. Every state is a gap
  between consecutive balanced cuts of `(sigma^n(ab), sigma^n(ba))`, and the
  overlaps inside it are productive. So its inflations contain a coincident
  tile, and every state reaches a coincidence. This is the per-specimen
  termination certificate that a direct ABBLS build could not deliver on the
  120 specimens. Applying ABBLS Theorem 5.3 itself would still need its seed
  hypotheses, which are not checked here. Routes (a) and (b) do not need it.

**Direction of the certificate.** Only (ii) ⇒ PDS is used. The converse,
PDS ⇒ (ii), is Corollary FP″ and still goes through Theorem S. So a specimen
failing (ii) would refute PSC only through that chain, which §6 re-derives.
A failure has never been observed.

## 5. The finite domains

**The recorded runs already give (ii).** By Proposition FP item 2
(`formal-productivity-reduction-2026-10-04.md`, elementary), (ii) is
equivalent to SC_all together with BH. BH asks that every cycle vertex has an
offset-zero descendant, and it follows from two inputs:

- the recorded vertex-coincidence verdict, that every vertex of `𝔅` has an
  offset-zero descendant;
- Lemma Ω1(2), that cycle vertices lie in `𝔅`.

The verdict is read here as a statement about the automaton, not about
periodic tilings, so Proposition V(2) is not used. With the SC_all census,
the recorded runs on

- the standing corpus,
- total length ≤ 8, and
- images ≤ 4

give (ii), hence PDS by (a) and by (b). **The 145,806-specimen statement
therefore rests on:**

- Lemma Ω1, Theorem Ω and Proposition FP (elementary);
- the exact runs;
- either LMS 2003 with LS 2012, or Theorem 5.38.

It does not use Theorem B, Lemma C, Proposition F, Theorem R, Theorem S or
Proposition V(2).

**One pass instead of two.** The census
(`kernel/vertex_coincidence_census.mojo`) now also decides (ii) directly on
the same automaton, by coincidence reachability
(`psc.vertex_coincidence`: `productive`, `coincidence_depth`,
`aligned_depth`). It prints `formally productive (Theorem Omega): N  not: 0`.

| specimen | box vertices | recurrent | `K_V` | box `D` | `S` | box cycle vertices missing from the seed graph |
| --- | --- | --- | --- | --- | --- | --- |
| Tribonacci `0→01, 1→02, 2→0` | 743 | 14 | 3 | 8 | 1 | 0 |
| cube `0→1, 1→222, 2→0222` | 85,287 | 1,166 | 17 | 51 | 7 | 38 |
| golden pump `0→1, 1→021, 2→001` | 61,337 | 716 | 15 | 39 | 6 | 100 |
| plastic `0→1, 1→2, 2→10` | 7,129 | 74 | 14 | 33 | 15 | 16 |

The last column is the counter-calibration
(`test_the_seed_graph_is_not_a_formal_certificate`). The swap-seed graph
misses unrealized carriers, so seed productivity is not a substitute for `𝔅`
in route (a). It suffices only for route (b).

**Fresh one-pass runs (2026-10-07, 4 workers).**

| domain | specimens | formally productive | capped | deepest box `D` | wall-clock |
| --- | --- | --- | --- | --- | --- |
| standing corpus | 4,554 | 4,554 | 0 | 51 (`1 11 17`) | 6.9 min |
| total length ≤ 8 (contains the 120) | 24,486 | 24,486 | 0 | 104 (`1 38 56`) | 50.6 min |

Both runs reproduce every figure that §4 of the vertex note records for these
rows: the largest box graph, the most recurrent vertices, the recurrent total
and the deepest `K_V`, with the same specimens. The standing row also
reproduces the `K_V` histograms that CI pins. The images ≤ 4
row was not re-run in this session. It rests on the recorded PPVC run together
with the SC_all census, as described above, until the guarding workflow runs.

The census slices pinned in `kernel/tests/test_vertex_coincidence.mojo`
(first 300 standing, first 100 images ≤ 4) are all productive, with box `D`
51 and 38.

**The 120 cube-family specimens** have image lengths `(1, 3, 4)`, so total
length 8. They lie in both the total-length ≤ 8 and the images ≤ 4 domains,
and the recorded runs settle them as above. The cube specimen's automaton is
listed in the table. With its seed graph's `D = 19`, consequence (c) bounds
every state by about `4.5 · 10^10` letters (`K' = 17` gives about
`4.2 · 10^9`), which agrees with the growth that exhausted the direct
build's budget.

## 6. Independent re-derivation of the October 4 chain

Each step was re-derived from its statement and not from the notes' proofs.
"Holds" means the step was checked line by line.

- **Lemma C** (`p1b-strict-zipper-periodic-pair-2026-10-02.md` §3): holds.
  - Step 1: if one edge misses the left end, strict monotonicity of the
    composite keeps `E(L_0) > L_0`.
  - Step 3: a terminal SCC of a child-closed set with no sinks contains a
    cycle, and the children of a branching vertex stay inside it.
- **Theorem B**: holds.
  - In the converse, "interior centre ⇒ `P`, `U` nonempty" needs one more
    sentence. The composite region map is the restriction of the tile map
    `x ↦ (x + <ell, pi(P)>)/beta^r`. So its fixed point is
    `c_A = <ell, pi(P)>/(beta^r − 1)`. If `P` is empty then `c_A = 0`, and
    `0 ∈ cl R_{v_0}` forces `0` to be the left end of `R_{v_0}`. This
    contradicts interiority. The other three cases are symmetric.
  - (a) ⇔ (b) uses only that subdivision keeps vertices and that
    `phi^n(R_{v_0})` exhausts `R`.
- **Proposition F**: holds.
  - Step 2 uses Pisot's theorem in its algebraic form: `beta` algebraic and
    `||theta beta^n|| → 0` give `theta ∈ Q(beta)`. The conclusion
    `m_n ≡ 0 (mod D)` follows because `k/D` is at least `1/D` from `Z` for
    `k ≢ 0`.
  - Step 5 needs only that `X_max` is dual to the continuous eigenvalues and
    that each continuous eigenvalue satisfies Solomyak's criterion. The
    stronger "every eigenfunction is continuous" (BK Thm 5.1) is not needed.
- **Theorem R**: holds.
  - In step 1, `G(n) = H(x_n)` is well defined because `x_[n,m) x_m` is a
    return word.
  - Steps 2–3 use only unique ergodicity and `Q`-independence of the
    frequency vector.
- **Proposition 1 / Proposition 4 of the depth note**: hold. Pieces between
  consecutive balanced cuts are irreducible. The overlaps of
  `(sigma^n(ab), sigma^n(ba))` inside the first period are depth-`n`
  descendants of seed overlaps. A common vertex is a balanced cut by Lemma
  5.30.
- **Theorem S**: holds given its imports. The residual risk is the one
  `coincidence-rank-imports-literature-gate-2026-10-04.md` §4 already
  records: Barge 2015 item (3) is a summary statement whose proofs (BKw,
  BBK, BK) were not read. That is now the only unread link in the necessity
  direction. After this note, nothing in the sufficiency direction depends
  on it.

## 7. Literature stop/go for the overlap-coincidence import

- **Claim.** FP(`sigma`) ⇒ overlap coincidence ⇒ PDS, for PIP `sigma`,
  unimodular or not.
- **Read (arXiv texts).**
  - Lee–Moody–Solomyak, *Consequences of pure point diffraction spectra for
    multiset substitution systems*, DCG 29 (2003), arXiv:0910.4450: Thm 4.7;
    Def. 6.7 (overlap `(T, y, S)`, `y ∈ Ξ`, interior intersection;
    coincidence `y + T = S`); Lemma 6.8 (finitely many classes; the class
    is determined by `i`, `j` and `u_i + y − u_j`); Lemma 6.9 ((i) density
    one ⇔ (iii) from each vertex of `G_O(T)` a path to a coincidence).
  - Lee–Solomyak, *Pisot family self-affine tilings, discrete spectrum, and
    the Meyer property*, DCDS-A 32 (2012), arXiv:1002.0039: Def. 2.7,
    Thm 4.3 ((i) Pisot family ⇔ (iv) control points Meyer), Cor. 2.13.
  - Akiyama–Lee, *Algorithm for determining pure pointedness of self-affine
    tilings*, Adv. Math. 226 (2011), arXiv:1003.2898: Def. 2.4, Thm 2.5,
    Thm 2.7.
  - Clark–Sadun, *When size matters: subshifts and their related tiling
    spaces*, ETDS 23 (2003), arXiv:math/0201152: Thm 3.1 and Cor. 3.2
    (length-change conjugacy under the PIP incidence spectrum).
  - Solomyak 1997, Thm 6.2, is the `d <= 2` original. Its full text was not
    obtained, and LMS is the cited source.
- **Transfers.** The hypotheses (primitive tile substitution, repetitive
  fixed point, FLC, `Ξ` Meyer, expanding `Q = beta^p`) hold for a legal
  repetitive fixed tiling of a suitable substitution power, as described in
  (a). Its tiling space is the same as that of `sigma`. No unimodularity
  appears.
- **Boundaries.**
  - The theorems quantify over overlaps that occur. FP quantifies over a
    superset, which is fine for sufficiency only.
  - "Reaches a coincidence" means that some path does.
  - Uniformity of the depth on the realized overlap classes follows from
    their finiteness under the Meyer hypothesis (LMS Lemmas 6.8–6.9).
    Lemma Ω1 proves finiteness separately for each formal starting overlap;
    it does not assert a uniform depth over all formal starting offsets.
  - The literature criterion concludes PDS for the `R`-action. The passage
    to the `Z`-subshift uses Clark–Sadun Cor. 3.2 and the constant-roof
    suspension argument in (a), with the full PIP incidence spectrum.
- **Negative control.** Akiyama–Lee 2014 Example 4.7 (reducible) has
  overlap coincidence but fails strong coincidence. Irreducibility is not
  needed for the overlap-to-flow implication, but the symbolic bridge in (a)
  uses the full PIP spectrum, and SC_all is not a consequence of PDS without
  irreducibility. This note uses SC_all only as part of (ii), which it checks.
- **Decision: proceed.** Record (a) as a literature-backed sufficiency
  route. Restrict novelty to Lemma Ω1 + Theorem Ω, the one-automaton
  certificate.

## 8. Evidence boundary and guarding

The standing-corpus row is CI-pinned: the `vertex-coincidence-census` job now
also requires `formally productive (Theorem Omega): 4554  not: 0` and a
deepest box first-coincidence depth of 51 (specimen `1 11 17`). This session's
run reproduced every earlier line of that job unchanged, in 6.9 minutes on
4 workers. The total-length ≤ 8 and images ≤ 4 rows
are guarded by `.github/workflows/box-automaton-evidence.yml`. It runs one
job for total length ≤ 8 and a matrix of twelve images ≤ 4 slices, each
under the six-hour job limit, on `workflow_dispatch`, on a weekly schedule,
and on pull requests that touch the kernel or this note. Each job requires
`capped: 0  fails: 0` and `formally productive (Theorem Omega): <slice size>
not: 0`. Until that workflow has run green, the two larger rows remain
recorded runs, as before.

**2026-10-08 completion:** all thirteen larger-domain jobs and all twenty
main research jobs are green at PR #233 final head `72f173d`. The twelve
images ≤ 4 slices directly certify 135,990 productive specimens, and the
total-length ≤ 8 job certifies 24,486, with no caps or failures. Exact
intersection counting gives the 145,806-member union. The dated snapshots,
verbatim output excerpts and remaining independent-review gate are in
[`audit-theorem-omega-2026-10-08.md`](audit-theorem-omega-2026-10-08.md).

## 9. What this does not do

The audit of PR #233's final head, including the power/fixed-point bridge,
signed dictionary, exact replay and current-head CI observations, is in
[`audit-theorem-omega-2026-10-08.md`](audit-theorem-omega-2026-10-08.md).
Independent review and completed evidence runs remain acceptance conditions.

- It proves neither FP nor PDS for all PIP substitutions. Theorem Ω is a
  per-specimen certificate, and #84, #138 and #139 are untouched.
- It does not review the Barge coincidence-rank imports. Those matter only
  for the converse direction.
- It promotes only the finite-domain statement of §5, as the claim-ledger
  entry `BoundedPureDiscreteSpectrum` (status finite-domain, guarded by
  `kernel/tests/test_vertex_coincidence.mojo`, the CI census job and
  `box-automaton-evidence.yml`). It adds no proof-dependency node: the claim
  is about a finite domain, not a universal implication.
