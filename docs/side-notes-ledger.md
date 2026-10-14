Warning: truncated output (original token count: 28282)
Total output lines: 1611

# Side-notes ledger

**Status:** live, append-only working ledger. It records side findings so that
no session re-spends cycles on them: refuted mechanisms, redirected routes,
specimens already settled by the literature, withdrawn figures, finite
observations, and tooling pitfalls. It changes no claim status; each entry
points to the note or receipt that carries the evidence. Policy:
`AGENTS.md`, "Record side findings".

Entry format: date · finding · evidence locator. Add entries at the end of the
right section; correct an entry by adding a dated correction under it, never
by deleting it.

## 1. Refuted or retired mechanisms (do not re-attempt)

- 2026-10-02 · One-step descent of the contracting size `q(t)` (or of
  `max_k |sigma_k(t)|/B_k`) as a local reason for boundary hitting: fails on
  234 of 1,166 recurrent vertices of the cube specimen. ·
  `p1b-vertex-coincidence-box-2026-10-02.md` §5.2
- 2026-10-02 · Endpoint hitting (first common vertex on the leftmost or
  rightmost chain): fails on the golden pump (8 of 716). · same, §5.2
- 2026-10-02 · First-hit depth ≤ contracting lower bound `m_0` + small
  constant: excess reaches 14. · same, §§5.2, 5.4
- 2026-10-03 · Ratio laws `K_V <= c / log(1/mu)` with `c = 3.2` or `4`:
  violated on images ≤ 4 (1,506 and 72 specimens). The existential form
  (Conjecture UH) stays open. · same, §5.5a
- 2026-10-03 · One-tile reduction (every recurrent vertex reaches a catch-up
  hit): false; 360 corpus specimens fail, 210 totally. · same, §5.6b
- 2026-10-04 · One-step M-adic valuation ascent as a local mechanism for T2:
  holds on none of the 210 (corpus) or 654 (total length ≤ 8) catch-up-free
  specimens; ascent depth reaches 25. · same, §5.6d;
  `kernel/valuation_ascent_census.mojo`
- 2026-10-04 · Universal noncoincident-cycle exclusion: retired earlier
  (flipped Tribonacci); formal carriers confirm that coincidence-free cycles
  are ubiquitous (13,260 on the corpus), realized or not. ·
  `formal-overlap-carriers-2026-10-04.md`
- 2026-06-13 (archive) · H3 letter-graph / affine-fixed-point trapped
  detector: transpose bug (offset matrix is `M`, not `M^T`) and wrong object.
  · `archive/2026-09-08/notes_2026_06/H3_LETTERGRAPH_BUG_2026_06_13.md`
- 2026-06-13 (archive) · Collar certification lemma `R(C) <= L_sigma`:
  refuted. · `archive/2026-09-08/notes_2026_06/COLLAR_LEMMA_REFUTED_2026_06_13.md`

- 2026-10-06 · Hub-guarded nonincrease of the physical cut potential `|i-j|`
  on target-free PIP occurrence transitions is false: replayed cycle
  `396,820` has hub word `1,1` and offset `0,1,0`; its first edge selects an
  actual interior child. The support is productive, so this is a local
  monovariant negative, not a strict component counterexample. ·
  `c4-ordered-hub-offset-negative-2026-10-06.md` §3;
  `evidence/ordered-hub-packets-2026-10-06/`

- 2026-10-12 · **Withdrawn box-walk radius-eight extremum.** The reported
  constrained exhaustive `n=3, L=3` maximum of 8 lacks a preserved
  family predicate, saturation proof, original program, run budget, and
  output; a plateau is not transition closure. Exact deterministic
  **single-specimen, aligned-prefix** replay on
  `sigma=(001,22,220)`, swap `01|10`, depths `0..9`, budget
  `30000` symbols per side, has radii `8` at depths 6–8 but `10`
  at depth 9, first attained at cut `9054` with defect `(5,5,-10)`.
  This refutes 8 for that observable only, not an undefined historical
  comp-set quotient. No `R*(3,3)` extremum or universal radius law is
  certified; further depth beyond the budget is not a saturation verdict. ·
  `docs/audit-2026-10-11-boxwalk-extremal.md` §4;
  `evidence/boxwalk-radius8-depth9.json`;
  `kernel/boxwalk_radius_probe.mojo`

- 2026-10-12 · **Progress-indexed radius hypothesis preserved.** The
  withdrawn radius-eight *global maximum* may instead have been a running
  maximum limited by inflation depth or enumeration progress; the original
  cursor, family, and stopping rule are unavailable, so this is an **open
  interpretation**, not a recovered exhaustive result. For the specified
  aligned-cut witness, the fully measured cumulative envelope
  `R_<=D=max_{d<=D} r_d` is `8` at `D=8` and `10` at `D=9`;
  it is nondecreasing **by definition** and is only a lower bound on the
  eventual radius. In a family scan the running maximum over completed
  specimens is likewise a lower bound until all specified jobs finish;
  neither progress plateau proves saturation. Progress-dependent
  `R_<=D <= f(n,L,D)` bounds or certified state-progress stopping
  criteria remain viable **research targets**, not established laws. ·
  `docs/audit-2026-10-11-boxwalk-extremal.md` §4,
  "Progress-dependent bounds remain a live possibility";
  `evidence/boxwalk-radius8-depth9.json`

- 2026-10-12 · **Do not revive the box-walk one-step shortcuts.**
  Spectral contraction to zero ignores affine prefix forcing; common-boundary
  gap `<= L`, child-box subset inclusion, a specimen-independent absolute
  radius, and one-step length/first-letter monovariants were rejected by the
  October 11 thread. The thread's raw counterexample runs are not preserved,
  so treat them as **unverified research negatives**, not individually
  certified disproofs. The sampled formulas `2(L-2)` and
  `(n-1)(L-1)`, and a depth-`<=5` saturation shortcut, remain unproved;
  the explicit depth-nine aligned-cut witness separately refutes any such
  proposed bound below 10 **when applied to that observable**. ·
  `docs/audit-2026-10-11-boxwalk-extremal.md` §§"Claims retracted or
  not to re-attempt", "Extremal-search reframing"

## 2. Redirected routes (no lever there; see the decision)

- 2026-10-05 · The `CU` / one-tile route cannot reach #139, and Proposition LC
  says why in terms of objects rather than counts: a `CU`-failure *is* a
  prefix-vs-interior periodic pair, whose centre is a vertex of one tiling of
  infinite level and interior to every level tile of the other — hence
  **never** a common vertex, by construction. So these pairs are a forced,
  abundant family (10,584 on the corpus, on 2,760 specimens) that costs
  nothing: G1 holds on the whole standing corpus anyway. The genuine
  obstruction to #139 is the **interior-vs-interior** pair of Theorem B, where
  the centre is a vertex of neither tiling and a shared vertex elsewhere is
  open — `psc.periodic_pair` and PPVC. Spend #139 effort there. The leftmost
  chain's remaining use is Corollary LC5. ·
  `p1b-leftmost-chain-periodic-pair-2026-10-05.md` §8b

- 2026-10-03 · Barge's (W) / beta-numeration monotonicity as a route to PPVC:
  it is a consequence of pure discrete spectrum, not independent of it. ·
  `p1b-vertex-coincidence-box-2026-10-02.md` §5.7 route check
- 2026-10-04 · Adelic coverage for T2 on the catch-up-free class: needs the
  multiplicity-one window property, which pure discrete spectrum gives; the
  class's arithmetic does not lower the bar. · same, §5.6e
- 2026-10-04 · Vertex-sheet alignment as a PDS-free lever: under SC_all a
  common vertex of two `Phi^r`-fixed tilings forces a common tile (Lemma VT),
  so it is tile coincidence. · same, §5.6f
- 2026-10-04 · Recoding a catch-up-free `|det M| = 2` substitution to a
  unimodular one on three letters: impossible, `|det M| = |N(beta)|` is an
  invariant of the Perron number. · same, §5.6e
- 2026-10-04 · Barge-class conjugacy for catch-up-free substitutions with one
  E letter and a length-1 image: powers provably never work (Lemma B); no
  rotation witness found (0 of 264 at total length ≤ 8). · same, §5.6g

- 2026-10-07 · A symbolic (Sellami-style) balanced-pair run over Theorem E's
  parameters, as a route to termination on the catch-up-free `|det M| = 2`
  class: the states are not parametric words. Maximal state length grows
  exponentially along lines (class A `(n, n − 1, n)`: 480, 2,124, 27,768
  letters at `n = 4, 5, 6`; class D `(1, 0, 0)`: 7,987). Work on the overlap
  graph, whose vertices are bounded. · `p1b-catch-up-free-ppvc-2026-10-07.md`
  §3; scratch `explore.py`

- 2026-10-07 · A one-step contracting trapping region as the finite
  candidate set for PPVC on a line of class B: finite but not constant (413 to
  593 lattice points for `q = 2..25` on `p = 2q + 2`, `r = q + 1`), while the
  true recurrent set is a constant 120 vertices. Use the swap-seed closure
  instead: pure discrete spectrum needs one seed, G1 needs the three, and
  neither needs a box. · `p1b-symbolic-line-2026-10-07.md` §2;
  `archive/2026-10-07/symbolic-line-probes/trap_float_probe.out`

- 2026-10-11 · Durand return-word derivation as a route into Barge's class
  for Theorem K's family: of the 130 primitive Pisot members with
  `|det M| = 2` and `|w_1|, |w_2| <= 4`, no derived substitution at any
  letter, nor its square, is in Barge's class or its mirror. Extends the
  2026-10-07 no-witness entry beyond powers and rotations. Archived probe with
  a float Pisot screen, not a registered claim; the splitting move
  `tau rho -> rho tau` is untested. ·
  `sadic-transfer-literature-gate-2026-10-11.md` §4;
  `archive/2026-10-11/return-word-barge-probe/`

- 2026-10-11 · Porting the S-adic Lemma S (swap walk bounded by the balance
  constant) to shrink PSC certificates: nothing consumes `D_sigma`. The box
  radii come from contraction on formal overlaps, and the seed graph is an
  exact closure. Zero gain by construction. Do not re-attempt. ·
  `sadic-transfer-literature-gate-2026-10-11.md` §6

## 3. Settled by the literature (do not target with new machinery)

- 2026-10-04 · Specimens with a power or common-prefix/suffix conjugate in
  Barge's 2016 class or its mirror have pure discrete spectrum, hence PPVC
  and G1: 1,248 of the 4,554 corpus specimens, 6,336 of the 24,486 of total
  length ≤ 8; in the catch-up-free class 78 of 210 and 174 of 654. List them
  with `pixi run barge-class-census [total]`. Rests on the imported Barge
  (2016) and, for PPVC, on Theorem S (unreviewed). ·
  `p1b-vertex-coincidence-box-2026-10-02.md` §5.6g

- 2026-10-04 · PDS ⇒ all-pairs prefix strong coincidence for irreducible
  Pisot substitutions: Akiyama–Lee 2014, Corollary 4.5; in the non-unit case
  the height-group step is Theorem R (repository, unreviewed), since Sing's
  2006 thesis is not retrievable (Bielefeld repository refuses access). Do
  not re-search; consequence FP ⟺ PDS. ·
  `pds-strong-coincidence-literature-gate-2026-10-04.md`

- 2026-10-07 · Theorem K's family has no power or rotation in Barge's PDS
  class or its mirror: the initial (and final) letters of `sigma^n` on
  `o, y, z` alternate `(y, o, o)` / `(o, y, y)`, never injective, never
  constant, no common first letter. Do not test Theorem K's members against
  `barge_witness` again. · `p1a-tail-literature-gate-2026-10-07.md` §3

- 2026-10-11 · Flow-to-symbolic: Sirvent–Solomyak 2002 Corollary 5.2 needs
  exactly PIP ("Pisot type") and no unimodularity, so every flow-PDS result
  here (Theorem Ω's 145,806 specimens, the 1,248 Barge-class specimens) is a
  symbolic `Z`-action result too. Primary text verified in the S-adic
  programme's gate §9. Do not re-gate Clark–Sadun or Barge–Kwapisz for this. ·
  `sadic-transfer-literature-gate-2026-10-11.md`

- 2026-10-11 · Brun composites (unordered, admissible, every dimension) with
  irreducible Pisot characteristic polynomial have symbolic PDS: S-adic
  Corollary B″, mirror Barge class. Do not run balanced pairs on them. ·
  `sadic-transfer-literature-gate-2026-10-11.md`

- 2026-10-07 · **Bounded `Z_2` closes the tails for every `Delta`.** With
  `Z_2 <= cap` the members' run patterns are finitely many and fully
  revealed (`w_1` or `u` beginning with `z`, at most `Z_2 + s` z-runs;
  `w_2` at most `cap`), symbolic in `Delta` and the run lengths; split by
  the value of `Z_2` (pieces above `cap` left out) each closes:
  `s = +1, Z_2 <= 1`: 24 patterns, 51 regions, 3 s; `Z_2 <= 2`: 60
  patterns, 748 regions, 45 s; `s = −1, Z_2 <= 2`: 20 patterns, 92 regions,
  2.5 s. Days of the open-tail run tree had not closed what this
  decomposition closes in seconds: decompose by the Pisot factor first.
  · `kernel/odd_letter_family_certificate.mojo` (`zcap_cover`, driver
  `2 zcap s cap budget`)

- 2026-10-07 · The Z_2-cap route, measured beyond cap 3. s = −1, Z_2 <= 4
  does not close: of its patterns, `zy | yzyzyz`, `zy | yzyzyzy`,
  `zy | yzyzyzyz` keep 9, 36 and 10 open regions after the finishers
  (Fourier-Motzkin bounds, implied equalities, point-by-point decision up
  to 2,000 points): the leftovers are finite boxes of up to ~18,000 points
  (`n2` in `[20, 42]`, `n4, n6 <= 27`), slices with large constants
  inherited from earlier carvings, where certificates found elsewhere do
  not extend. Cost per cap: 3 s, 45 s, 82 s for the closed caps, hours at
  cap 4. Witness shapes at `s = −1, Delta = −2`, `|w_1| <= 6` (scratch
  census of distinct members): `Z_2 = 2`: 24 members, 20 shapes; `Z_2 = 3`:
  186, 42; `Z_2 = 4`: 470, 86. The leading shapes at `Z_2 = 3` and `4` are
  the same level-3 paths (`w_1` read from its start, `w_2` from its end),
  so the bulk is uniform in `Z_2`, but the number of shapes grows with it:
  no finite named-path lemma covers all `Z_2` from this census. ·
  `kernel/odd_letter_family_certificate.mojo` (`zcap_cover`); scratch
  `zshape.py`

- 2026-10-07 · Unbounded `Z_2`: Lemma P1 is needed only **linearly**. At
  the McCormick corner `(floor, b_lo)` (`a = Z_2`, `b = |Delta| − 1`) it
  implies one affine form, `2 Y_2 >= Z_2 + 2 Delta − 8` (`s = +1`,
  `Delta >= 2`, `Z_2 >= 3`) and `2 Y_1 >= Z_2 + 3|Delta| − 4` (`s = −1`,
  `|Delta| >= 2`, `Z_2 >= 4`) (`z_floor_forms`). On that polyhedral region
  every non-crossing pair tested is coincident, PIP or not: exhaustive
  `|w_1| <= 9` (`s = +1`: 453 pairs; `s = −1`, `|w_2| <= 13`: in progress)
  holds only PIP pairs (non-PIP region points need longer words), so a
  seeded sample of the **non-PIP** part (seed 1, 150 draws each sign,
  `Z_2 <= 8`, `|Delta| <= 6`; seed 2, `s = +1`, 400 draws, `Z_2 <= 14`,
  `Delta <= 10`) found every pair coincident by level 4 (draw budget 200
  per wanted pair, not exhausted). Outside it, non-PIP pairs do fail (e.g.
  `w_1 = z^k y^3`, `w_2 = z^(k−1)`, `k >= 6`: no tile by level 7), so the
  quadratic is replaced, not dropped. Consequence: the open-tail cover needs
  no McCormick staircase; `2 zfloor s delta floor budget` runs it.
  · `kernel/odd_letter_family_certificate.mojo` (`z_floor_forms`,
  `cover_pattern_guided(z_floor=)`); scratch `lin.py`, `linsamp.py`
  Correction (2026-10-07): the `s = −1` exhaustive run "in progress" never
  started (launched from the wrong directory); the `s = −1` exhaustive figure
  is `|w_1| <= 7`, `|w_2| <= 11`: 1,395 region pairs, all PIP, all coincident
  by level 5. The seed-2 `s = −1` sample (400 wanted, `Z_2 <= 14`,
  `|Delta| <= 10`) was killed out of memory (10.5 GB: `first_tile` expands
  whole level-6 words), so it reports nothing; `s = −1` rests on seed 1 only.

- 2026-10-07 · Unbounded `Z_2`, the z_floor cover run: **what blocks is a
  product inside the certificates, not Lemma P1's staircase.** (1) The
  open-tail trees `2 zfloor 1 2 3 5000 8` and `2 zfloor -1 -2 4 5000 8`
  refine their roots and first children (open regions 12, 59 and 58, 184;
  10–30 min per pattern) and were stopped after ~1 h without a verdict. The
  root's open regions are opaque-tail regions with no certificate, so z_floor
  leaves §3i's doubly open chain where it was. Re-running the cells
  `(+1, 2)` and `(−1, −2)` after the cover-leak fixes
  (`2 cell ±1 ±2 30000 8 plain`) walks the same chain: no verdict after 70
  min. (2) Fully revealed patterns with every run length symbolic, so `Z_2`
  and `Delta` unbounded, under z_floor (scratch `zruns`, budget 5,000):
  `s = +1`, `Z_2 >= 3`, `Delta >= 2`: all 17 patterns with `u` of at most 2
  runs and `w_2` of at most 4 runs close (at most 28 regions, 7 s each)
  except `zy +y^(2+e) | zyzy`, with no verdict after 40 min. `s = −1`,
  `Z_2 >= 4`, `Delta <= −2`: 11 close; `zy | yz` and `zy | yzy` end with 1
  and 2 open regions, and `zy | yzyz` gave no verdict after 25 min.
  (3) The open region of `zy | yz` is `w_1 = z^a y^b`,
  `w_2 = y^(b+2+e) z^(a+1)`, `Delta = −2 − e`. Its witnesses
  `(y, z, −e_o) → (y, z, a e_z − (a+2) e_y) → (y, y, −4 e_o) → (y, y, 0)`
  have `M d = (−4, 2a − 2b + ae, −a)`: the `a b` terms cancel. So the
  level-3 positions `k` (in `y^b`) and `m` (in `y^(b+2+e)`) need
  `k − m = 2b − 2a − ae`. That product is Lemma P1's own:
  `f(−1) = ae + a − 2b + 2`, and `k − m = 2 − a − f`. The certificate is
  affine in `(a, b, e, q = ae)` but not in `(a, b, e)`, so lifting by run
  offsets only carves slices (polynomial line mode's "degree-2 part does
  not vanish"). This one family, with the level-4 offset `t` in `0..2`,
  verifies on 1,134 of the 4,913 members with `a <= 11`, `b < 80`, `e <= 8`
  (brute recomputation, scratch `qcert.py`). In line mode,
  `M (c_0 + lambda (e_z − e_y)) = M c_0 + lambda (0, −Delta, −s)` with
  `lambda` affine and `Delta = D ± e`, so every product a line certificate
  needs has the form `n_j e` (`e` included). **Next:** lift the cover by
  the coordinates `q_j = n_j e`. Lemma P1 then becomes exactly affine, so
  no McCormick wedge is left; certificates become affine; regions are
  polyhedra in `(n, q)` whose real points satisfy `q = n e`, under the
  envelope `q_j >= lo_j e + lo_e n_j − lo_j lo_e`. Do not spend more budget
  on z_floor trees or on fixed-`Delta` cells with opaque tails. ·
  `experiments/z2-route/` (`zruns.mojo`, `onepat.mojo`); scratch `qcert.py`;
  `kernel/odd_letter_family_certificate.mojo` (`cover_pattern_guided(z_floor=)`)

- 2026-10-07 · **The q-lift closes the `s = −1` tail leaf `zy | yz`**
  (`Delta = −2 − e <= −2`, `Z_2 >= 4`): `2 qlift -1 -2 4 5000 zy 0 yz 0`
  ends with 104 regions, 35 certified (20 by polynomial paths lifted over
  `(n, q)`), 6 cut, 34 without a real member, **0 open**, in ~50 s; the
  plain z_floor cover of the same leaf leaves 1 open region of 16. Three
  things were needed besides the lift itself, each a finding: (1) the
  point search must reach the path at all: with offset bound 3 it cannot
  pass `(y, y, −4 e_o)`, and with the line offset bounded it cannot pass
  `(0, −(a+2), a)` once `a > 3`, so the q-lift searches with bound 4 off
  the line and the line position free (`search_witness_line(line_cap=)`);
  (2) the lift must not solve a line coordinate to the point's constant
  (that pins `lambda = a` and carves the slice `a = const`, an endless
  staircase), and among lifts it prefers one whose end offset is zero over
  `(n, q)` (`lift_path_poly(lift=)`); (3) regions without a real point are
  settled exactly when `e` is bounded, by `search_point` on the forms with
  `e` fixed (`_point_search`). Beyond `zy | yz` no verdict after ~15 min
  (budget 5,000, runs stopped): `zy | yzy` walks a staircase in `a` (each
  lifted path carries a bound `a <= const`; 1,293 regions, 11 open so
  far), `zy | yzyz` reports regions open, mostly with no real point found
  (159 of 812 regions so far), and `s = +1` `zy +y^(2+e) | zyzy` (Delta >= 2,
  Z_2 >= 3) walks a staircase in one run length (187 regions, none open). ·
  `kernel/odd_letter_family_certificate.mojo` (`cover_pattern_guided(q_lift=)`,
  main mode `qlift`); `kernel/psc/product_lift.mojo`; `kernel/psc/poly_line.mojo`;
  `test_the_q_lift_closes_the_zy_yz_tail_leaf`

- 2026-10-07 · The q-lift measured, budget 5,000 per pattern, `timeout
  1800` per run (four runs side by side on 4 cores): **only `zy | yz`
  closes; nothing else reached a verdict.** `s = −1` (`Delta <= −2`,
  `Z_2 >= 4`): `zy | yz` closed (104 regions, 0 open, 49 s); `zy | yzy`
  timed out after 1,657 regions (354 line and 232 polynomial paths, 11 open
  with no real point), climbing a staircase that had reached `a = 191`;
  `zy | yzyz` timed out after 938 regions (103 polynomial paths, 1
  polynomial crossing, 161 open with no real point, 26 open with no
  certificate). `s = +1` (`Delta >= 2`, `Z_2 >= 3`): `zy +y^(2+e) | zyzy`
  timed out after 212 regions (206 paths, none open), a staircase of one
  region per value of one run length, which had reached 235. Sweeps
  (`zruns … 4 4 5000 1`, 36 patterns each, timed out): `s = −1` closed the
  first 12 patterns (11 one region or none, `zy | yz` in 48 s) and then
  spent the rest of the time on `zy | yzy`; `s = +1` closed the first 13
  and then spent the rest of the time on `zy +y^(2+e) | yzyz`. **The q-lift
  is not a uniform improvement.** The plain z_floor cover closed
  `zy +y^(2+e) | yzyz` in 3 regions, but under the q-lift it climbs a
  staircase (a 4-minute verbose run: 138 regions, 92 polynomial paths, 42
  open with no real point). The other 23 patterns of each sweep were never
  reached. · `experiments/z2-route/zruns.mojo` (optional `qlift` argument);
  `kernel/odd_letter_family_certificate.mojo` (main mode `qlift`)

- 2026-10-07 · The q-lift's staircases are gone and its no-point regions are
  refuted exactly; **`zy | yzy` now ends with 1 open region, and the q-lift
  closes 2 more `s = +1` patterns in the sweep.** Four additions, all under
  `q_lift` only (flag-off output byte-identical): (1) extent-aware lift
  selection: `lift_path_poly` ranks children by whether the state is affine
  over `(n, q)` and returns the complete lift with the largest `lift_key`
  (number of real probe points of the region, `probe_points`, where the
  carving forms and the zero end offset hold, then lowest offset cost);
  `_poly_carve` lets the tree lift compete with `solve_lift` by that key, and
  `_implied_equality` is substituted eagerly. The staircases came from lifts
  that copy a coordinate of the base point into an offset (pinning `a` in
  `zy | yzy`, one run length in `zy +y^(2+e) | zyzy`). (2) RLT cuts
  (`product_lift.rlt_forms`): `(e − lo_e) g >= 0` and `(hi_e − e) g >= 0`
  for every assumption `g` over `n` alone, expanded with `n_k e = q_k`.
  (3) An exact phase-1 LP (`psc/farkas_lp.mojo`, Bland's rule over
  `finite_exact.Q`) whose answer counts only through a Farkas vector checked
  exactly (`y >= 0`, `yᵀA <= 0`, `yᵀc < 0`), used where a region gets no
  base point; kernel Fourier–Motzkin keeps redundant rows and hits its
  4,000-row cap even on 3 live variables. (4) `_value_split`: a variable
  whose range is bounded by checked certificates is split into its values,
  an exact partition. Measured (budget 5,000): `sweep.sh`, r1 = r2 = 4, 300
  s per pattern, the two signs in parallel: `s = +1` (`Delta >= 2`,
  `Z_2 >= 3`) 30 closed by plain, 2 by the q-lift, 0 open, 4 timeouts
  (was 30 / 0 / 0 / 6); `zyz +y^(2+e) | yzyz` (q-lift 121 regions, 27 s)
  and `zyzy +y^(2+e) | yzy` (193 regions, 66 s) went from timeout to closed.
  `s = −1` (`Delta <= −2`, `Z_2 >= 4`) 25 plain, 1 q-lift, 1 open, 9
  timeouts (was 25 / 1 / 0 / 10): `zy | yz` closes in 42 regions, 10 s (was
  104, 49 s), and `zy | yzy` went from timeout to open. The other 69
  patterns kept their verdicts; every remaining timeout outside `zyz | yz`
  is killed inside the plain cover, so the q-lift never runs on it (this
  includes `zy +y^(2+e) | zyzy`, which the q-lift alone closes in 17
  regions, 3 s). Single runs (`2 qlift -1 -2 4 5000 zy 0 … 0`, `timeout
  1200`): `zy | yzy` 120 regions (49 certified, 46 line, 44 polynomial, 1
  crossing, 2 cut, 58 not member), **1 open**, 89 s, terminating; `zy |
  yzyz` timed out at 1,200 s at region #1293 with 14 open without a real
  point, 3 open without a certificate and 10 value splits traced. **Open:**
  `zy | yzy`'s region is LP-feasible over `(n, q)` with no bounded variable;
  at each fixed `e` it has `n_0 = 3`, `n_1` in `[2e + 11, 2e + 13]`, `n_4` in
  `[e − 1, e]` and no integer point for `e <= 60`, so it needs `e`-parametric
  integer reasoning (a split on an affine form such as `n_1 − 2e`, or
  `e`-parametric Fourier–Motzkin). `zy | yzyz`'s no-certificate regions hold
  real points; their liftable paths sit at depth 4–5, which the shared
  5,000-node point-path enumeration in `_poly_carve` never reaches (0 paths
  at 5,000 nodes, 401 at 2,000,000), so they need a larger or lazy
  enumeration (and `Q_OFFSET_BOUND` there). **Measured, not shipped:**
  splitting off the face `e = 0` first (`zy | yzy` 56 regions, 1 open, 28
  s, but `zy +y^(2+e) | yzyz` 2 → 117 regions and `zy | yz` 42 → 69);
  peeling `e = lo | e >= lo + 1` up to `lo = 8` (no extra closures, more
  regions); a value split from Fourier–Motzkin bounds (never fired: FM hits
  its caps); RLT without the LP (`zy | yzy` 216 regions, 4 open). Not
  proved: termination of the lift selection; it is measured. ·
  `kernel/psc/poly_line.mojo` (`lift_path_poly`, `lift_key`,
  `probe_points`); `kernel/psc/product_lift.mojo` (`rlt_forms`);
  `kernel/psc/farkas_lp.mojo`; `kernel/odd_letter_family_certificate.mojo`
  (`_poly_carve`, `_value_split`); `experiments/z2-route/sweep.sh`

- 2026-10-08 · **The q-lift closes `s = −1` `zy | yzy`** (`Delta <= −2`,
  `Z_2 >= 4`): `2 qlift -1 -2 4 5000 zy 0 yzy 0` ends with 121 regions (49
  certified, 44 polynomial, 2 cut, 59 not member), **0 open**, 91 s. The last
  region needed a value split whose probes carry their envelope
  (`_affine_value_split`): a probe `L >= h + 1` or `L <= h − 1` is refuted
  on the region plus the probe plus `_with_envelope` of that, by bound
  propagation or a checked Farkas certificate, for `L = n_k − c e`,
  `c` in `0..3`; the pieces `n_k := v + c e` (`q_k := v e + c q_e`, with
  `v + c e >= 0` kept) partition the real points. The previous round's
  diagnosis was off: on that region's polyhedron over `(n, q)` no form
  `n_k − c e` (`k` in `{0, 1, 4}`, `c` in `−1..3`) is bounded both ways,
  `n_1 − 2e` included, since `q` is free of `n e` there. What bounds it is
  the envelope of the probe (`n_0 >= 4` raises the McCormick floor of
  `q_0`): `n_0 >= 4` and `n_0 <= 2` are each refuted with their envelopes,
  so the split is the single value `n_0 = 3` (slope 0), and that piece is
  refuted outright. `zy | yz` (42 regions, 0 open, 12 s), `zy +y^(2+e) | zyzy` (17,
  0 open, 3 s) and the flag-off `zcap` runs (byte-identical) are unchanged.
  `zy | yzyz` still times out (`timeout 900`: region #1037, none open yet,
  3 value splits; the old cover reaches #1075 in the same time with none
  open either, so its open regions lie past where 900 s gets). The sloped
  forms (`c > 0`) are exercised by the seeded test only; no cover run has
  needed one yet. · `kernel/odd_letter_family_certificate.mojo`
  (`_affine_value_split`, `_affine_top`, `_refuted_with`, `_value_pieces`);
  `test_the_affine_value_split_partitions_the_real_points`,
  `test_the_affine_value_split_refutes_the_zy_yzy_region`,
  `test_the_q_lift_closes_zy_yzy`
- 2026-10-08 · **A deep lazy lift gives `zy | yzyz`'s no-certificate regions a
  certificate; the leaf still times out.** Under `q_lift` only (flag-off
  `zcap` output byte-identical): `_poly_carve` enumerates point paths with
  `Q_OFFSET_BOUND` (4) through a resumable `PointPaths` and lifts each as
  it comes (`_lazy_lift`): the first `solve_lift` that solves wins, else
  the best `lift_key`, stopping at the first whole-region lift
  (`whole_region_lift`: end offset lifts to zero, carving forms hold at
  every probe point). The ordinary pass keeps 5,000 nodes and 40 paths; a
  region past the peel limit with no certificate gets one deep pass,
  2,000,000 nodes and no path cap, before it is reported open. Running the
  deep pass on every failed lift is ruinous: one `zy | yz` region spent
  175 s (1,320 paths, 155 s in `lift_path_poly`, ~117 ms a path) without a
  whole-region lift. At the four no-certificate regions of the
  `zy | yzyz` run (#1150, #1165, #1198, #1338) the deep pass certifies in
  7–8 s each, two carving nothing. Measured (`timeout` as given, 3–4 runs
  side by side; the lazy-lift branch alone, before the value split was
  merged): `zy | yz` 42 regions, 0 open, 11 s (unchanged); `zy | yzy`
  120 regions, 1 open (no point), 91 s (unchanged); `zy | yzyz` timed out
  at 1,800 s at region #1493 with 15 regions certified by the deep pass,
  none failing, 0 open without a certificate, 18 open without a real
  point, 33 value splits (at 5c43b85, 1,300 s: #1352, 4 / 15 / 16); `s =
  −1` `zyz | yz` timed out at 900 s at #581, 2 deep certifications, 0 / 13
  / 15 (at 5c43b85: #1053, 4 / 38 / 20; the runs diverge at #90, the
  first deep certification). Two of the deep lifts (#1463, #1472) carve
  slices `n_1 >= 67`, `n_1 >= 60`. Not tried: restricting deep line
  positions to anchors (the deep pass already finds its lift in seconds).
  What blocks `zy | yzyz` now is regions with no real point found. ·
  `kernel/odd_letter_family_certificate.mojo` (`_lazy_lift`,
  `_certify_at(deep=)`); `kernel/psc/poly_line.mojo` (`PointPaths`,
  `whole_region_lift`); `test_the_deep_lazy_lift_certifies_a_zy_yzyz_region`
- 2026-10-08 · Round 3 of the q-lift, measured in the sweep: **3 more
  patterns close, none opens; 3 `s = +1` and 8 `s = −1` patterns still time
  out.** Round 3 added the envelope-carrying value split
  (`_affine_value_split`) and the deep lazy lift (`_lazy_lift`), merged
  together (entries above), and `sweep.sh` now gives the two stages
  separate timeouts (`sweep.sh BIN s delta floor r1 r2 budget plain_secs
  qlift_secs`, through `zruns ... at i plain|qlift`), so a pattern whose
  plain cover times out still gets the q-lift; before, every timeout killed
  inside the plain cover never reached it. Measured (budget 5,000, r1 = r2 =
  4, 300 s plain then 600 s q-lift, the two signs in parallel, the full test
  suite running beside them for the first ~hour): `s = +1` (`Delta >= 2`,
  `Z_2 >= 3`) 30 closed by plain, 3 b…13282 tokens truncated… 1)(x + 1)^2`.
  `is_pip` tests irreducibility first, and the `is_pisot_charpoly` verdicts
  agree on all 3,375 cubics. The chain is now built once per cubic rather
  than once per count: `test_census_library` 13.3/14.0 s to 8.5/8.2 s,
  `census.mojo` 91/98 s to 84/88 s. Claim receipts and the full Mojo test log
  are byte-identical before and after. · `kernel/psc/pisot.mojo`;
  `kernel/psc/pisot_screen.mojo`
- 2026-10-06 · Tooling pitfall: `tools/verify_all.sh` and a `uv tool`
  `pytest` fail `manuscript source integrity` when `pypdf` is missing from
  that interpreter. That is the pinned dev dependency (`pyproject.toml`), not a
  manuscript defect; install `pypdf==6.19.0` into the interpreter that runs
  it. · `tests/test_check_manuscript_source.py`
- 2026-10-06 · Symmetry, endpoint maps, Barge class, bounded BPA, Dumont-Thomas,
  return lattices and the strong-coincidence automaton moved to the vendored
  `substitution_dynamics` over an explicit alphabet; only the Perron-field
  reserve and the C4 A..G names stay here. Pitfalls met: `psc.symmetry.word_key`
  renders arbitrary integer lists (cycle lengths, counts), so it stays the
  plain decimal concatenation rather than the package's bracketed letter key;
  pruning-independence makes the shortest coincidence witness, minimised
  sizes and coaccessible counts reproducible under any sound bound, which is
  how the package regressions pin this repository's outputs. Two orbits of a
  self-map of d letters that meet do so within d - 1 steps (exhaustive,
  d <= 6). · finite-math-kernels `tests/substitution_dynamics/`
- 2026-10-06 · Owner decision: the vendored `prolongable_points`
  (`substitution_dynamics/dumont_thomas.mojo`, finite-math-kernels
  `d61bcf8`) reports each letter at its minimal prolongable power only (its
  first return under the first-letter map), as its docstring says, not again
  at every multiple of its period up to `|A|`. Tribonacci now has one
  prolongable point `(1, 0)` instead of `(1, 0), (2, 0), (3, 0)`;
  `test_oa_overlap_types` pins that. In `oa_type_inclusion_census` and
  `oa_failures_probe` only the `"points"` field of 17 of the 22 per-specimen
  JSON lines drops (3 -> 1, 5 -> 3, 6 -> 2), where the dropped powers were
  duplicates giving the same fixed-point word; union types, witnesses, every
  CI-pinned summary line and the claim receipts are byte-identical. The
  per-specimen lines are recorded nowhere in the repository. ·
  `kernel/tests/test_oa_overlap_types.mojo`; `kernel/oa_failures_probe.mojo`

- 2026-10-06 · Repository-wide PSC research audit confirms the canonical
  status is coherent after #153: PSC and `OP_seed`/#84 remain open, and no
  accidental PSC promotion was found. Highest-priority review debt is the
  October 4 PDS => PPVC/G1 => all-seed-termination chain, whose live surfaces
  still say human review pending. Research priority is narrowed to seed-strength
  #84 plus an occurrence-compatible adelic coverage/alignment theorem for #139;
  #9 should supply only portable ordered-factorization lemmas. PR #223's
  Dumont–Thomas streaming regression is resolved at the current FMK pin;
  PR #221 should not merge unchanged because its side-notes entry is missing
  and its base predates the current vendoring state. No claim status changes. ·
  `audit-2026-10-06.md`
- 2026-10-07 · Dated correction to the October 6 PSC audit entry: PR #221 was
  rebased, supplied its required benchmark/ledger locator, revalidated, and
  merged at 00:45:58 UTC as `f09627e377abae49e5a4bf13694cb0e15f11ed36` after
  green current-head workflows and a no-findings review. Its tooling finding
  is resolved; the October 6 snapshot and prior ledger entry remain intact.
  No mathematical claim or review status changes. ·
  [October 7 follow-up](audit-2026-10-06.md#7-follow-up-2026-10-07);
  [PR #221 evidence](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/221)
- 2026-10-07 · Specimens already settled by the literature: Tribonacci,
  Kol(3,1), the two Sirvent–Solomyak ternary examples, the Arnoux–Rauzy
  product `σ₁σ₂σ₃`, and the three circulated Rauzy-fractal examples
  `12,31,1` / `12,23,312` / `123,1,31` all terminate with coincidence on the
  all-seed `B_sigma`; six of them lie inside the 145,806-specimen
  finite domain. The circulated `123,1,1132` has `det M = 0` and is not PIP.
  The Sirvent–Solomyak count of 260 pairs of length 194 is not reproduced
  under the `(ab,ba)` seed convention (257 / 137); it stays unconfirmed until
  checked against the paper's full text. No claim status changes. ·
  [motivations note](motivations/ternary-literature-context-2026-10-07.md);
  `kernel/tests/test_ternary_literature_specimens.mojo`
- 2026-10-07 · Adversarial audit of Proposition V and Theorem E found no
  disproof and no failing proof step. An independent oracle reproduced every
  computational input: the Theorem E class enumerated to image length 5 stays
  in the normal form and is coincident; the 27-member residue was reproduced;
  the Proposition V radii hold with margin ≥ 2. Four presentation fixes were
  applied to the A1′ note: "position" means prefix length, L_BC's dead
  `r = q = 0` clause was removed, two endings have det divisible by 4, and
  §3b.7 line ranges are now explicit. The dead clause stays in the kernel's
  `lemma_witness`, where it is unreachable. No claim status changes. ·
  `audit-adversarial-prop-v-theorem-e-2026-10-07.md`,
  `archive/2026-10-07/session-probes/`
- 2026-10-07 · Correction to the entry above: the dead L_BC clause is now also
  removed from `lemma_witness` in `kernel/a1_normal_form_census.mojo`.
  `tests/test_a1_normal_form.mojo` passes unchanged (453 named witnesses,
  27-point residue), which confirms the clause never fired. ·
  `kernel/a1_normal_form_census.mojo`
- 2026-10-07 · The 145,806-specimen PDS statement does not need Theorem B,
  Lemma C, Proposition F, Theorem R, Theorem S or Proposition V(2): step 1 of
  Proposition V (cycle vertices lie in the box, a geometric series) with
  Proposition FP turns the recorded box verdicts and SC_all into formal
  productivity, and FP gives PDS both through Lee–Moody–Solomyak overlap
  coincidence and through Theorem 5.38. It also certifies termination with
  coincidence from every swap seed, so the 120 budget-exhausting cube-family
  specimens need no direct `B_sigma` build. The swap-seed graph misses box
  cycle vertices (38 on the cube specimen), so it cannot replace the box on the
  literature route. A fresh re-derivation of Lemma C, Theorem B, Proposition F,
  Theorem R and depth-note Propositions 1/4 found no error. ·
  `pds-certificate-from-the-box-automaton-2026-10-07.md`
- 2026-10-08 · The 145,806-specimen PDS statement is promoted to the claim
  ledger as the finite-domain theorem `BoundedPureDiscreteSpectrum` (claim
  map row "Finite-domain pure discrete spectrum"). The proof-dependency
  ledger is unchanged, because the claim is finite-domain, not a universal
  implication. ·
  `pds-certificate-from-the-box-automaton-2026-10-07.md` §§5, 9;
  `claim_governance.toml`
- 2026-10-08 · PR #228's Python oracle `_poly_rem` now caches the exact
  leading reciprocal and nonzero divisor terms for degree >= 4; small divisors
  retain dense division after setup overhead was measured. Independent dense
  quotient/convolution checks cover 4,800 rational pairs (324 cached-path
  cases); all 3,375 cubic caller results agree. Recorded sparse degree-12/32
  workloads improve 3.19×/7.43× in elapsed time; no uniform dense or whole-screen
  speedup is claimed. The unrecorded "14s to 8s" figure is withdrawn and the
  PR's incorrectly dated `2024-05-18` `.jules/bolt.md` entry is removed.
  The tracked Markdown-link guard requires a removed file's deletion to be
  staged before replay. No mathematical claim status changes. ·
  [scope, regression and replay](poly-rem-sparse-rational-2026-10-08.md);
  [pinned benchmark](../evidence/poly-rem-sparse-2026-10-08/benchmark.json)
- 2026-10-08 · Seed strength buys no slack in truth: for each PIP `sigma`,
  one productive swap seed ⟺ every seed ⟺ FP ⟺ PDS (Theorem 5.38 forward,
  Corollary FP″ back), so do not look for a seed that avoids an obstruction.
  The object does depend on the seed: on 444 of 4,554 standing specimens the
  three seeds reach different recurrent parts, and none is ever empty. The
  census domains are closed under reversal, so the prefix SC census already
  gives two-sided SC on 408,798 specimens. Class B lines with slope 3 and
  `r = q − 1` leave PIP (a second eigenvalue of modulus 1, or above it). ·
  `p1-seed-strength-2026-10-08.md`
- 2026-10-08 · Class B swap-seed graphs are constant on sectors of the
  `(q, p)` plane bounded by slopes `1, 3/2, 2, 5/2, …` (74 / 226 vertices for
  `r = q + 1`; 123 / 171 / 217 for `r = q − 1`), with sectors accumulating at
  slope 3; along `p = 3q + 11 − d`, `d` fixed, the graph grows linearly in `q`
  (`d = 0`: 2,655 → 4,893 vertices for `q = 8 → 28`). Do not look for a finite
  symbolic graph on the top layer: it needs an index variable. Scans are
  scratch exact-kernel runs at `q = 12, 20, 21, 28, 40`. ·
  [cone note §1, §5](p1b-symbolic-cone-2026-10-08.md)
- 2026-10-08 · Retired for two parameters: the parametric Sturm–Tarski sign
  reader of `psc.symbolic_line`. Its sequence entries need not keep one sign
  on a 2D region even when the query does; the cone engine brackets `beta`
  between certified rational functions instead. On Theorem L's line the
  bracket method certifies from `q >= 6`, where Sturm needed `q >= 52`. ·
  `kernel/psc/symbolic_cone.mojo`
- 2026-10-08 · Tooling pitfall: Pólya's multiplier cannot certify a
  polynomial whose top form vanishes on a ray of the orthant (e.g.
  `(s1 − s2)^2 + s1 + 1`, or a one-variable polynomial lifted by
  `1 + u + v`); the region reader lifts only by the coordinates that occur. ·
  `kernel/tests/test_symbolic_cone.mojo`
- 2026-10-08 · Rauzy representability of the closed claims: of the 47
  closed repository-proved claims (44 ledger nodes with complete closure plus
  three hand-ledger claims), 11 are natively statements about adelic Rauzy
  pieces, 2 partly, and 34 not: they use degree ≥ 2 subword or free-Lie
  invariants that the Parikh map erases, or stay on `Z^A` without reaching
  the projection (factoring through ℓ is necessary, not sufficient). The shortest PDS route and
  the #139 frontier lie on the Rauzy side. This is an interpretive map; it
  moves no claim status. · `rauzy-representability-2026-10-08.html`
- 2026-10-08 · Correction to the 2026-10-08 `BoundedPureDiscreteSpectrum`
  entry above ("the proof-dependency ledger is unchanged"): the two notes' proved results are
  now proof-dependency (TLA+) nodes. Box note: `BoxCycleContainment` (Lemma Ω1),
  `BoxAutomatonCertificate` (Theorem Ω), the open gate `FormalProductivity`,
  the import `OverlapCoincidenceCriterion` (LMS 2003 Lemma 6.9 + Thm 4.7, LS
  2012 Thm 4.3), and consequences (a), (b), (c) as `PDSFormalProductivityRoute`,
  `PDSFormalProductivitySeedRoute` and `G1FormalProductivityRoute`; the last
  is a fourth alternative establishment of canonical G1. Leftmost note:
  `LeftmostChainCycleStructure` (Lemma S, Proposition LC, Corollary LC4) and
  `LeftmostChainG1Certificate` (Corollary LC5). Routes (b), (c) and LC5 cite
  Theorem 5.38 and Propositions 5.46/5.47 for their mechanism but do not depend
  on those nodes, which bundle the weaker open seed gates (the D.4
  resolution). New model `MCLedgerFormalProductivityGateAssumed`: FP with the
  two imports reaches G1 and both PDS routes, and leaves PDS, SCC Producer and
  every seed gate unestablished; all 15 TLC models hold. No status of PSC, G1
  or any gate changes. ·
  `tools/make_ledger.py`; claim-map rows from "Cycle vertices lie in the box
  automaton" and "Leftmost-chain cycles are prefix-vs-interior pairs"
- 2026-10-08 · Review of the two notes before promotion, from the statements:
  Lemma Ω1(1) needs the map `w -> (<ell, w>, (sigma_k <ell, w>)_k)` to be
  invertible over `R`, not only injective on `Z^3`; it is, since it factors as
  a Vandermonde matrix of the distinct conjugates of `beta` times the rational
  coordinate matrix of `ell`, which is invertible by `Q`-independence. Ω1(2)'s
  bound uses `|1 - sigma_k(beta)^p| >= 1 - mu_k^p` and
  `sum_{n<p} mu_k^n <= (1 - mu_k^p)/(1 - mu_k)`. Theorem Ω's descent needs every
  non-coincident overlap to have a child, which holds because the sub-tiles
  of each image cover their tile up to finitely many points. In Proposition LC
  claim 5, "the composite fixes `c = 0`" follows directly from the definition of
  the leftmost child (each edge maps the parent's left region end to the
  child's), so Lemma C step 1 is not needed, and the M-adic-centre remark
  (Proposition P″(a)) is not load-bearing. `LeftmostChainCycleStructure` thus
  has no ledger dependency. Corollary LC4's involution maps the leftmost child
  to the leftmost child because it translates the region by `-t`. Corollary
  LC5 uses Lemma Ω1(2) for "terminal-SCC vertices lie in the box", and needs
  each `Z(s)` vertex to have a child, which holds because it is not a
  coincidence. No error found. ·
  `pds-certificate-from-the-box-automaton-2026-10-07.md` §§3–4;
  `p1b-leftmost-chain-periodic-pair-2026-10-05.md` §§3–4, 8a
- 2026-10-08 · Two two-parameter engines agree on class B's wedge `q < p < 2q`:
  `psc.symbolic_cone` (Theorem C) and the line engine generalised to
  `Q[s, d]` (commit `5ee3f0f`, not merged). They were written separately
  but share `psc.symbolic_line`'s primitives: support primitivity, offset-zero
  reachability, and the exact Sturm reads at sample points. Every shared
  vertex count matches. The second engine also showed where the Sturm chains break
  inside a region:
  - along `d^2 ≈ 8s`, where the conjugate pair turns from real to complex;
  - along the irrational ray `d/s = (1 + sqrt 5)/2`, through a leading
    coefficient.

  Rouché (`|c_2| > 1 + |c_1| + |c_0|`) decides PIP there with three sign reads
  and no bracket. ·
  `p1b-symbolic-cone-2026-10-08.md` §4;
  `archive/2026-10-08/class-b-wedge-crosscheck/`


- 2026-10-08 · Reconcile #236/#237 after #241 merged at `33a1b8b`: keep
  its Ω1/Ω/LC grouping and formal-productivity model, retain both independent
  review notes, add separate Meyer/import and per-specimen box-PDS evidence,
  and preserve the open uniform gates. LC's prefix object is a right-infinite
  ray; zero child indices are on the later-starting side. The census completion
  gate now raises on caps and refuted sign/shape or integral replays; 456 long
  offsets remain uncomputed. Source-inventory and compiled Lean audit are
  separate: root `PscVerif.lean` proofs must be inventoried, and a dependency
  at its pinned HEAD with tracked edits must refuse verification. Seven added
  negative cases reproduce these P2 defects on #237 and pass after repair. ·
  [reconciliation and source mapping](proof-ledger-reconciliation-2026-10-08.md);
  `tests/test_proof_bank.py`; `kernel/tests/test_leftmost_chain.mojo`
- 2026-10-08 · LC claim 5 fixes the region end directly by the definition of
  each leftmost child; its prose proof now states this, matching #241's review
  and dependency-free cycle-structure node, without invoking Lemma C. ·
  `p1b-leftmost-chain-periodic-pair-2026-10-05.md`, Proposition LC proof step 5
- 2026-10-08 · Current-head review of the reconciliation found an additional
  dependency gap: hiding untracked files lets an injected Lean source pass at
  the correct HEAD. Pin verification now rejects nonignored untracked files;
  two additional negative controls reproduce the gap before repair, while
  ignored build-cache artifacts remain usable. · `tests/test_proof_bank.py`;
  `tools/make_proof_bank.py`
- 2026-10-08 · The ignored-file review extends dependency refusal beyond
  ordinary Git status: a local Git exclusion can hide an injected Lean source.
  Ignored files are now enumerated separately; source/configuration inputs and
  ignored files outside the declared build-artifact paths refuse verification.
  Four new negative controls cover ignored Lean and cache-adjacent TOML inputs
  in both pin-check modes. The thirteen root/pin negative cases pass. ·
  `tests/test_proof_bank.py`; `tools/make_proof_bank.py`
- 2026-10-08 · Git status alone also hides tracked edits marked
  assume-unchanged or skip-worktree. Dependency verification now compares
  actual tracked bytes, file types and executable modes with HEAD's tree,
  without changing the index. Four negative controls reproduce these flag
  bypasses; all seventeen root/pin cases pass, as do the real nine manifest
  checkouts. This is source/pin verification, not a compiler or proof receipt. ·
  `tests/test_proof_bank.py`; `tools/make_proof_bank.py`

- 2026-10-08 — A fresh pinned Lake build exposed normal ignored outputs outside the initial cache allowance: `.lake/build/ir/**/*.setup.json`, `.lake/build.barrel`, and `.lake/build.barrel.trace`. Permit only those generated paths in addition to the existing caches; dependency regressions now carry these real output shapes while still refusing all source/configuration injections. Local Lean startup required a scratch-only shim mapping its own numeric `/proc/<pid>/exe` lookup to the identical permitted `/proc/self/exe`; no compiler, kernel, or dependency source was changed.
- 2026-10-08 — During integration validation, #236 was independently rebased to `3eb62008d39aa3a531b27980615972e0d5b80a44`. Compare that current head as well: retain its two added vertex-test claim declarations and reconciled-baseline metadata, keep the explicit Meyer import and partial Lean spectral locators, and preserve #241's direct leftmost-child fixed-end proof. No new mathematical premise is discharged. Evidence: `docs/proof-ledger-reconciliation-2026-10-08.md`, `kernel/tests/test_vertex_coincidence.mojo`, and `tests/test_ledger_generation.py`.
- 2026-10-08 — Current-head review reproduced another source-integrity bypass: Git replacement refs make a pinned HEAD and clean status expose an altered tree. Disable replacement objects for every dependency inspection. Two real replacement-commit controls fail before the repair and pass afterward; nineteen root/dependency negative cases now cover the original P2s and follow-up findings. Evidence: PR #237 discussion 4225106073, `tests/test_proof_bank.py`, and `tools/make_proof_bank.py`.
- 2026-10-08 — The root-module repair did not alone make all valid Lean headers visible: `nonrec`, `public`, other pinned declaration modifiers and multiline headers/attributes could omit named proofs. Inventory the complete pinned modifier vocabulary and balanced attributes across line breaks. Six failing-before/passing-after controls require each proof in the source bank and reject its omission from an audit receipt; all twenty-five inventory/dependency negative controls pass. Evidence: PR #237 discussion 4225149030, Lean v4.34.0-rc2 `Parser.Command.declModifiers`, and `tests/test_proof_bank.py`.
- 2026-10-08 — Compact scoped Lean commands can put a theorem after `open ... in` or `set_option ... in`, beyond the supported source-header grammar. Detect every otherwise unaccounted theorem/lemma header and refuse inventory rather than silently omit it. Two additional negative controls reproduce the omission before this guard; twenty-seven inventory/dependency controls now pass. Evidence: `tests/test_proof_bank.py`, `tools/make_proof_bank.py`.
- 2026-10-08 — Private Lean proof names are internally mangled, so direct source-name comparison rejected valid private theorems/lemmas. Audit replay now emits Lean's native `privateToUserName` normalization alongside the unique compiled name and origin module. Reconcile source proofs by module/name while retaining raw declaration/theorem counts; support identical private helper names in distinct modules and refuse ambiguous claim bindings. Reproduced the original missing-name failure and added private theorem/lemma compatibility plus missing-module controls. Evidence: PR #237 discussion 4225196994, `proof/PscVerif/ProofBankAudit.lean`, and `tests/test_proof_bank.py`.
- 2026-10-08 — Final review raced with main's merge of #244 at `d98e027f8f22400fd827fbce8635d3f6a8ea2e6d`. Integrate its class-B cross-check documentation and archived logs byte-for-byte, preserve both independent append-only side findings, and regenerate the source inventory. Its shared-primitives and provenance-versus-proof boundary stays explicit; no PSC/G1/PDS premise changes. Evidence: `docs/proof-ledger-reconciliation-2026-10-08.md`, `archive/2026-10-08/class-b-wedge-crosscheck/README.md`.

2026-10-08 — Current-head cache review: source pins do not attest ignored compiled dependencies. Lean verification now discards caller compiled caches/configuration, clones and byte-checks fresh pinned dependencies, and uses a fixed upstream Mathlib source-hash cache in an empty temporary directory before compiling PSC and replaying its axiom audit. A forged-artifact/metadata and environment-override regression fails against the prior dispatcher; compiler and upstream cache trust remain explicit. No mathematical claim status changes.

2026-10-09 — Current-head compiler-selection review: inherited Elan environment/directory overrides outrank lean-toolchain files. Verification now invokes every Lake command through the explicit checked-in Elan toolchain and refuses mismatched Lean/Lake executable versions before building. Four negative controls reproduce the override/version mechanisms; no mathematical claim status changes.

2026-10-09 — Main advanced to 8d91e48 through #245 during final review. Reconciliation retains its Rouche-first symbolic-cone certificate, Jury fallback and regression, with the changed Mojo test rerun and its actual receipt refreshed. Canonical ledger nodes and Lean sources are unchanged; governed inventories are regenerated on the new main.

2026-10-09 — Current-head review found compiler overrides also affected provisioning. Setup now forces the exact checked-in Elan toolchain, refuses Lean/Lake version mismatches and clears inherited Lean/Lake/cache configuration before cache preparation. Four failing-before/passing-after setup controls cover both overrides and version probes. Development setup grants no formal audit credit; the Lean README routes verification to the isolated complete audit and preserves partial formalization boundaries.
- 2026-10-08 · The line certificate is not class-B specific: on 32 lines of
  Theorem E's classes A (slope 2), C and D it certifies boundary hitting from
  every seed (Theorem L″), and every refusal met was a line outside the
  Pisot class. Class A at slope 1 is different: its seed graph grows linearly
  in `n` (235 → 915 vertices for `n = 3 → 20` at `p = n + 1`), so the
  constant-graph method cannot reach it. Do not rerun it there with a larger
  budget; it needs vertex families indexed by a run position. ·
  `p1b-boundary-hitting-progress-2026-10-08.md` §§3–4
- 2026-10-08 · Two-parameter certificates need three changes from the line
  method, each forced by a concrete failure on class D. (1) Per-entry Sturm
  signs fail: the PIP test's last Sturm entry is the discriminant, which
  changes sign on a parabolic region `b ≲ √(2a)` along an edge. Use instead
  `χ(−1), χ(1), χ(2) < 0`, which is equivalent to Pisot when `|det M| = 2`.
  (2) Sturm–Tarski entries for realness signs change sign along irrational
  rays (slopes `2√2`, `(3 ± √17)/2`), which no rational split avoids. Read
  `sign h(β)` from a nonvanishing norm `det h(M)` plus one sample point. (3)
  Coefficient positivity alone misses forms like `a² − ab + b²`, so add a
  Pólya multiplier. Separately, a whole class-D cone cannot be one wedge,
  because a run-position bound changes regime along `3r = 4q`. Split it at
  the Farey directions `(1,1), (3,4), (2,3), (1,2)`. The same norm reading
  also helps lines that lie beside such a ray. A boundary line on
  `3r − 4q = −9` has threshold 196 by Sturm entries (about 5 h of exact
  finite part) but 4 by norm. Certify wedge edges in norm mode. ·
  `p1b-boundary-hitting-progress-2026-10-08.md` §4b

2026-10-09 — Isolated #247's parameter-algebra refactor (`a3f1b15`) against
#246's pinned pre-refactoring head (`e068c4c`). Both earlier engines inherited
noncanonical `t`-polynomial keys for trailing zero terms; the shared module's
key contract now strips that padding, with a failing-before regression.
Independent monomial evaluation, specialized Euclidean division, denominator
boundaries and three killed coordinate-reversal controls guard the conversion
`(s1, s2) = (b, a)`. Direct replay agrees on the asymmetric 74-vertex class-B
graph (including edges and hitting decisions) and the 105-vertex class-D wedge
(corner `(1, 0)`, 1818 sign reads). This records computational preservation;
#246's separate mathematical review and Corollary W1 acceptance boundary are
unchanged. Evidence: `kernel/tests/test_param_poly.mojo`,
`kernel/tests/test_symbolic_cone.mojo`, `kernel/tests/test_symbolic_line.mojo`,
and the scoped review on PR #247.


2026-10-10 — PR #250 Python-oracle matrix unrolling preserves the exact
integer map: each output is the same three products in the same order;
81 matrix-unit pairs and asymmetric signed, zero/identity, 256-bit boundary,
rational and seeded mixed-entry regressions guard indexing and nonmutation.
The pinned original full module and revised module differ in AST only at
`mul`; all 4,554 ordered corpus entries agree at warm-up and every timed run.
Seven alternating full-corpus pairs on Python 3.12.14 / AMD EPYC 9V74,
one CPU affinity, give median 2.6361 s before and 1.7996 s after (31.73%
elapsed reduction on this shared host). The original ~7.9/~4.8 s and 40%
claim lacks preserved context and is not independently reproduced; historical
2024-05-18 dates and broad polynomial optimization claims from `.jules/bolt.md`
are unverified for this experiment. Remove that competing log; no polynomial
algorithm changes or new mathematical claims are made. Evidence:
`tests/test_pip_matrix_mul.py`, `oracles/python/pip_mul_benchmark.py`
(replay from repository root with Python and the pinned git history), and
`evidence/pip-mul-2026-10-10/benchmark.json` (machine context, raw wall/CPU
samples, source/replay digests and ordered-corpus digest).

2026-10-10 — PR #250 replay correction: fresh review found that Python `-O`
stripped `assert` provenance guards. Replace them with explicit exceptions;
optimized-mode negative controls reject unrelated source drift and a corrupt
matrix kernel without emitting a report. The first `benchmark.json` remains
verbatim and names its original replay digest; the corrected replay under
`python -O` is separately preserved as `benchmark-guards-r2.json`, with its
new replay digest and optimization level. Its seven-pair medians are 2.5266 s
before / 1.7929 s after (29.04% reduction); performance is host/run-dependent,
not a fixed 40% promise. Pin both recorded outputs in the packet's
`SHA256SUMS`, as required by the recorded-data integrity guard. Evidence:
`tests/test_pip_mul_benchmark_guards.py`,
`oracles/python/pip_mul_benchmark.py`,
`evidence/pip-mul-2026-10-10/benchmark-guards-r2.json`.

2026-10-10 — PR #250 CI replay-test correction: Actions uses a shallow
checkout, so negative-control tests must not request the pinned historical
module through git. Stub the baseline read with the local source, then inject
an unrelated AST node or a zero matrix kernel; both optimized-mode refusal
paths remain exercised without history. The actual benchmark intentionally
requires the pinned baseline history and continues to fail if it is absent.
Evidence: `tests/test_pip_mul_benchmark_guards.py` and failed Actions job
`114294069121` (515 other tests passed; two history-dependent controls failed).

- 2026-10-12 · governance: independent human review is a final validation gate,
  not a research-progress gate. `human review pending` is non-blocking
  validation debt: repository proof development, provisional dependency use,
  and closure construction continue; truthful status labels remain mandatory,
  and the assembled closure chain receives independent review afterward.
  Machine source: `claim_governance.toml [review_policy]`; synchronized human
  surfaces: `README.md`, `AGENTS.md`, `docs/README.md`,
  `docs/research-roadmap-2026-09-21.md`, and
  `docs/verification-architecture.md`.

2026-10-13 — Nakaishi arXiv:2401.07771v1 §13 Proposition 5 equates first simultaneous C×C entry with first second-coordinate C entry along N_i, despite a positive-measure early second-coordinate-only event at N_0; the measure partition used against Proposition 4 is unproved as written. This is a source-audit objection, not a PSC counterexample or final refutation. The paper's mixing / special-cylinder / Garsia separation mechanisms remain research leads for exact occurrence-compatible #139 hitting, contingent on repaired conditioning and non-unit adelic transfer; no theorem import or status promotion. Evidence: `docs/nakaishi-2024-first-entry-audit-2026-10-13.md`, arXiv:2401.07771v1 §§12–13, eqs. (24), (29), Proposition 5.

2026-10-13 — PR #258 validation repair: all four failing jobs (python-tests,
source-provenance, lean-proofs, exact-kernels) refused a stale proof-bank input
digest after the review-policy edit. The Lean job stopped before compilation;
exact equivalence, Mojo regressions and census checks passed. Regeneration changes
only the claim_governance.toml digest, preserving claim statuses, dependency edges
and named Lean proofs. Preserve both append-only entries when merging main.
Evidence: Actions runs `38294266656`, `38294266627`,
`proof/proof-bank.json`, `tests/test_review_policy.py`.
