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

- 2026-10-12 · **Retired: predecessor contraction for full BPA closure.**
  The proposed parent-bound `beta * L(s') <= L(s) + D` from one selected
  child `s` of `sigma(s')` is invalid: Parikh-contact decomposition can
  distribute inflated parent mass among multiple children. Do not use it
  to infer finite reachable balanced-pair closure or G1. **Retain only the
  conditional K2 result:** a dominant length-two swap source and K2
  additivity imply that *if its reachable balanced-pair closure is finite*,
  some recurrent SCC has transition spectral radius at least
  `beta * |beta_2|`; finiteness is still an unproved hypothesis. ·
  `docs/k2-load-bearing-scc-salvage-2026-10-11.md` §§"Conditional theorem:
  load-bearing SCC under finite closure", "Retired proof pattern:
  predecessor contraction"
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


- 2026-10-15 · **Correction to box-walk reachability claim (2026-10-12 notes and PR #253).**
  The historical `box_walk_recurrence.py` zero-stuck count comes from
  reverse reachability to the *zero imbalance vector*, although a genuine
  diagonal child requires zero imbalance **before equal next letters**.
  Example `12|21` has a terminal zero return and no diagonal child.
  Projected vector edges collected across different occurrences can also
  splice nonrealizable paths; observed depth-wise edge plateaus do not prove
  substitution successor closure. “Every vector can reach zero” is therefore
  **not** a matched-origin or SCC-productivity certificate. Correct
  conditions: occurrence/address-compatible path lifting, target-aware
  equal-letter zero-return, complete finite successor closure and explicit
  seed/vertex quantifier coverage. Existential escape does not mean every
  infinite path must hit a target. No PSC/G1/SCC Producer claim changes. ·
  `docs/boxwalk-reachability-realizability-audit-2026-10-15.md`;
  `docs/audit-2026-10-11-boxwalk-extremal.md` (2026-10-15 correction)

- 2026-10-15 · **Scope of exact depth-nine radius witness.** The replayed
  `sigma=(001,22,220)` has characteristic polynomial
  `x^3-4x^2+4x-2` and a **complex** secondary pair. Its aligned-cut
  depth-nine radius `10` refutes a radius-eight bound *for that observable*
  but alone says nothing decisive about a proposed **real-secondary-only**
  radius bound or the unrecovered staircase/comp-set statistic. Do not
  transfer across observable, seed, or spectral regime. ·
  `docs/boxwalk-reachability-realizability-audit-2026-10-15.md`;
  `evidence/boxwalk-radius8-depth9.json`

- 2026-10-22 · **Class-A literal d=1-to-d=2 carrier transfer refuted uniformly.**
  The accepted 89-row strict-overlap carrier for `d=1, eps=+1` cannot be
  transplanted unchanged to `d=2, eps=+1`, for any integer `n>=4` (within
  the plus PIP domain `n>=0, 1<=d<=2n+11`). Its historical row
  `(top,bottom,s,y,a,b,A,B)=(y,y,0,-2,-1,0,0,0)` includes the formal state
  `(y,y,w)` with `w=(-n,n+2,-2)`. At the unique positive root of
  `P_2(n,h)=1-(n+1)h-(n+2)h^2-2h^3`, `h=1/(beta-1)`, monotonicity and
  `125 P_2(n,1/5)=88-30n<0` give `0<h<1/5`. The necessary strict-overlap
  margin is `T(w)+L_y=1-h-2n h(1+h)=-1+h+4h^2+4h^3<-76/125<0`:
  the tiles are disjoint, not boundary-touching. This retires the literal
  carrier transfer, **not boundary hitting**; it asserts neither seed
  reachability of the formal witness nor nonproductivity or a PSC
  counterexample. The accepted d=1 proof is unaffected; a d-dependent,
  sign-aware carrier remains the constructive target. Evidence: written
  all-parameter argument in `docs/class-a-residual-geometry-2026-10-22.md`,
  "A uniform obstruction to transporting the 89-row gap-one carrier";
  canonical `kernel/psc/class_a_residual_geometry.mojo`
  (`_check_d2_nontransfer_rows`), with the historical row in
  `kernel/psc/class_a_typed_carrier.mojo` (`template_rows`);
  independent sparse-polynomial oracle
  `oracles/python/class_a_residual_geometry.py` (`d2_witness`);
  `kernel/tests/test_class_a_residual_geometry.mojo` (exact native
  `n=4,d=2` strict-overlap refusal, invalid-sign and missing-row controls)
  and `tests/test_class_a_residual_geometry.py` (both-sign identities and
  corrupted-identity controls). Replay: the note's "Replay, negative
  controls and precise next obligation" and
  `.github/workflows/class-a-residual-geometry.yml`. No claim status changes.

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
  `Z_2 >= 3`) 30 closed by plain, 3 by the q-lift, 0 open, 3 timeouts (was
  30 / 2 / 0 / 4); `s = −1` (`Delta <= −2`, `Z_2 >= 4`) 25 / 3 / 0 / 8 (was
  25 / 1 / 1 / 9). The verdict changes, all to closed by the q-lift:
  `zy +y^(2+e) | zyzy` (timeout → q-lift 17 regions, 3 s, after the plain
  cover's 300 s), `s = −1` `zy | yzy` (open → 121 regions, 93 s; the value
  split) and `s = −1` `zyzy | zyz` (timeout → 7 regions, 2 s, after the
  plain cover's 300 s). The first and third come from the separate
  timeouts alone; the other 69 patterns keep their verdicts, and the
  region counts of every pattern closed in both sweeps are unchanged.
  **Open:** the 11 timeouts, every one killed in the q-lift as well: `s =
  +1` `zyzy +y^(2+e) | yzyz`, `| zyz`, `| zyzy` (plain and q-lift both
  killed); `s = −1` `zy | yzyz`, `zyz | yzy`, `zyz | yzyz`, `zyzy | yz`,
  `zyzy | yzy`, `zyzy | yzyz`, `zyzy | zyzy` (both killed) and `zyz | yz`
  (plain 45 regions, 1 open, 13 s; q-lift killed at 600 s). `zy | yzyz`
  alone (`timeout 1800`) reaches region #1215 with 1 region open without a
  real point; `zyz | yz` (`timeout 900`) reaches #563 with none open; what
  blocks both is time, then regions with no real point found. **Measured,
  not shipped:** the lazy lift without the value split reaches further in
  the same time (`zy | yzyz` #1493 against #1215 in 1,800 s) but leaves 18
  regions open without a real point (8 by #1215) and `zyz | yz` 13 by #581;
  the deep pass on every failed lift (one `zy | yz` region 175 s). The
  sloped forms (`c > 0`) of the value split still fire in no cover run. ·
  `experiments/z2-route/sweep.sh`, `zruns.mojo` (`at i plain|qlift`);
  scratch `/tmp/claude-0/r5/sw/sweep-{plus,minus}.txt` (against
  `/tmp/claude-0/r2/final/sweep-{plus,minus}.txt`)

## 4. Withdrawn or unreproducible figures

- 2026-10-04 · "1,764 formal producer-free cycles; maximum death radius 7;
  collar tested to 40" (`completion-ledger-2026-09-11.md` §V): no instrument
  exists in the repository or the archive. Superseded by the exact
  formal-overlap carrier census. · `formal-overlap-carriers-2026-10-04.md` §1

## 5. Finite observations worth not recomputing

- 2026-10-04 · Formal carriers: 13,260 on the corpus (6,078 realized, 7,182
  unrealized), none closed, no nonproductive potential overlap; identical
  under three different seeding regions. Realization separates the escape
  mechanism (aligned and fast vs strict and slow), not productivity. ·
  `formal-overlap-carriers-2026-10-04.md`; receipts in
  `evidence/formal-overlap-carriers-2026-10-04/`
- 2026-10-04 · The §5.6b trichotomy holds on all 24,486 specimens of total
  length ≤ 8: no exception; every total Q1 failure is catch-up-free; P′ exact.
  · `p1b-vertex-coincidence-box-2026-10-02.md` §5.6c
- 2026-10-04 · The catch-up-free class is not confined to `|det M| = 2`: 84 of
  654 at total length ≤ 8 have another determinant (all 210 corpus members
  have `|det M| = 2`). · same, §5.6e
- 2026-10-04 · Lemma E (§5.6e) and Proposition C (§5.6b, from `main`) are the
  same statement; Proposition P″ (§5.6b) shows the M-adic centres of a
  periodic pair coincide, so the M-adic coordinate alone excludes nothing.
  Do not re-derive either. · `p1b-vertex-coincidence-box-2026-10-02.md`
- 2026-10-04 · `L` (per-carrier least offset-zero depth, max 12) and `K_V`
  (per-vertex greatest first left-aligned depth, max 17) are different
  statistics; do not compare them as equals. ·
  `formal-productivity-reduction-2026-10-04.md` §6

- 2026-10-04 · SC_all holds on 408,798 specimens of total length ≤ 10 and on
  the 135,990 with images ≤ 4 (exact, 11 and 3 minutes); deepest residual pair
  level 15 on `0 -> 1, 1 -> 2, 2 -> 10` on every domain. With the recorded
  PPVC runs this gives PDS on 145,806 specimens; the catch-up-free specimens
  without a Barge witness are settled one by one, only a uniform argument is
  open. Lemma A: on the catch-up-free `|det M| = 2` class an unmerged aligned
  pair has no interior offset-zero child. · `strong-coincidence-census-2026-10-04.md`

- 2026-10-04 · The two cube-image certificates behind Propositions 5.46/5.47
  were executed in Mojo, not just cited: all 15 seed-patch-overlap tests pass
  and the receipts reproduce 1,142 vertices, first-coincidence depth `D = 19`
  and first left-aligned depth `K' = 17`. The stated state bounds
  `2 beta^19 ell_max = 45,136,797,534` and `2 beta^17 ell_max = 4,198,004,819`
  recompute exactly in 60-digit decimal, and both integer floors are right.
  Do not re-verify. · `kernel/tests/test_overlap_seed_patch.mojo`;
  `audit-2026-10-04.md` §B.3

- 2026-10-06 · All four retained real-secondary packet SCCs and both controls
  have acyclic nonzero-physical-cut induced graphs; coherent defined hub phase
  also survives on the non-Pisot strict support. Neither finite property
  distinguishes PIP or gives balanced alignment. ·
  `c4-ordered-hub-offset-negative-2026-10-06.md` §§2,5

- 2026-10-07 · Only 70 of the 383 PIP members of Theorem E's classes with
  `p, q, r <= 11` have the characteristic polynomial of a three-letter
  simple-Parry β-substitution, a necessary condition for conjugacy to one;
  the other 313 cannot inherit Barge (2018) that way, and the 70 are not
  shown conjugate. · `p1b-catch-up-free-ppvc-2026-10-07.md` §3; scratch check

- 2026-10-08 · Theorem Ω's box automaton is **not** a faster exact decider
  than `coincidence_level` on Theorem K's members: on the `s = −1` leaf
  `zy | yz`, 3.9 s against 0.05 s at (3, 3, 0), 105.6 s against 51.9 s at
  (9, 7, 0), and no verdict within 180 s at (7, 9, 1), which
  `coincidence_level` decides in 58 s; 27,000–65,000 box states already at
  `a, b <= 9`. Use it as a cross-check for its stronger FP verdict, not to
  speed up member decisions. · `audit-finite-regime-advice-2026-10-08.md`;
  `experiments/z2-route/boxtime.mojo`

## 6. Tooling pitfalls

- 2026-10-04 · `pkill -f PATTERN` inside a shell command whose own text
  contains PATTERN kills that command. Kill by PID from a separate command.
  (Hit again the same day: `pkill -f 'scratchpad/scc'` killed its own shell.)
- 2026-10-04 · `/usr/bin/time` is not installed in the cloud container; time
  runs with `date +%s` differences.
- 2026-10-04 · `cmd | tail -1 && next` tests `tail`'s status, not `cmd`'s:
  a failing governance audit then lets the commit through. Capture `$?`.
- 2026-10-04 · Editing a `require_contract` text makes the recorded receipts
  stale until `kernel/run_tests.sh` reruns; the coverage audit then fails
  locally (CI regenerates the receipts).
- 2026-10-04 · Prefer Mojo with `parallel_fold` to throwaway Python for any
  exact check; a Python-only computation is a defect under `AGENTS.md`.
- 2026-10-04 · Seeding the formal census from Proposition V's box takes 7
  minutes; the earlier `K_T` seeding took 107. Reuse the box graph.
- 2026-10-04 · Background jobs are capped at two hours; long oracle sweeps
  must be chunked or restricted to labelled samples.
- 2026-10-04 · The exact Python formal-overlap oracle is slow on specimens with
  two real contracting conjugates unless each `q(c)` is bounded tightly
  (binary search on exact signs): `1 5 20` takes 42 s, about 7 minutes before.
- 2026-10-04 · Estate layout on `main`: `mojo/` → `kernel/`, `scripts/` →
  `tools/` (Python censuses → `oracles/python/`), `src/psc_research` →
  `reference/psc_research`, `docs/evidence/` → `evidence/`, `tla/` →
  `proof/tla/`. A pixi env cannot be moved (absolute prefixes; `std` not
  found): keep `mojo/.pixi` and symlink `kernel/.pixi` to it, excluded in
  `.git/info/exclude`.
- 2026-10-04 · `p1b-vertex-coincidence-box-2026-10-02.md` §§5.6h–5.6i were
  §§5.6c–5.6d on `main`; the checksummed archive index still cites the old
  numbers. Do not edit the archive README (its `SHA256SUMS` covers it).

- 2026-10-04 · `tools/make_ledger.py` binds eleven generated claim surfaces to
  `WEEKLY = docs/completion-ledger-2026-09-14.md`, a frozen dated snapshot, so
  claims are validated against a superseded weekly ledger. Repointing `WEEKLY`
  to `completion-ledger-2026-10-02.md` is **not** a drop-in: the consistency
  check then fails on five anchors the newer snapshot does not carry
  (`ConcentrationAuxB`, `G1b2RenewalFiniteness` twice, `SpanRichProductivity`,
  and `OverlapProductivity` for want of a status label within 0 lines). Either
  give the new snapshot those anchors with status labels, or drop the WEEKLY
  bindings and rely on the live surfaces, which is arguably correct since a
  snapshot is not a proof source. Left at 09-14 deliberately rather than
  changing what eleven claims are checked against. · `tools/make_ledger.py`
  (`WEEKLY`); `audit-2026-10-04.md` §D.5
- 2026-10-05 · Vendored `madic_ball.mojo` (finite-math-kernels da41c27) now
  states that the generators of `M^k Z^n` are the *columns* of the row-major
  `M`; the row span is a different lattice. `psc/overlap_madic_filter.mojo`
  does not call `contains_exact` but solves `M^m x = d` with its own
  adjugate inverse of `qmat_pow(lift_square(incidence))`, where
  `incidence()[3*i + j]` counts letter `i` in `sigma(j)`; that is the column
  span, the one `d = M^m w` for Parikh vectors needs. Checked by reading the
  adjugate entry by entry; nothing changed. ·
  `kernel/finite_linear_algebra/madic_ball.mojo`;
  `kernel/psc/overlap_madic_filter.mojo` (`_inverse_lattice3`)
- 2026-10-05 · The vendoring checker moved to the vendored
  `tools/vendoring/check_vendored_sync.py`; the old `tools/check_vendored_sync.py`
  is gone. `CONTRIBUTING.md` (gate 7), `.github/` and `.forgejo/`
  `PULL_REQUEST_TEMPLATE.md` and `.claude/skills/steward/SKILL.md` still name the
  old path: they are rendered from `larsbx/agent-icm` and must be corrected
  there and re-rendered, not hand-edited here. Until then run the new path. ·
  `vendored.toml`; `tests/test_vendored_sync.py`
- 2026-10-05 · `mojo build kernel/pisot_polynomial_bench.mojo` needs `-I tests`
  as well as `-I .`: it imports `tests/polynomial_reference.mojo`. Without it
  the build fails to locate the module, before and after the re-vendor. ·
  `kernel/pisot_polynomial_bench.mojo` line 7
- 2026-10-06 · Python-oracle `_poly_gcd` can reuse exact immutable `Fraction`
  coefficients while retaining conversion for every other type, including
  subclasses: 4,800 gcd pairs and all 3,375 cubic screen results agree with
  `main@c2bd9a0`; median normalization time drops 0.477466 -> 0.031462 s,
  with a 6.4% full-screen gain on the shared-container run. Keep the exact-type
  guard and distinguish normalization-only from caller speedup. ·
  [poly-gcd-fraction-normalization-2026-10-06.md](poly-gcd-fraction-normalization-2026-10-06.md#benchmark-evidence)
  (source digests and replay in §Reproduce); `tests/test_pisot_screen.py`

- 2026-10-06 · `PacketGraph.expansions` has two entries per BPA state,
  indexed by `2*state_id + Int(sign == -1)`; indexing by state ID selects
  another state's factor row. The new ordered-hub golden regressions caught
  this during implementation before export. ·
  `kernel/psc/target_packets.mojo::_prepare`;
  `kernel/tests/test_packet_hub_analysis.mojo`

- 2026-10-06 · Claim coverage reads live passing receipts. Running governance
  or the full Python suite before `kernel/run_tests.sh` finishes can report
  uncovered claims from its incomplete receipt file. Complete the Mojo run
  first, then audit; the completed 60-file run and subsequent full checks pass.
  · `c4-ordered-hub-offset-negative-2026-10-06.md` §7

- 2026-10-06 · Cleanup decision: subtract unused Julia scaffolds, obsolete
  boundary-sync integration/task notes, the superseded architecture pointer,
  duplicate Python optimization advice and repeated workflow paths; the live
  automation protocol now follows the claim taxonomy and both proof routes. Ten
  remaining frozen-weekly status bindings now check the live proof ladder and
  roadmap, resolving the September 14 snapshot debt above; all 71 proof
  records and claim statuses stay unchanged. September 11/14 completion
  ledgers are preserved byte-for-byte at their new archive locators. ·
  `tools/make_ledger.py`;
  `archive/2026-10-06/status-snapshots/README.md`

- 2026-10-07 · `search_point` enumerates every value of a bounded domain, so
  on forms with large coefficients (the q-lift's tail-fixed forms) one node
  pushes thousands of boxes: 14 GB and an OOM kill. Pass `span_cap`.

- 2026-10-07 · `finite_linear_algebra.mat3.has_rational_root` evaluates `r^3`
  in unchecked `Int` for every divisor `r` of `det M`; safe at the audited
  column-sum bound 6 and at entries up to 64, not beyond. Any path that admits
  larger matrices must use `psc.pisot_screen.has_rational_root` (exact over
  `Q`, divisor pairs up to `sqrt |det|`), as `screened_perron_field3` now does.
  · `kernel/psc/perron_field3.mojo`

- 2026-10-07 · Run-position ranges in a symbolic overlap closure: the upper
  end is the largest `m` with `ell_A − t − m ell_y > 0`, which is (least `m`
  with `t + m ell_y − ell_A >= 0`) − 1, **non-strict**. Computing it with a
  strict inequality admits one invalid child exactly when `t + m ell_y = ell_A`
  identically, and on the class B line it produced 123 vertices (4 without a
  hit) instead of the exact 119. · `kernel/psc/symbolic_line.mojo` (`least_m`)

## 7. Review outcomes

- 2026-10-04 · Independent status audit (`audit-2026-10-04.md`) re-derived
  Propositions 5.46, 5.47 with Corollary 5, and Theorem B: all hold. Theorem
  B's realization does **not** breach the formal-recurrence firewall — it
  builds `Phi^r`-fixed tilings from *interior* occurrences, whose patches are
  allowed for `sigma`, and takes offset integrality from the cycle equation.
  The ledger's new set-of-sets `Requires` with existential discharge is sound
  and no route establishes anything from nothing. Two findings of that audit
  were self-corrected: the 2026-10-04 review *is* recorded (§7 here, not a
  standalone file), and `PDSImpliesRepoG1` *does* name its repository inputs
  in the record source, though they are not ledger nodes so the closure cannot
  track them. · `audit-2026-10-04.md` §§B, D.2, D.4
- 2026-10-04 · The four 2026-10-04 claims (`PDSImpliesRepoG1`,
  `PDSImpliesSeedwiseTermination`, `CoincidenceRankFibreTheorems`,
  `StrongCoincidenceFromPDS`) were on no prose status surface, so governance
  could not see drift on them; they now have rows in the claim/source map and,
  for the two repository claims, sections in the conjecture ledger and proof
  ladder. `PDS => G1` and the seedwise bridge were likewise absent from every
  headline surface and are now stated on README, the conjecture ledger, the
  proof ladder and the architecture note. · `tools/make_ledger.py` surfaces;
  `audit-2026-10-04.md` §D.3

  - *Correction 2026-10-05.* That list omitted
    `docs/research-roadmap-2026-09-21.md`, which the same audit counts as a
    headline status surface (§D.5) and which stayed synchronized only through
    2026-10-02. It now carries a 2026-10-05 synchronization block for both
    results, plus the planning consequence that by Corollary 5 the
    strict-zipper branch (#139) alone suffices for G1, so G1b-2 (P2) is the
    least load-bearing of the three routes. The dated
    `completion-ledger-2026-10-02.md` snapshot stays frozen by design. ·
    `audit-2026-10-04.md` §D.5 correction

- 2026-10-05 · **Theorem E proved**: on the catch-up-free `|det M| = 2` class,
  any two distinct letters fixed by the first-letter map are eventually
  coincident, so case (i) of #138's aligned template is eliminated on the whole
  class. Three things worth not rediscovering. (1) `p, q, r` sit only in the
  bottom row of `M`, so `det M`, `f(1)` and `f(-1)` are all **affine** in them,
  and `|det M| = 2` is a linear Diophantine condition that fixes one
  parameter. (2) The Pisot necessary conditions `f(1) < 0`, `f(-1) < 0`
  (Lemma P1) predict every line's PIP range *exactly* — e.g. B's line
  `(n, 0, 1)` has `f(-1) = n - 12`, which is why it stops at `n = 11` — so no
  witness lemma is needed on the lines, only on the 2-dimensional bulk. (3) The
  bulk falls to three explicit witness lemmas, each a one-step cancellation of
  a small Parikh discrepancy by offsets that differ by one inside the next
  blocks. The remainder is 27 explicit substitutions, all decided coincident
  at levels 3-7. · `p1a-a1-prime-2026-10-05.md` §3b;
  `kernel/tests/test_a1_normal_form.mojo`

- 2026-10-06 · Prefix transfer: `sigma^(n+1)(i)` begins with
  `sigma^n(h(i))`, so coincidence propagates *backwards* along the pair map
  `H({i,j}) = {h(i),h(j)}`, and all-pairs strong coincidence holds iff every
  `H`-cycle of distinct pairs contains a coincident pair. Do not re-derive the
  per-pair cases by search: on the catch-up-free `|det M| = 2`, `|O| = 2`
  class the `H`-cycles are a seven-row table, and only the swap family
  (`h` swaps the odd letters) is not closed by Theorem E, Lemma T,
  Barge–Diamond, or the two-lemma Proposition Y. Its sweep needs level-4
  witnesses on infinite lines (`(n+1,0,n)` in ending `(x,x,x,c)`), so Theorem
  E's level-2/3 lemma style will not suffice there. Reversal preserves `M` but
  not coincidence levels (swap ending `(x,c,x,x)` is class D reversed, with
  different levels). · `p1a-a1-prime-2026-10-05.md` §3c;
  `kernel/tests/test_a1_normal_form.mojo`

- 2026-10-06 · **Theorem H / Corollary H1 proved**: strong coincidence for
  every pair on the catch-up-free `|det M| = 2` two-odd-letter class. Worth
  not rediscovering: (1) *constant-offset* witness paths suffice — every
  `gamma_l` along the path is a parameter-free vector, so `M gamma` is affine
  and validity on a whole cone is affine identities plus coefficient-sign
  inequalities (`psc.cone_witness`); (2) with that, every bulk quadrant of the
  swap family is **one** cone, and the level-4 infinite lines are cones too —
  hand-found lemmas were the bottleneck, not the mathematics; (3) the search
  re-finds Theorem E's L_D with the lemma's own position `p + 3`, so the
  machinery should be tried first on any new linear-exponent family. It does
  not reach the `|O| = 1` sub-class as it stands: there the images `o w o`
  carry arbitrary two-letter words `w`, not one run. ·
  `p1a-a1-prime-2026-10-05.md` §3d;
  `kernel/tests/test_swap_family_certificate.mojo`;
  `p1a-swap-family-literature-gate-2026-10-06.md`

- 2026-10-06 · One odd letter needs no new machinery except in one row: the
  images are a non-`o` letter or `o w o`, so `h` is `o` on every long image and
  prefix transfer closes every pair unless `sigma(o)` is a single letter (or
  two images are short, which forces a letter 3-cycle and Barge–Diamond). None
  of the 18 one-odd-letter corpus specimens is in that row, so the open family
  of Theorem K has **no corpus member**; a census of it must be built from
  scratch, over patterns of runs in `w_1, w_2`. · `p1a-a1-prime-2026-10-05.md`
  §3e; `kernel/tests/test_swap_family_certificate.mojo`

- 2026-10-06 · Theorem K's family (`sigma(o) = y`, `o w_1 o`, `o w_2 o`):
  `det M = 2(Z_1 − Z_2)`, and every witness found starts
  `(o, y) -> (y, w_1[0], −e_o)`. When `w_1` begins with `z` the crossing of the
  Parikh walks of `w_1` and `w_2 + e_y` gives level 3 through the two final
  `o`s (Lemma Φ2), so only non-crossing pairs remain. **Do not retry the
  letter-by-letter pattern tree** on them: with opaque tails and relational
  splits its open leaves still grow (34, 237, 969, 4,083 at depths 6, 9, 11,
  13); the non-crossing witnesses depend on `delta = pi(w_1) − pi(w_2)`, so
  the next decomposition should split on `delta` and on the walk. ·
  `p1a-a1-prime-2026-10-05.md` §3f;
  `kernel/tests/test_odd_letter_family_certificate.mojo`

- 2026-10-06 · Delta split of Theorem K's family: `f(−1) = (1 + Z_2)(Y_2 − Y_1 − 1)`
  when `Z_1 = Z_2 + 1` and `f(1) = (Z_2 − 1)(Y_1 − Y_2 − 1)` when
  `Z_1 = Z_2 − 1` (exact), so the sign of `Y_1 − Y_2` is fixed by `s`. Most
  witnesses sit at **common points** of the walks of `w_1` and `w_2 + e_z`
  (`t = 1` always is one): a matched step needs a factor of Parikh `±delta`, an
  unmatched one a meeting of `w_2` with `w_1 + delta`. That closes
  `delta = e_z` (Theorem Φ) but leaves a growing residue elsewhere (87 at
  length 7, 265 at 8). The parametric cone search on residue run families
  works only with `Delta` fixed. Next: split on `Delta` together with
  relational run-length splits. · `p1a-a1-prime-2026-10-05.md` §3g;
  `kernel/tests/test_odd_letter_family_certificate.mojo`

- 2026-10-06 · Run-shape cover of Theorem K's residue: whole shape families
  close (Theorem Ψ; 29 cells at length 8) once three things are in place —
  exact `Delta` cells (with `Delta` free, `delta` is not constant), the
  quadratic Pisot forms `f(1) = Z_2(Delta − 1) − 2Y_2 − Delta − 3` /
  `f(−1) = Z_2(|Delta| − 1) − 2Y_1 − |Delta| + 3` as cuts (they kill the
  `Delta`-tails), and a **line mode** allowing offsets affine along
  `e_z − e_y` (some witnesses pass through `(b + 1)(e_z − e_y)`). Value
  splits alone just push an open region outward (`a >= 11`): when a cell
  will not close, look for a non-constant offset, not a deeper split.
  Many-run shapes still exceed a 600-region budget. Tooling: never
  `pkill -f` / `pgrep -f` a pattern that also appears in the running shell's
  own command line — it kills that shell (happened twice). ·
  `p1a-a1-prime-2026-10-05.md` §3h; `kernel/tests/test_odd_letter_family_certificate.mojo`

- 2026-10-06 · Induction on runs for Theorem K's residue: run patterns with
  an opaque tail close as whole infinite families (unboundedly many runs);
  over six `delta` cells 60 of 84 run-tree leaves close, and the cell
  `(s, Delta) = (+1, 1)` is settled up to `zyz* | zyz*`, `zyz* | yzy*`
  (Theorem Ξ). **Refining a doubly open pattern does not converge**: one
  revealed run moves the openness to the other word (open regions 104, 74,
  96, 44, 107 down the chain in cell `(+1, 1)`), so do not spend more budget
  or depth there. The residue is mostly **single excursions**: only common
  point `t = 1` (51 of 87 at length 7, 170 of 265 at 8). Next: a witness
  argument inside an excursion. Tooling: a scratch driver `kernel/_*.mojo`
  was once committed by mistake; check `git status` for it. ·
  `p1a-a1-prime-2026-10-05.md` §3i; `kernel/tests/test_odd_letter_family_certificate.mojo`

- 2026-10-06 · Excursion route for Theorem K's residue. **A lockstep
  one-counter reading is the wrong model**: the level-2 state is
  `(w_1[t], w_2[t−1], (1−h)(e_z−e_y))`, but closures compare the walks at a
  lag `c (Delta + s)` (`M(e_z − e_y) = −delta`). What works is **Lemma X**
  (monotone paths crossing at their endpoints meet; weak end allowed when a
  letter follows), which reads endpoints only and so crosses opaque tails,
  plus **Lemma Φ5′** (`s = −1`: `w_2` ends in an explicit suffix of length
  `2 − Delta` with two `z`). Ablations (exploratory): without the Φ5/Φ5′
  suffix the revealed runs a certificate needs grow with length (to 7 at
  30–40); without lagged cuts `s = −1` climbs to 5–6; extremum cuts of `h`
  are a marginal aid. With them (kernel `reveal_census`) the need is at most
  2 runs through length 10 exhaustively and at most 4 in seeded samples at
  lengths 40–60. **Blind splitting does
  not uniformize** the per-point certificates: open regions 44 → 533 → 994 as
  the budget grows 300 → 3,000 → 20,000, while every one of 11,664 tested
  points has an opaque-tail certificate. Next: a certificate-guided
  partition (lift a point certificate, carve its validity polyhedron). Do not
  spend more budget on relational/value splits. Tooling: `grep` without
  `--line-buffered` hides a long driver's progress until it exits. ·
  `p1a-a1-prime-2026-10-05.md` §3j; `p1a-excursion-route-literature-gate-2026-10-06.md`;
  `kernel/tests/test_odd_letter_family_certificate.mojo`

- 2026-10-06 · Certificate-guided partition (exact integer decomposition
  `impose_nonneg` + lifted base-point certificates) closes what blind
  splitting could not: Theorem Λ, the whole cell `(+1, 1)`. **Base points
  must be generic**: from the origin, certificates carve slices
  (`n_0 = 0`) and the cover peels one value at a time; with every variable 2,
  they exploit accidental equalities (`2 n_0 = n_3 + n_6`), and one carve split
  into 8,307 + 35,040 regions. Distinct primes `2, 3, 5, …` fixed both
  (`zyz* +y | yzy*`: 18,396 regions → 2,833). Drop duplicate carving forms.
  Tooling: never `pkill -f` a scratch binary; kill by the PID that `ps`
  lists. · `p1a-a1-prime-2026-10-05.md` §3k;
  `kernel/tests/test_odd_letter_family_certificate.mojo`

- 2026-10-06 · Regions that carry their own inequalities (`GuidedRegion`,
  `Prover` in `psc/cone_witness.mojo`) replace decomposition in the guided
  cover. Pitfalls met on the way, each now a regression: the verifiers' end
  tests asked the offset to be *identically* zero, which a carved region
  never makes it (they now ask the prover for `= 0` on the region); a form
  tightened by its gcd (`tighten`, Chvátal–Gomory, same integer points) is
  only re-provable with a multiplier (`f − 2 T >= 0`), so the prover reads
  multipliers off coefficient ratios; the base-point walk into a region
  overflowed `Int` and lifted a certificate at a garbage point (now capped,
  and a carve whose inside misses its own base point raises). Complements of
  carves are mostly *empty*, and often only through three assumptions at
  once; pairwise sums missed them and the raise-only walk found no point, so
  they were reported open (412 of them in `zyz* +y | yzy*`). Sums of up to
  three assumptions, integer bound propagation (`propagate_bounds`) and a
  local search on total violation took that pattern to 0 open (3,536
  regions). **Finite observation, not to repeat:** in the symbolic tail cell
  `s = +1`, `Delta = 1 + e`, point-wise McCormick quadrants do not converge:
  with `a_0 = 2, b_0 = b(p)` the base points climb `e ≈ 23, 701, 22397,
  716669` (×32 per step), and once points are walked into regions the cuts
  step `e` by one (slopes 23, 24, 25, …). For fixed `Z_2` the non-PIP set
  `(Z_2 − 1) e >= 2 Y_2 + 4` is a half-space, but over all `Z_2` it is not
  polyhedral, so finitely many cuts always leave wedges holding non-PIP
  points with `Z_2, e` both unbounded: a finite tail cover needs
  certificates valid on those non-PIP points too, not finer cuts.
  Certificate-before-cut (`cut_first = False`) does not converge at 5,000
  regions either (PIP-side base points reach `n ≈ 400`, beyond the offset
  bound). · `p1a-a1-prime-2026-10-05.md` §3k;
  `kernel/tests/test_odd_letter_family_certificate.mojo`

- 2026-10-06 · Theorem K's tail cells, what the obstruction is and is not.
  **Not the mathematics:** in a seeded sample (seed 1, 400 draws,
  `|w_2| <= 10`, `Delta <= 12`; `xlev`, scratch) of `s = +1` non-crossing
  members, every coincidence level is `<= 5`, and `<= 4` for `Delta >= 4`;
  members per `Delta` settle at about 63. Past a threshold depending on
  `(u, w_2)`, the shared tile's path is the same for every `Delta`, its
  `o`-side digit counted from the *end* of `y^Delta` (e.g. `zyzy y^Delta |
  zyy` at level 3 for all `Delta >= 2`), so the certificate is affine in
  `Delta`. **Not hidden Pisot constraints:** for `s = +1`, `f(1) < 0` is the
  whole Pisot condition (exact `pisot`, 5,680 of 5,680 points of
  `Y_2, Z_2 < 30`, `Delta < 30`), and 3,100 of them have `Z_2, Delta >= 2`.
  **It is the cover:** line mode works in fixed-`Delta` cells because
  `M (e_z − e_y) = (0, −Delta, −s)` is constant there; with `Delta = 1 + e`
  symbolic a variable line coefficient makes `M gamma` quadratic, which line
  mode refuses, and point-wise lifting from small-`e` base points carves
  `e`-bounded slices. Uniform McCormick corners `(k, 0)` cut `{Z_2 >= k,
  (k − 1) e >= 2 Y_2 + 4}` with no staircase but leave wedges. Also: the
  non-tail cells never fell back to a non-member base point (now they do),
  and carve complements were mostly empty (dropping implied forms and empty
  complements took `zyz* | yzy* +zzz` from 15,612 regions to 3,441). ·
  `p1a-a1-prime-2026-10-05.md` §3l.5; `kernel/odd_letter_family_certificate.mojo`
  (`search_point`, `mccormick_forms`, `_new_forms`)

- 2026-10-06 · Polynomial line mode (`psc/poly_line.mojo`) for the tail
  cells. Pitfall: lifting a point path by the *search's* candidate menu (run
  offsets anchored 0–2 from either end) found no candidate in all 15
  quadratic cases (s = +1 tail, 3,000 regions): states agreed, offsets did
  not. Building candidates from the point's own step (its offsets anchored at
  either end, or solved to hold a coordinate) gives polynomial certificates,
  some on a whole region uncarved. Open: most lifts end with an offset whose
  degree-2 part does not vanish, i.e. the certificate holds on a slice, which
  a finite cover cannot use. Also: the fixed cell `(+1, 2)` does not close
  (15 of 20 leaves, 8 revealed runs), so fixed `Delta` is not a way around
  the tail either. · `kernel/tests/test_poly_line.mojo`

- 2026-10-06 · Lifting is linear algebra once the segments are fixed: the
  letters are then determined and the end offset is linear in the run
  offsets, so "affine offsets with `gamma_L = 0` identically, agreeing with
  the point" is one exact system over Q (`solve_lift`). It answers
  definitively where candidate menus only fail to find: in `zyz +yy | zyz`
  (cell `(+1, 2)`, every run revealed) the base point's first path has
  **no** such offsets, while other paths at the same point do
  (`enumerate_point_paths`); open regions 2 → 1, one certificate covering a
  whole region uncarved. The remaining one is a boundary slice (`n4 = 0`)
  whose 40 enumerated point paths all fail; Lemma X closures are not yet
  solved linearly. · `kernel/psc/poly_line.mojo`; `kernel/tests/test_poly_line.mojo`

- 2026-10-06 · Two cover leaks, each closing `zyz +yy | zyz` (cell
  `(+1, 2)`, every run revealed: 2 open → 0, 81 regions → 51, 62 s → 4 s).
  (1) With `Delta` fixed, Lemma P1's form is *affine*, and the cover never
  split by it: it certified member base points and cut only at non-member
  points, so a region whose members are finite (here 3 points,
  `f = n3 + n5 − 1`) ran out of peels. Now `{f >= 0}` is cut once and the
  rest carries `f <= −1`. (2) A region whose assumptions pin every
  occurring variable is one substitution, but counted as live and never
  reached exact decision; propagated bounds with `lo = hi` are now
  substituted. Also: Lemma X closures solve linearly too
  (`solve_crossing_lift`). Tooling: an unset shell variable sent a build to
  `/olf20` and four logs to `~` (left for the user to delete; the safety
  check blocks the removal). · `kernel/odd_letter_family_certificate.mojo`
  (`_affine_pisot_form`, `_pin_fixed`); `kernel/psc/poly_line.mojo`

- 2026-10-06 · s = −1 tail cell, `zy* | zy* +[z*]` at 1,500–3,000 regions,
  never closing. The McCormick cut at corner `(2, b(p))` walks `b` down one
  unit per cut (69, 68, 67, …): 636 of 1,500 regions were cuts. Uniform
  corners `(k, 0)` did not help (1,001 cuts, 359 open), certificate-before-
  cut was worse (996 open). Descending from a feasible point to a member
  (coordinate descent on Lemma P1's `f`) cut the cuts to 63 but left 464
  regions with no certificate. Their base points have one y-run in the
  thousands (n2 = 2,134), forced by large constants that earlier cuts left
  in the region's inequalities, beyond the search's offset bound; smaller
  candidate points change nothing there. Not reached by point heuristics:
  the tail needs certificates (or cuts) that do not inherit those
  constants. · scratch `xt m`; `kernel/odd_letter_family_certificate.mojo`
  (`pisot_carve_forms`, `_descend_to_member`, `_base_candidates`)

- 2026-10-06 · Witness shapes of `s = +1` non-crossing members at large
  `Delta` (scratch census, digits read structurally: in `u` from its start,
  in `y^Delta` from its end, in `w_2` from its start). **Sampling pitfall:**
  rejection sampling repeats members; a "dominant" level-4 shape inside
  `y^Delta` (72% of 300 draws at every `Delta` in 6..20) is one family:
  its Parikh condition is `(M^4 − Delta M^3 − 3 M^2 + (Delta − 4) M − 2) e_y = 0`,
  i.e. `chi` divides that quartic, i.e. `w_2 = z`, `u = zz`. Counting
  *distinct* members (all with `|w_2| <= 6`, `Delta = 8`): 37 members, 15
  shapes, no shape a majority. The leading ones are uniform in `Delta` and
  affine in run lengths, e.g. `u = zzy^k z`, `w_2 = zy^k z` at level 3 with
  the `o`-side position `k − 1` from the end of `y^Delta`, which is the
  form `solve_lift` finds; so the tail's obstacle is the cover, not missing
  certificates. For `s = −1`, `Delta = −6`, `|w_1| <= 5`: Lemma P1 forces
  `Y_1 >= 4`, so all 28 members have `w_1 = zyyyy` and `w_2` = two `z` in
  `y^10`; 11 shapes, all level 4, reading `w_2`'s `z` by position from its
  end (the x-block), again affine. · scratch `shapes2.py`, `shapes3.py`

- 2026-10-06 · Tooling, measured: the guided cover's tail regions cost
  ~2 s each (300 regions: 9m51s), and neither the candidate search's
  degree, nor its node budget, nor string-keyed polynomials were the cause
  (each change: same 9m40s–10m13s, identical results). A stack sample with
  `gdb -p PID -batch -ex bt` showed it at once: exact RREF over `BigZ`
  rationals (a gcd per product) in the linear lift, on systems that are
  mostly inconsistent. Screening mod two primes below 2^31 first: 42 s,
  identical results. Sample before optimizing. · `kernel/psc/poly_line.mojo`
  (`_consistent_mod`)

- 2026-10-05 · Tooling: a test pinned an unscreened parameter tuple and the
  exact `coincidence_level` refused it ("the powered characteristic polynomial
  is reducible"). Screen before deciding; the refusal is the procedure failing
  closed correctly, not a bug. · `kernel/tests/test_a1_normal_form.mojo`

- 2026-10-05 · On the catch-up-free `|det M| = 2` class the surviving aligned
  template is an explicit normal form: the odd set of Proposition C is exactly
  the bad edge, `O = {x, c}`, so `sigma(x) = x y^p s_x`, `sigma(c) = c y^q s_c`,
  `sigma(y) = t y^r s_y` with the four endings in `{x, c}`. The lemma behind it
  is worth keeping: `|O| <= 2`, because all three letters odd forces every
  image to have length exactly two, hence every column sum 2, hence Perron root
  the rational number 2, contradicting irreducibility (checked independently:
  no nonnegative 3x3 matrix with all column sums 2 is PIP). Two consequences:
  the 18 catch-up-free corpus specimens with `|O| = 1` cannot carry case (i) of
  the template at all, and the alternating template forces `sigma(a) = b` or
  `sigma(b) = a` as a single even letter, landing in the §5.6g one-E-letter
  sub-class. · `p1a-a1-prime-2026-10-05.md` §3a

- 2026-10-05 · Exploratory sweep of that normal form at three budgets,
  `p, q, r <= 5`, `<= 8`, `<= 11`: 174, 420 and 766 PIP members with
  `|det M| = 2`, A1′ witnessed on **every** one, coincidence level at most 7
  throughout. The finding worth not recomputing: **the tail does not move.**
  The level-4 to level-7 counts are identical at all three budgets (8, 2, 2, 2)
  while only levels 2 and 3 grow, so the hard cases do not scale with the
  parameters. The 14 members of level >= 4 are the same 14 every time, form 7
  mirror pairs under `x <-> c`, and all have `p, q, r <= 3`; the deepest has
  `sigma(x) = xyc`, `sigma(c) = cx`, `sigma(y) = cyc` with its first shared
  tile at position 311. The method is cheap because equal Parikh prefixes have
  equal length, so the search is one pass with two integer counters. Not a
  verdict: a member outside the range is uncovered, and the cap column is
  reported separately (zero on all three). Now ported:
  `kernel/a1_normal_form_census.mojo` decides each member with the canonical
  exact `coincidence_level`, so a negative is a verdict and the driver raises
  on one, and it reproduces the probe cell for cell at bounds 5 and 8. The
  regression pins **two** bounds on purpose, so that the tail claim itself is
  guarded. The probe is kept as provenance with its output and digests. ·
  `p1a-a1-prime-2026-10-05.md` §3a; `kernel/tests/test_a1_normal_form.mojo`;
  `archive/2026-10-05/session-probes/`

- 2026-10-05 · A1′, the obligation Theorem C leaves, is the **residual** half
  of all-pairs strong coincidence: under its hypothesis `h^n(x) = x != c =
  h^n(c)` for every `n`, so the pair is never merged and its witness is
  strictly interior. So A1′ inherits the strong-coincidence census: **0
  failures on all 408,798 PIP specimens**, residual level at most 15. Worth not
  attempting: there is no sharper finite test, because A1′'s hypothesis
  presupposes a bad edge and no verified specimen has one — a specimen
  satisfying it non-vacuously would refute SC_all and PSC. ·
  `p1a-a1-prime-2026-10-05.md` §2

- 2026-10-05 · On the catch-up-free `|det M| = 2` class, **A1′ and T2 are the
  same statement**, so #138's aligned branch and #139's strict-zipper branch
  converge. Mechanism: Theorem C's template gives `h(x) = x`, `h(c) = c`, hence
  `h(x) != h(c)`, so Lemma A's contrapositive forbids any offset-zero child of
  `(x, c, 0)` other than its leftmost, which is itself; a coincidence must
  therefore arrive through a nonzero-offset return, and by Lemma P every such
  return is a simultaneous birth, which is T2's object. Covers all 210
  catch-up-free corpus members (all of determinant 2) and 570 of 654 at total
  length <= 8. · same §3

- 2026-10-05 · Why A1′ is not a corollary of the Barge-Diamond import, in one
  line to stop the question being reopened: BD Theorem 1 produces **one** of
  the `d(d-1)/2` pairs, and neither of its two cases can be aimed at a
  prescribed pair. For `d = 2` there is only one pair, which is exactly why the
  two-letter case is a theorem; for `d = 3` the two bad edges are left open and
  A1′ asks for the aimed version on one of them. · same §4

- 2026-10-05 · #138's aligned branch has **one** surviving obligation, not
  two. Theorem C: passing to `sigma^2` squares the first-letter map, a fixed
  bad edge is permuted by it so the square fixes the edge pointwise, and in the
  alternating-E template the square is the identity — so all three
  sub-templates become the case where both letters of a bad edge are
  `h`-fixed. Every hypothesis transfers (`sigma^2` is PIP because `beta^2` is
  still cubic; the good pair survives by raising the level; a `sigma^2`-child
  is a `sigma`-grandchild). Certificate: 36/36 viable endpoint/good-edge
  placements, with `h o h` fixing at least two letters always. The surviving
  statement in classical form: two distinct one-sided fixed points of a PIP
  substitution, anchored at a common point, share a tile. ·
  `p1a-template-collapse-2026-10-05.md`; `kernel/psc/hub_selector.mojo`

- 2026-10-05 · Stop/go on that surviving obligation: it is a **special case of
  the open ternary strong coincidence problem**, not a corollary of the
  Barge-Diamond import. BD 2002's Case 1 (maximality) produces two eventually
  coincident segments that start at the same point — exactly the aligned
  configuration — but the pair it hands over is whichever maximality gives, and
  the argument cannot be aimed at a prescribed pair; that is why `d >= 3` is
  open. Negative control worth keeping: eventual coincidence is stable under
  raising the level but is **not** transitive (two witnesses decompose
  `sigma^n(j)` at unrelated positions), so any proposed proof that would also
  give transitivity is wrong or is a major result. Also recorded:
  Akiyama-Gaehler-Lee settle PSC by exhaustive search for every three-letter
  substitution of incidence trace at most 2 — a finite-domain fact worth
  pairing with this repository's own trace condition
  (`kernel/psc/degree2_sieve.mojo`), not a mechanism. ·
  same note §4

- 2026-10-05 · Proposition LC verified exactly on the whole standing corpus:
  10,584 terminal leftmost cycles over 4,554 specimens, every one sign-constant
  and prefix-vs-interior, no capped box graph, no failed replay, longest
  `r = 39`; 10,128 cycle equations replayed over Z and 456 past the exact
  integer range, reported uncomputed. Two sharpened corollaries: terminal
  cycles come in **mirror pairs** of opposite sign, so their number is even
  (LC4 — the catch-up-free counts are 2, 4, 6, 8, 10, never odd); and a box
  graph with **no** terminal cycle has `Z(s) = ∅` for every seed, giving
  finiteness for that substitution by Proposition 5.47 (LC5), which covers
  1,794 of the 4,554. LC5 is a cheaper certificate, not a new finite-domain
  result — the Proposition V census already certifies the whole corpus — and
  it is one-directional and useless for the uniform statement, since all 210
  catch-up-free specimens have cycles. ·
  `p1b-leftmost-chain-periodic-pair-2026-10-05.md` §§8–8a;
  `kernel/leftmost_chain_census.mojo`

- 2026-10-05 · The leftmost child is a *function* on nonzero-offset vertices,
  so `CU` is the complement of the basins of its terminal cycles, and every
  such cycle is a prefix-vs-interior periodic pair with constant offset sign
  (Proposition LC). Worth not rederiving: the sign is preserved by every
  leftmost step, so the catching side's child index is always 0 and its letters
  follow the first-letter map `a -> sigma(a)[0]`; at most three letters are
  periodic for it, so the prefix side of every cycle is one of at most three
  tilings. This gives Lemma P back in one line. It does **not** give T1: the
  reachability half is still a pointwise hitting problem. ·
  `p1b-leftmost-chain-periodic-pair-2026-10-05.md`;
  `kernel/psc/leftmost_chain.mojo`

- 2026-10-05 · Stop/go on the leftmost-cycle route: Siegel-Thuswaldner's
  zero-expansion graph (Def. 5.1 of *Topological properties of Rauzy
  fractals*) is the same principle — a finite graph whose nodes all lie on
  infinite paths decides whether 0 lies in a tile — so claim no novelty for it.
  The decisive hypothesis boundary: their Proposition 5.2 is for primitive
  **unit** Pisot substitutions and its proof uses unimodularity at the step
  "`gamma_{l+1} ∈ pi(Z^n)` by the unimodularity of `M`", which is exactly the
  `M^{-1}`-integrality that Proposition LC(4) must carry explicitly as
  `ab(Q) ∈ (I - M^r) Z^A`. Their graphs are in the contracting representation
  and are not functional, so no sign invariant and no prefix-vs-interior
  dichotomy there. Geometric property (F) is the right dictionary entry for a
  resolved carry. · same note §5

- 2026-10-05 · Finite observation worth not recomputing: Tribonacci
  `0 -> 01, 1 -> 02, 2 -> 0` has **no** terminal leftmost cycle at all — every
  nonzero-offset vertex reaches a catch-up — which is the expected unimodular
  behaviour (Lemma P is void). The smallest witness in the other direction is
  `0 -> 1, 1 -> 12, 2 -> 022`, with two cycles of length `r = 1`,
  `ab(Q) = e_0` and `w_0 = (0, 1, -1)`; it is checkable by hand and is pinned.
  The catch-up-free `1 -> 22, 2 -> 012` specimen's cycles have `r = 15`, where
  `M^r` is already past the exact 64-bit integer range, so its offsets are
  reported as uncomputed rather than assumed. · `kernel/tests/test_leftmost_chain.mojo`

- 2026-10-05 · The closure behind `PDSImpliesRepoG1` tracked only the Barge
  import; its five repository inputs were named in the record `source` field
  but were not ledger nodes. Three are now nodes — `ReturnModuleFullRank`
  (Theorem R), `PeriodicPairOneFibre` (Proposition F) and
  `StrictZipperPeriodicPairForm` (Theorem B with Lemma C and Corollary B′) —
  and the closure stays complete. The trap worth not re-finding: manuscript
  Proposition 5.47 must **not** be added as a dependency, because the existing
  `G1HalfCoincidenceRoute` node bundles the half-coincidence bound with its
  open all-seed premise, so requiring it would make an unconditional
  implication read as conditional on an open gate. Splitting that node into
  premise and mechanism is the only way to model 5.47's role, and it was not
  attempted here. · `tools/make_ledger.py`; `audit-2026-10-04.md` §D.4
  resolution

- 2026-10-05 · The three manuscript statements tagged
  `\Status{Theorem}, conditional only on its hypothesis` (Theorem 5.38,
  Propositions 5.46/5.47) now read `\Status{Conditional}` with the open
  hypothesis named. Carried as audit debt since 2026-09-20; it was always only
  a taxonomy inconsistency, since every generated surface already classified
  them as conditional. · `audit-2026-09-20.md` §5, `audit-2026-09-27.md` §G.1,
  `audit-2026-10-04.md` §D.6

- 2026-10-05 · Tooling pitfall: `claim_governance`'s promotion check reads a
  proving phrase within 120 characters of any claim alias, and its
  `negating_context` list does not contain "none". A section-closing
  disclaimer of the form "None of the above is proved" therefore *triggers* a
  promotion finding against a claim name a few lines above it. Write the
  disclaimer without a proving phrase ("nothing here discharges an open
  premise; X remains open") rather than relying on the negation list. ·
  `tools/claim_governance/checks/promotion.py`, `claim_governance.toml`
  `[promotion]`

- 2026-10-04 · Independent adversarial audit (no counterexample found) of
  Lemma C, Theorem B, Corollary B′, Proposition F, Theorem R, Proposition V,
  Theorem S, the mass lemma, Lemmas E, VT, B, the Barge-class lever,
  Proposition FP, Corollary FP′ and the region argument. All hold as
  corrected; fifteen findings applied in the notes (dated corrections). The
  one open item: the hypotheses of the imports behind Theorem S (Barge 2013
  Thm 4(5),(6); Barge 2015 item (3)) are recorded but not audited in any gate.
  Do not cite "Barge 2013 Thm 4(3)" (not recorded) or BK Lemma 5.12 for
  "no common tile ⇒ cr ≥ 2" (wrong direction). Theorem S implies "PDS ⇒ G1 for
  the all-seed automaton", which manuscript Open Problem 4.24 declines to
  assert; flag it at review. · `p1b-vertex-coincidence-box-2026-10-02.md`
  §5.1, §7; `p1b-strict-zipper-periodic-pair-2026-10-02.md`;
  `p1b-periodic-pair-fibre-literature-gate-2026-10-02.md` §6
- 2026-10-04 · The Theorem S import gap is closed: Barge 2013 Thm 4 (Pisot
  family) and Barge 2015 §1 items (2)–(3) (primitive, non-periodic, Pisot
  inflation) assume neither unimodularity nor irreducibility, so every PIP
  substitution qualifies. Do not re-audit. ·
  `coincidence-rank-imports-literature-gate-2026-10-04.md`
- 2026-10-04 · `PDSImpliesRepoG1` promoted to repository-proved (Theorem S
  route; audited; human review pending) and manuscript Proposition
  `prop:PDS-implies-G1` added; the coincidence half of Open Problem 4.24
  stays open. · `tools/make_ledger.py`; manuscript §4.8
- 2026-10-04 · Pre-existing false positive on `main`: `tools/audit_manuscript.py`
  flags `docs/psc-motivation-2026-10-02.md:58`, where "PSC is closed" appears
  in a list of formulations to *avoid*. Not caused by this branch. ·
  `tools/audit_manuscript.py` (psc-closed-premise rule)
  *Fixed 2026-10-04:* the rule now reads a Markdown list together with its
  colon-terminated lead-in paragraph and accepts "avoid" as negation; an
  affirmative list ("Results:" / "- PSC is closed.") still fails. ·
  `tests/test_audit_manuscript.py`
- 2026-10-04 · Former manuscript Open Problem 4.24 answered in full: pure
  discrete spectrum gives termination with coincidence from every seed,
  legal or not (Theorem `thm:seedwise`; ledger `PDSImpliesSeedwiseTermination`,
  with imported `StrongCoincidenceFromPDS`). Dated notes that still call 4.24
  open (`audit-2026-09-20.md`, `bsw-import-literature-gate-2026-09-21.md`,
  `overlap-finiteness-and-coincidence-density-2026-09-13.md`) are history, not
  status. · manuscript §4.8; `formal-productivity-reduction-2026-10-04.md`

- 2026-10-05 · Vendoring review caught shared machine-integer and governance
  defects beyond green consumer CI. FMK #63 repairs checked products and
  signed-minimum GCD refusal, exact support-based primitivity, alternative-route
  closure and executable-source coverage. All twelve packages now match landed
  commit `360bc90c27893900d30718e42d61d14ce255e530`; the boundary-synchronization
  wrapper propagates upstream refusal. ·
  <https://github.com/larsbx/finite-math-kernels/pull/63>; `vendored.toml`;
  `kernel/psc/boundary_sync.mojo`
- 2026-10-06 · PSC's substitution application and powers now come from the
  vendored `Substitution.apply` / `apply_n`: the second `apply_substitution`
  in `oa_overlap_types` and `one_tile._power` are deleted, and
  `legal_tower.apply_substitution_n` and `dumont_thomas.power_substitution`
  delegate. The alphabet-generic callers keep the trusted (unvalidated)
  constructor; the alphabet-3 callers keep `bpa.sigma3`'s abort, at depth 0
  still unconsulted. `periodic_pair._image` stays: its word cap refuses
  mid-construction, which `apply_n` cannot. Claim receipts and the full Mojo
  test log are byte-identical before and after. · `kernel/psc/legal_tower.mojo`;
  `kernel/run_tests.sh`
- 2026-10-06 · `pisot.is_primitive(Mat3)` now delegates to the vendored
  `integer_matrix.is_primitive` (Boolean support powers). The old body
  multiplied real powers `M^1..M^5` with unchecked `Mat3.__mul__`, so a
  matrix with entries large enough to wrap could be misjudged; on every
  matrix whose fifth power fits a machine integer (all incidence matrices
  here) the verdicts agree, as `test_boundary_sync` already pinned. The
  vendored test raises only on a dimension mismatch, impossible for a
  `Mat3`, so the view aborts there. `periodic_pair._checked_mat_mul` is
  replaced by the checked `integer_matrix.matmul`: it raises exactly when
  the old one did, though in a contrived case with two overflowing entries
  the message may name addition where the old named multiplication, or the
  reverse (loop order i,k,j against i,j,k). · `kernel/psc/pisot.mojo`;
  `kernel/psc/periodic_pair.mojo`
- 2026-10-06 · The 2026-10-04 session-probe replay pointed `MOJO_DIR` at the
  retired `mojo/`; repointed to `kernel/`. All five Mojo probes compile
  unchanged against the current APIs and reproduce the archived results
  (vc_try radii 29,17,18 / 61,337 states / 716 recurrent; closure 276 + 72;
  diagonal 1,080,828 / 1,153,308 of 1,154,040, 180/30; direct 4170 of 4344,
  29,712 vertices), compared against the README index (the archived
  `rerun_*.out` files were never committed; the fresh ones carry new
  timings and were not written back). ·
  `archive/2026-10-04/session-probes/probes/rerun.sh`
- 2026-10-06 · `psc.real_root_sign` now builds its Tarski query on the
  vendored `qpoly` (`normalize`, `derivative`, `mul`, `remainder`, `neg`,
  `evaluate`, `variation_difference`); its `poly_trim`, `poly_deriv`,
  `poly_mul` and `poly_rem` are deleted. `tarski_query`, `count_real_roots`,
  `isolate_real_roots` and `sign_at_isolated_root` stay: `qpoly` has no Tarski
  query and isolates only the largest root. One semantic difference: the old
  helpers raised on a rejected rational, `qpoly` aborts (via `q_is_zero`), so
  `tarski_query` now checks its inputs are accepted and raises first; accepted
  rationals stay accepted under every operation used. Runtime unchanged:
  13,530 `sign_at_isolated_root` calls take 15.7 s on each side;
  `overlap_contracting_census` 615/615 s before, 647/614 s after;
  `vertex_coincidence_census` 791/647 s before, 855/700 s after (run-to-run
  noise is about 20%), output byte-identical. · `kernel/psc/real_root_sign.mojo`;
  `kernel/tests/test_overlap_contracting.mojo`
- 2026-10-06 · `psc.pisot` and `psc.pisot_screen` take the derivative,
  negation, gcd and Cauchy root bound from the vendored `qpoly`;
  `poly_derivative`, `cauchy_bound` (`3 + max floor|p_k/p_n|`, a looser
  bound than `qpoly.root_bound`'s `1 + max |p_k|/|p_n|`; only ever an
  enclosing interval, so no count changes), `pisot_screen.poly_gcd` and
  `int_cauchy_bound` are deleted. Kept local after measurement: `poly_eval`
  (unrolled; `qpoly.evaluate` is the reference algorithm, about 15% slower
  in `pisot_polynomial_bench`), `poly_degree` (`qpoly.degree` copies),
  `poly_rem` (keeps length, returns the dividend for a zero divisor where
  `qpoly.remainder` aborts; `test_pisot_polynomials` pins it) and
  `sturm_chain` of `p` itself: `qpoly.sturm_chain` passes to the squarefree
  part first, and an all-`qpoly` `is_pisot_charpoly` ran about 17% slower on
  the 3,375 monic cubics with `|c_i| <= 7`. The two chains differ only for
  non-squarefree `p` with a root at a count endpoint, outside Sturm's
  hypothesis: the plain chain gives `-1` on `(-1, 1]` for `(x - 1)(x + 1)^2`.
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

2026-10-14 — Ω/G1 continuation: complete-box offset-zero reachability,
all-potential-overlap offset-zero reachability and cycle boundary hitting
are equivalent by Ω1 finite descent. Their direct G1 sufficiency uses
Proposition 4, without SC_all, leftmost-cycle exclusion or spectral imports.
Derived all-level symbolic bound: `2 L^(K+2)`, with `K` the maximum
all-seed first-half-coincidence depth; box recurrent depth cannot replace
it. This assembles existing implications and does not discharge universal
hitting or promote G1/PSC. Human review remains non-blocking validation
debt. Evidence: `docs/bpa-termination-by-overlap-depth-2026-10-02.md` §7;
`docs/research-roadmap-2026-09-21.md`, October 14 synchronization.

2026-10-14 — Exact class-D residual cover: below `r=q-1`, each
determinant-two branch is a complete unimodular quadrant. For `p=q+s`,
`a=q-r-2`, `b=3r-2q+2s+2` are nonnegative exactly on the residual PIP
region; `chi(-1)=-b-1`. The infinite `b=0` edge is the nearest Pisot
boundary and cannot be omitted from a core certificate. This is parameter
coverage, not a hitting certificate; no sampled grid or class-level closure
is claimed. Evidence: `docs/p1b-boundary-hitting-progress-2026-10-08.md`
§4d; updated `docs/proof-ladder.md` and live roadmap §12.

2026-10-14 — **Correction/refinement of 2026-10-13 Nakaishi source audit (do not delete the earlier entry).** The exact §12/§13 measure identity is `sum_{k=1}^j m(tau2(x,omega)=N_k on Z) = s_j - m(E0) + m(E0 intersect H_j)` with `E0 = {omega in Z: T^N0 omega in C}`, `H_j = union_{k=1}^j {omega in Z: T^Nk omega in C}`. Since `m(E0)=alpha^(-L)m(Z)>0` and joint recurrence on the paper's selected fibre gives `m(E0 intersect H_j) -> m(E0)`, the purported contradiction with Proposition 4 reduces to an identity; no proof of universal tiling/PDS follows from this step. Stop direct import of the weak-mixing-to-cancellation step; independent algebraic control of *early-only then joint* returns is the missing repair. This does not refute PSC or disqualify other source lemmas. Evidence: `docs/nakaishi-2024-first-entry-audit-2026-10-13.md` section 'Exact corrected stopping-time partition (2026-10-14 continuation)', arXiv:2401.07771v1 §§12–13, equations (23)–(25),(29), Propositions 4–5.

2026-10-14 — Mixing-SFT negative control and Theorem 3 transfer gate: reconciled the distinct original #261 countercalibration with main's corrected stopping-time partition. In the primitive full two-shift with C=[11], Z=[1], x=0(110)^infinity, the exact conditional H_j masses are 1/4, 7/16, 37/64 for j=1,2,3 while the defective early-subtracted formula gives 0,1/8,7/32; all 4,32,256 finite tails were independently recounted. Under actual source hypotheses the intersection term tends to m(E0), and conditioning on Z minus E0 changes both limits equally. A valid replacement via source Theorem 3 needs (i) positive-measure algebraic nonvanishing support, (ii) O_(d+1) shrinking-scale membership at the same joint times, and for PSC #139 (iii) a realized occurrence-labelled affine target witness. No such bridges are proved; the full-shift control is not a Pisot-substitution counterexample and general PSC stays open. Evidence: docs/nakaishi-2024-first-entry-audit-2026-10-13.md section 'Additional independent calibration and repair criterion', arXiv:2401.07771v1 §§8–13, Definition 9, Theorem 3, Proposition 5; original pre-reconciliation PR #261 preserved at archive/pr261-before-main-reconciliation-2026-10-14.

2026-10-14 — Nakaishi Theorem 3 radius/source mismatch and exact-diagonal salvage. In arXiv:2401.07771v1 PDF p.16 Definition 9, the Archimedean radius of O_(d+1) contains c^(1/d), while the proof (p.17 Eq.16 and p.18) requires c^(1/(n−1)), c=(1−alpha^(−1))/M in (0,1). At times d>=n the printed tube is strictly larger; O_1 has undefined exponent. No direct import of Theorem 3 as printed. Corrected-tube/zero-distance pointwise use is conditional on the source's Garsia and tail estimates, and yields the integral certificate sum_(k<d) M^k(pi(p_k)−pi(q_k))=w from a *synchronized exact-diagonal* pair by irreducible spectral injectivity. This yields unscaled ancestor-prefix equality, not automatically #139's M^d w_PSC equality; the special cylinder enforces same ancestor, and exact Fibonacci/Tribonacci fixtures guard scaling and word order. Scale-matched shrinking-target limsup lies in the exact diagonal; weak mixing alone cannot supply infinitely many such hits off it. The open bridge is a realized occurrence-labelled affine-offset transport (or an independent proof avoiding Nakaishi). Source/evidence: docs/nakaishi-2024-first-entry-audit-2026-10-13.md, section 'Theorem 3 radius and pointwise address audit (2026-10-14 continuation)', arXiv:2401.07771v1 §§9–13, Definition 8–9, Theorem 3, Eq.16; docs/p1b-adelic-prefix-difference-cylinder-2026-09-21.md. No universal claim promotion.

2026-10-14 — Nakaishi reverse-address affine transport: in the repo's forward child-offset convention, reversing a legal source depth-d ancestry gives u_d=M^d u−W_d, W_d=sum_(k<d) M^k(pi(p_k)−pi(q_k)); exact source polynomial cancellation W_d=w_src is not the fixed-PSC boundary hit unless w_src=M^d w_PSC and the ordered occurrence chain is actually realized. For the genuine non-unit PIP substitution a->aaab, b->ab (M=[[3,1],[1,1]], charpoly X^2−4X+2, det=2), legal source SFT pairs with one second-a prefix at level d−1 and identical empty-prefix tails from d onward lie on the exact full-adelic diagonal and synchronously revisit the special cylinder for every t>=d, yet their fixed displacement w_src=M^(d−1)e_a is outside M^t Z^2 for every t>=d (M^(-1)e_a=(1/2,−1/2)). This rules out arbitrary source-diagonal-to-integral-PSC-offset transport, NOT a transport lemma under extra realized tiling/overlap conditions or PSC itself. Needed next: a geometric source-to-overlap realization bridge that forces the correct M-adic residue and *prescribed* fixed offset, plus legal occurrence/endpoint replay. Evidence: docs/nakaishi-2024-first-entry-audit-2026-10-13.md 'Exact reverse-address affine transport and a non-unit obstruction'; docs/p1b-adelic-prefix-difference-cylinder-2026-09-21.md §7 control 5; arXiv:2401.07771v1 §§3,6,9–10. All universal PSC/G1/#84/#138/#139 claims remain OPEN.

2026-10-12 — Mercat–Akiyama (arXiv:1810.03500v1) provides a unit-Pisot interior-language/PDS equivalence and effective automata construction (Thms 3.3/5.12, Cor. 5.14), plus already-proved ordered families and an everywhere-directive S-adic positive example. A zero-language automaton (Thm 5.21) does not extend the spectral equivalence to non-units. Redirect prospective #139 connection to a unit-only occurrence-preserving calibration before any adelic extension; no new PSC or PDS claim. Gate: `docs/mercat-akiyama-interior-language-gate-2026-10-12.md`.

2026-10-14 — PR #254 integration after #253: preserve all current-main ledger
entries and both distinct salvage results. Clarify that the conditional K2
argument counts child occurrences with multiplicity and retains raw-pair
orientation signs; for complex conjugates its dominant real subspace is a
plane. The finite-closure hypothesis remains open and the predecessor
contraction remains retired. Regenerate the proof inventory without changing
claim statuses or named Lean proofs. Evidence:
`docs/k2-load-bearing-scc-salvage-2026-10-11.md`,
`tests/test_defect_intertwiner.py`, `tests/test_boxwalk_radius_probe_oracle.py`.

2026-10-15 — Nakaishi-to-PSC realized-ancestry shortcut refuted in a seed-patch overlap (stronger than the previous SFT-only negative control). For sigma(a)=aaab, sigma(b)=ab, beta=2+sqrt(2), lengths ell=(1,sqrt(2)-1), the initial ab/ba swapped patches contain an interior (a,a,e_b) overlap S. The ordered child pair (top second a, bottom first a) maps S to itself exactly because M e_b-e_a=e_b, so it is a realizable recurrent nonzero-offset path of arbitrary duration. Along r repetitions W_r=sum_(k<r) M^k e_a=(M^r-I)e_b and W_r is outside M^r Z^2 since e_b is outside M Z^2 by parity. Yet S is productive: top third a / bottom first a maps it to T=(a,a,-e_a+e_b), and top first a / bottom third a maps T to coincidence (a,a,0); all overlap interiors are exact from 0<sqrt(2)-1<1. This *does not* exhibit a closed bad SCC or refute PSC. A proof must use the all-children, child-closed nonproductive hypothesis (and the exact orientation/offset) rather than realization plus an arbitrarily chosen recurrent path. Existing M-adic valuation-ascent failures and affine-pump negative controls remain in force; this one specifically audits the Nakaishi realization-transfer shortcut. Evidence: docs/nakaishi-2024-first-entry-audit-2026-10-13.md (2026-10-15 realized loop); docs/p1b-adelic-prefix-difference-cylinder-2026-09-21.md negative control 6; docs/research-roadmap-2026-09-21.md live P1b boundary.

2026-10-15 — Infinite ternary non-unit PIP good-edge family: for every k>=3 and 2<=h<=k, sigma(a)=a^k b c^h, sigma(b)=ab, sigma(c)=a has M=[[k,1,1],[1,1,0],[h,0,0]], det=-h and irreducible Pisot cubic X^3-(k+1)X^2+(k-1-h)X+h (root brackets (-1,0),(0,1),(k,k+2), with k+1 not a root). The actual swap-seed overlap S=(a,a,e_b) self-loops under top second a/bottom first a, giving W_t=(M^t-I)e_b outside M^t Z^3 for every t>=2 because M^-1 e_b=e_b-e_c but M^-2 e_b is nonintegral. Yet a DIFFERENT labelled child pair (top first c, bottom last a) reaches (c,a,0) at depth one and the common first a/a child reaches tile coincidence (a,a,0) at depth two, uniformly in both parameters. This is a scoped one-vertex constructive family theorem plus an infinite bad-path/good-exit calibration, not a closed nonproductive SCC, not universal BH/PDS and not a novelty claim for general pump failures. Scratch exact SymPy matrix/root-sign calibration passed at (k,h)=(3,2),(4,2),(4,3),(6,5),(8,8), with 2<=t<10 residue checks; the full family follows the displayed symbolic proof. Larger k/h exceed the audited Mojo cubic screen's length-six input precondition and must not be sent through it unchanged. Evidence: docs/nakaishi-2024-first-entry-audit-2026-10-13.md (infinite ternary family); docs/p1b-adelic-prefix-difference-cylinder-2026-09-21.md negative control 7; live P1b roadmap. #139/#84/#138/G1/PSC remain open.

2026-10-16 — Correction to 2026-10-15 ternary good-exit family: The local exact one-vertex self-loop / two-step good-exit theorem remains valid, but **the entire family is already PDS by prior art**. All substitutions a->a^k b c^h, b->ab, c->a (k>=3, 2<=h<=k) begin with a and have distinct terminal letters c,b,a. Word reversal is therefore injective on initial letters and constant on final letters; primitivity/irreducible Pisot and nonperiodicity transfer. Barge, DCDS-A 36 (2016), Theorem 3.13 (arXiv:1403.7826) yields flow PDS with no unit restriction, and mirror conjugacy preserves it. For the substitutive Z-action the *existing* imported Sirvent–Solomyak 2002 Corollary 5.2 supplies flow-to-symbolic transfer on irreducible Pisot substitutions. This prior-art route is already governed by BargeClassFlowPDS and BargeClassSymbolicPDS and tested by psc.barge_class. The October 15 result is a nonresolving-selected-path vs productive-alternative-child calibration, NOT novel family PSC/PDS coverage; no universal #139 or depth bound follows. Do not spend the next cycle trying to close PDS for this mirror-Barge family; move to non-Barge residual classes. A new exact Mojo test checks the direct mirror-class witness for (k,h)=(3,2) and (6,5), without screening the latter's oversized image through the cubic legacy classifier. Evidence: docs/nakaishi-2024-first-entry-audit-2026-10-13.md October 16 correction, docs/sadic-transfer-literature-gate-2026-10-11.md §§2–3, kernel/tests/test_barge_class.mojo. Append-only correction; retain 2026-10-15 research record; general PSC/#84/#138/#139 remain OPEN.

2026-10-16 — **Audit-priority attainment checkpoint.** For the box-walk/extremal audit (#253), exact `R*(3,4)` and extremizer structure remain **not obtained** (bounded depth-nine, complex-secondary `L=3` aligned-cut negative control only). For the K2 salvage (#254), finite reachable closure / bounded-K2 substitute / a closure-free truncation theorem remain **not obtained**; the load-bearing SCC spectral conclusion is conditional. For the matched-origin/path-lifting audit (#269), exact target semantics and finite occurrence-aware target-packet Mojo receipts already exist, but a complete sound lift/closure/coverage theorem for the proposed box-walk and universal productive SCCs is **not obtained**; finite diagnostic progress is partial. New PR #270 supplies a distinct *single-vertex* uniform two-parameter family good exit, not all-children closure. These are degrees of **the stated mathematical priorities**, not of audit-document merge completion; no PSC/G1/#84/#138/#139 status changes. Evidence: `docs/audit-priority-attainment-register-2026-10-16.md` (priority quotations, scoped attainment, blockers, next receipts).

2026-10-16 — Class-D Barge power/rotation stop theorem: for every p,q,r>=0, the substitution x->x y^p c, c->c y^q x, y->c y^r c has first-letter map f=(x,c,c) with f^n=f for all n>=1, and last-letter map g=(c,x,c), g^n=(c,x,c) for odd n and (x,c,x) for even n. All powers have two distinct first letters (x,c), two distinct last letters (c,x or x,c), and noninjectivity at both ends; thus no power belongs to Barge's initial-injective/final-constant class or its mirror. Every power has zero common-prefix AND common-suffix length, so the repository's allowed maximal common-word rotations cannot change this. The negative result is uniform across class-D determinant-two PIP residual quadrants, including both pending b=0 boundaries and b>0 interiors; it rules out only this imported theorem route, not arbitrary conjugacies, PSC, #139, or the pending class-D certificates of PRs #263/#266. The proof is exact endpoint algebra, with a new canonical Mojo regression on sample powers 1..3, not a depth-limited claim. Contrast PR #271's already-PDS direct mirror-Barge ternary family. Evidence: docs/p1b-class-d-barge-power-rotation-stop-2026-10-16.md, kernel/tests/test_barge_class.mojo, docs/sadic-transfer-literature-gate-2026-10-11.md. Next: finish occurrence-labelled boundary coverage rather than repeat Barge witness searches.

2026-10-16 — Class-D certificate reconciliation (PRs #263/#266): integrated the *distinct* b=0 evidence contracts without overwriting sealed packets or later main research. PR #263's complete occurrence-aware directed-support templates certify (as scoped execution-backed candidates) the minus boundary p=3a+5,q=3a+6,r=2a+4 for a>=4, 145 vertices/781 edges/max offset-zero depth 4 and finite a=0..3, and the plus boundary p=3a+3,q=3a+2,r=2a for a>=7, 718 vertices/4326 edges/max depth 6 and finite a=0..6. PR #266's independent 145-row upper-cover/selected-occurrence spine handles the minus line already from a>=2: 6 offset-zero targets, 139 affine whole-image selected child paths, exact rank descent <=4, 18779 exhaustively classified symbolic child candidates. Full directed support differs at a=2 (779 edges) from a>=3 (781 edges), so it must NOT be treated as a constant graph from a=2. Reconciliation preserved both sources/evidence as originally sealed; verified independent spine's 145 labels, ranks and 139 selected child edges against full support at a>=4, plus independent exact integer replay of all 139 chosen occurrences at a=2,3,4,8,12 (695 checks, zero discrepancies). The exact residual PIP parameter inversion is s=p-q=±1, d=q-r>=2, a=d-2>=0,b=r-2d+2s+2>=0; the two boundary lines cover b=0 only. Previously certified W1 handles r>=q-1. **Both b>=1 quadrants remain OPEN and neither PR proves full class-D PDS/G1 or general PSC**. Integration-head Mojo, provenance, policy and generated proof-bank checks still need completion; earlier green PR263 receipts and failed historical PR266 CI are not equivalent to a green integrated head. Evidence: docs/p1b-boundary-hitting-progress-2026-10-08.md §§4e–4m; evidence/class-d-minus-template-2026-10-14/, class-d-plus-template-2026-10-14/, class-d-target-spine-2026-10-14/; tests/test_class_d_certificate_agreement.py; original #263/#266 branches. No claim status promotion.

2026-10-16 — **Positive-b literal-spine-transfer no-go.** On the minus class-D residual, increasing the positive-b parameter by one changes the incidence matrix by the rank-one integer update e_y(1,1,1). For an offset w, the child under an unchanged occurrence pair therefore changes by (sum w) e_y unless the chosen prefix occurrences themselves move with b. The sealed minus b=0 145-row target-aware spine contains the nonzero-rank state (c,y,−2,4,−3) choosing FIRST/FIRST indices on both sides. Since sum w=−1 and both prefixes remain zero, its selected child shifts by −b e_y at b>0 and cannot remain the same fixed target. This is an all-b *algebraic failure of that literal edge transport*, not a claim that the state is geometrically reachable on every interior member or that BH fails there. Thus 139 affine a-only edges must not be relabeled a two-parameter theorem; a valid interior proof must track b-sensitive occurrence indices and provide all-child cover and descending paths. Evidence: docs/p1b-boundary-hitting-progress-2026-10-08.md §4m and tests/test_class_d_certificate_agreement.py. Both b>=1 quadrants remain OPEN.

2026-10-16 — Reconciled #267/#275 as alternative integer-Horner rational-root optimizations, with canonical BigZ Mojo, exact Python subclass fallback, deterministic equivalence and paired benchmarks against main@f6e181d. Python cubic root checks measured 3.29× (not a reproduced universal sixfold claim); full screen control 1.01×. The original Mojo signed abs(Int.MIN) skips divisors and gives a false negative for [-2^63,1]; unsigned magnitude/quotient bounds now avoid this and d*d overflow, with a direct witness regression. The 2024 dates and broad speed claims in both proposed .jules/bolt.md files are unverified and are not imported. Tooling lesson: exclude disposable scratch scripts but retain intentional reproducible benchmarks; no parallel ledger. Evidence: docs/rational-root-optimization-2026-10-16.md, tests/test_rational_root.py, kernel/tests/test_rational_root.mojo, evidence/rational-root-2026-10-16/.

2026-10-16 — Consolidation validation also reproduced main@f6e181d's unrelated class-D agreement-test failure: full_oracle.report() emits tuple vertices but the stored JSON loads list vertices. Normalize only the test's generated report through JSON before exact equality; the oracle, certificate bytes and mathematical assertions are unchanged. The same main had one missing generated proof-bank opening from #276; tools/make_proof_bank.py restores it. Evidence: tests/test_class_d_certificate_agreement.py and regenerated docs/proof-bank.md/proof/proof-bank.json.

2026-10-16 — Correction to the initial #267/#275 consolidation above: #278 review found immediate complementary-divisor visits can regress high-degree small-root inputs (x-2)(x^(n-1)-2520) by creating huge intermediates at ±5040 before reaching root 2. Retain ascending Python divisors; canonical Mojo defers complements until all smaller divisors. Revised degree-5,000 Python / degree-128 Mojo controls and paired measurements are in evidence/rational-root-2026-10-16-r2/; the original evidence packet is preserved but superseded. The selected Python cubic-grid gain is 2.61×, full-screen control 0.96× (unchanged code/noise); the initial 48.84× large-root speed claim is withdrawn for this selection. The final Int.MIN test uses [-2^63,2^63-1,1], root 1, to avoid a multi-billion-step full divisor search. Evidence: docs/rational-root-optimization-2026-10-16.md and the revised regression/benchmark programs.

2026-10-19 — **Project progression acceptance convention.** For continued PSC
proof development, a result that is mechanically sufficient at its exact
recorded scope (proof/certificate complete, hypotheses preserved, required
exact replay/CI receipts present) is implicitly project-approved and may be
load-bearing without waiting for a separate human-review event. This is an
operational interpretation of the existing non-blocking review policy, not a
claim that independent human review occurred. Keep finite-domain, conditional,
family-scoped and universal quantifiers unchanged; independent human review
remains final validation. Evidence/status surfaces: `AGENTS.md`, `README.md`,
`docs/README.md`, live roadmap, proof ladder and claim/source map.

2026-10-19 — **Issue #9 closure clarification.** Issue #9 was closed
`completed` on 2026-10-07, but its thread contains no theorem-bearing closure
argument and its preceding canonical notes explicitly left C4/Part (b) open.
Interpret the closure as completion/routing of that research track, not proof
of C4. The surviving obligations are word-level: occurrence/address-compatible
realizability, ordered hub-residual words across actual interior children, and
alignment/coverage strong enough to force the good edge. Algebraic quotient
compatibility, a projected zero, or one replayable path is insufficient. Keep
G1 extraction separate: C4 is about a supplied finite strict SCC; G1 is the
separate global finiteness/extraction problem. Canonical locations:
`docs/c4-good-edge-system-bridge.md`,
`docs/target-aware-bpa-diagnostic-2026-10-02.md`, successor #84/#138/#139.

2026-10-19 — **Post-#277 class-D status correction.** PR #277 merged the
distinct class-D `b=0` certificate systems and their occurrence-agreement
checks. Both infinite boundary lines are therefore available as scoped,
mechanically certified inputs for project progression. The exact residual
class-D target is the two positive-`b` interiors
`s=±1, a>=0, b>=1`. Do not call these determinant-two domains "unimodular
parameter quadrants"; use **integral affine parameter quadrants**. The recorded
rank-one update refutes literal transport of the sealed `b=0` occurrence
spine into `b>0`, so the next certificate must be genuinely two-parameter.
General #139/#84/G1/PSC remain open. Evidence: merged PR #277,
`docs/p1b-boundary-hitting-progress-2026-10-08.md` §§4e–4m,
`tests/test_class_d_certificate_agreement.py`.

2026-10-19 — **PR #283 executed refusal audit.** With available Mojo 1.1.0 (8189361e), both complete positive-b drivers refuse their first integer-affine run fit (plus -808/-1408/-1007; minus 811/1412). After explicit-copy compile repairs, the sealed-cover checkers refuse at minus row 1 and plus row 0 on auxiliary polynomials that change sign on every shifted quadrant; both rows nevertheless have positive geometric margins by the exact Perron identity beta(d-2)=2D+2s/beta. No escaped child was reached, so no carrier enlargement is justified. Plus row 12 changes actual realness along b=a versus b=10a, ruling out its classification by a fixed real subcover on a single quadrant. Preserve caps/exact arithmetic and the literal-spine negative control; proceed by clipping/chambers or conditional upper-cover arguments, not larger corner guesses. Pinned pixi environment could not be installed; GitHub jobs observed queued. Evidence: docs/p1b-class-d-positive-b-wedge-2026-10-19.md section 10; evidence/class-d-positive-b-audit-2026-10-19/; kernel/tests/test_class_d_positive_b_obstructions.mojo. No claim promotion or merge-as-proved.

2026-10-19 — **PR #283 base validation findings.** The audit found unchanged-base claim-governance status-anchor drift (docs/proof-ladder.md:17, DensityToPDSBridge), stale proof-bank.json, and malformed/trailing manuscript content rejected at line 1357. These are distinct from positive-b mathematical refusals; generated ledger/math catalogue, vendoring and Markdown checks passed. Evidence: docs/p1b-class-d-positive-b-wedge-2026-10-19.md section 10 and evidence/class-d-positive-b-audit-2026-10-19/run-context.json. No gate waived.

2026-10-19 — **PR #290 recurrent-contract correction.** Unrestricted cyclic-carrier inclusion is false, but both independently replayed 56-specimen swap-seed grids have no escaped recurrent labels (127 or 129 recurrent vertices). Genuine formal U/Ubar/V/Vbar cycles do not by themselves establish seed reachability. Replace carrier-only rejection by exact typed classification, explicit exceptional exits and replayable unexplained labels; distinguish the noncarrier zero targets (x,x,0) coincidence versus (c,x,0) noncoincidence/BH target. A six-edge affine control recovers v=2u+7 and v<=u on ONE parameter pair; exact guard rows 0+5 give -7-u<0. This refutes that walk, not CycleSum-. Canonical Mojo plus independent Python receipts and unchanged-base governance/manuscript blockers: `evidence/class-d-minus-reduction-repair-2026-10-19/`; derivation and narrowed literature decision: `docs/p1b-class-d-minus-recurrent-carrier-2026-10-19.md` §§9–11 and `docs/class-d-minus-cycle-literature-gate-2026-10-19.md`. CycleSum-, universal #139/#84 and PSC stay open.

2026-10-19 — **PR #290 unbounded shared-guard family and baseline repairs.** The documented six-edge k=2 negative control extends to sums (-k,k-1,-k,k-1,-k,k) for every integer k>=2. Exact symbolic occurrence guards 0+5 cancel k and v to -7-u; for every even k=2t each edge separately has an integral witness, so edgewise parameter reselection creates artificial cycles with unbounded sums. This excludes one itinerary family and any shared-valuation walk containing its contradictory guard pair, not every higher-sum cycle. CycleSum-, universal #139 and PSC stay open. The earlier manuscript failure was two identical 183,857-byte tail injections into A1-prime expressions; a hash-recorded reconstruction preserves all unique text. Fixed status vocabulary, test syntax and contract; registered the existing two-obstruction assembly with both universal premises still open. Canonical symbolic Mojo receipts, independent finite calibrations, TLA+ models and reconstruction: `evidence/class-d-minus-continuation-2026-10-19/`; proof and scope: recurrent research note section 12. Pinned pixi replay still blocked by package tunnel failure; no validation gate waived.

2026-10-19 — **Seed qualification is essential to CycleSum-.** Cyclic scalar reconstruction forces m_n=2s_(n-1)+eta_(n-1) and x_n=2s_(n-2)+eta_(n-2)+delta_x,(n-1). Applying it to the LAST/RUN, RUN/LAST two-cycle yields U_k=(y,c,-2k,4k,-3k) and its mirror. On a=2k-1,b=1, every integer k>=2 gives one shared-parameter legal occurrence cycle with strict real interior geometry and |sum|=k; canonical symbolic Mojo proves -1/2<t<0 without a parameter cut. Thus shared guards plus realness cannot exclude all higher-sum formal cycles. Complete independent Mojo/Python seed graphs at k=2,3,8 have 139 states and omit both vertices; this is finite nonmembership, not uniform seed exclusion. Redirect the universal proof to a seed-preserved constraint or an address/predecessor obstruction. Keep the conditional 1971-state result, universal #139 and PSC unchanged. Evidence: `evidence/class-d-minus-high-sum-control-2026-10-19/`; derivation, qualifier definitions and stop/redirect: recurrent note section 13 and the appended literature gate.

2026-10-20 UTC — **Uniform minus seed carrier discharges the seed-qualified CycleSum premise.** The correlated Perron region 0<X,Y<1, 10X>7Y, 10-10X>3Y follows from beta*X=2a+4-2/beta and beta*(1-X)=b+2+X+2/beta. Canonical exact Mojo proves all real swap seeds and all real occurrence children stay in the sealed 145-label carrier throughout a>=2,b>=1: 9 seeds included, 3 nonreal; 12,255 child candidates partition into 1,218 carrier, 9,034 geometry exclusions and 2,003 guard exclusions. No child sum premise or parameter cap is assumed. Independent Fraction vertex enumeration agrees. This proves seed-qualified CycleSum and scoped minus BH via the existing ranked descent; unrestricted formal-cycle RC remains false. The coarse box leaves 148 apparent child escapes/19 labels and a seed obligation; direct norm-sign search on the strengthened margins refuses on an auxiliary polynomial, so exact Perron identities supply the region instead. Coarse-box and deleted-target mutations refuse. Universal #139/#84/PSC remain open; pinned CI and independent human review remain pending. Derivation and receipts: recurrent research note §14; `evidence/class-d-minus-seed-cover-2026-10-20/`.

2026-10-20 UTC — **Issue #139: entire minus class-D boundary hitting.** The omitted a=0,1 strips are exact lines (p,q,r)=(n+6,n+7,n+5) and (n+9,n+10,n+7), n=b-1>=0. Locked-compiler certificates give thresholds 42/72, 140/137 symbolic vertices, all 42/72 finite-prefix members PIP and hitting, and exact graph agreement at threshold and threshold+5. The native four-component aggregate replays b=0, both strips, the uniform core carrier, rank descent and conditional geometry. Combined with the existing r>=q-1 wedges, this covers all PIP minus class D. The installed minimal Mojo 1.1.0.dev2026090805 compiler/std/runtime were hash-checked against the lock-matched archive; the seed-carrier regression also passes there. Fixed five inherited copy/type errors in the selected-spine source without changing formulas. Full Pixi/CI and independent human review remain pending. Plus components are completed separately in #293; universal #139/#84/PSC remain open. Evidence and current next obligations: `docs/p1b-minus-boundary-strips-2026-10-20.md`; `evidence/issue139-minus-strips-2026-10-20/`.

2026-10-19 — **Post-#289 chamber execution.** The merged complete driver passes low wedge 0 and then refuses at low wedge 1 on an auxiliary polynomial with opposite signs along u=v and u=4v; the actual query -4-(5+2u+2v)beta-(3u+4v)beta² is strictly negative. The high wedge's first query factors as (beta-2)((u+2)beta+2)>0. Exact coefficient fallbacks repair these reader failures without changing the lattice cover, caps or child relation. All six explicit interface lines and five low cores have local receipts; full boundary/high outcomes and source variants are in the execution manifest. Mojo 1.1.0 was used after locked provisioning failed; original CI remains queued. No carrier extension or family/universal promotion is inferred. Evidence: docs/p1b-class-d-chamber-execution-2026-10-19.md; evidence/class-d-chamber-execution-2026-10-19/.

2026-10-19 — **Chamber audit governance reconciliation.** Base main also lacked a contract declaration in test_symbolic_line_empty_blocks.mojo and used an unrecognized imported-bridge label in proof-ladder.md. Add the declaration after its assertions and use the existing [IMPORTED theorem] vocabulary; neither changes mathematical status. Regenerate the stale proof inventory. The unchanged manuscript source still fails at line 1357 and receives no waived integrity credit. Evidence: the chamber audit provenance log and final validation manifest.

2026-10-19 — **Inherited class-D line pin drift confirmed.** The full symbolic-line regression expects q0=18 for D (n+1,n,n+3), but untouched main@85fafd3 and the chamber repair both compute q0=21 (97 vertices, 20 finite PIP members, one non-PIP). This is a reproducible base mismatch, not a new coefficient-fallback failure. Preserve the pin and report the red regression pending a separately justified reconciliation; no missing contract receipt is credited. Evidence: evidence/class-d-chamber-execution-2026-10-19/base-class-d-pin.log and symbolic-line-regression.log.

2026-10-19 — **Concurrent frontier reconciliation during chamber execution.** Preserve main@c0c5f9d (PR #292 documentation). Issue #139 / open PR #290 now use uniform recurrent-carrier inclusion RC- as the sufficient minus obligation; full child closure is stronger and is not asserted necessary. Open PR #291 owns the Mojo integer-squeeze certificate. The chamber execution contribution stays on the plus closure route and does not duplicate either active investigation. No new uniform minus or PSC conclusion follows from the finite SCC calibration.

2026-10-19 — **Final chamber execution boundary.** Under explicitly unpinned Mojo 1.1.0, all six cores and six interface lines pass, and 67/69 distinct boundary lines (71/73 strip obligations) pass. Low-1 v=13,14, with coefficients (4,69,4,68,3,53) and (4,74,4,73,3,57), time out at 1200 seconds; isolated retries lose the execution session without a verdict. High core (7,0) and all seven strips pass by recorded component replay. No aggregate receipt, pinned replay or family promotion exists. Preserve these exact two outstanding lines; the first observed reader obstructions were not escaped children. Evidence: final table and run-context.json in the chamber execution packet.

2026-10-19 — **Chamber continuation: recover the pinned Mojo compiler and resolve the two slow strips.** Full Pixi provisioning still fails on a conda-forge dependency, but the lock-matched `mojo-compiler` and `mojo-python` archives download directly and verify against their locked SHA-256 digests. The exact compiler/runtime is Mojo 1.1.0.dev2026090805 (34562fa1). Low-1 v=13,14 were finite-prefix execution-cost gaps, not additional mathematical obstructions: the tails have 164 vertices and thresholds 53,56. An exact monotone occurrence-interval sweep preserves ordered children (1,096-state differential plus 16 existing seed-overlap regressions) and completes both lines including every finite-prefix member and both graph cross-checks. The old q0=18 class-D test still returns21 with the pinned compiler; the gate is not waived. PR #290 subsequently refuted RC- using productive U/Ubar/V/Vbar cycles; the current open minus premise is CycleSum-, separate from plus certification. Evidence: `evidence/class-d-chamber-continuation-2026-10-19/`, `docs/p1b-class-d-chamber-execution-2026-10-19.md`. No universal #139/#84/PSC promotion.

2026-10-19 — **Pinned regression follow-through.** Replaying tests after the inherited class-D pin failure exposes the second historical norm-line pin mismatch (6 obtained, 4 expected). Untouched merged #289 with the pinned compiler reproduces both 21/18 and 6/4 mismatches. Do not attribute them to the chamber fallback or interval sweep, and do not credit the full symbolic-line suite; the final norm-product test passes independently. Evidence: `evidence/class-d-chamber-continuation-2026-10-19/pinned-baseline-pins.log`, `symbolic-line-suffix.log`, `norm-property-only.log`.

2026-10-19 — **Complete same-source plus component replay.** All six wedge calls (including all 73 returned strips, 69 distinct lines) and all six explicit line calls return zero under the lock-matched compiler/runtime. The canonical low-strip map and seven high-strip formulas reconcile exactly. The duplicate serial aggregate was manually interrupted (exit130); no aggregate marker is synthesized. Full Pixi/CI validation and inherited regression/manuscript gates remain separate integration debt, with no governed theorem promotion. Evidence: `evidence/class-d-chamber-continuation-2026-10-19/coverage-reconciliation.json`, component logs, and `docs/p1b-class-d-chamber-execution-2026-10-19.md`.

2026-10-20 — **Inherited clipping pins reconciled without changing coverage.** The parent of PR #288's clipping commit reproduces thresholds18/4 under the locked nightly; merged #289 reproduces21/6. The clipping endpoint queries enlarge sufficient sign thresholds, not the parameter domain. Complete line certification plus exact transition vertex-set checks at n=18,19,20 and n=4,5 justify the two updated pins; the full symbolic-line regression now reaches every contract. Preserve both historical receipts and avoid claiming a replay of every other pin. The pin edit leaves the aggregate binary byte-identical. Evidence: `docs/class-d-chamber-validation-2026-10-20.md`, `evidence/class-d-chamber-validation-2026-10-20/`.

2026-10-20 — **Reuse the independently located source reconstruction, with hash checks.** PR #290 commit 5e9391d repairs two identical manuscript-tail injections and the malformed show-your-work regression string. This branch verifies the original, duplicated-block and corrected hashes and reproduces that source byte for byte; no unique manuscript text or archived PDF is removed. Integrity and provenance now pass. The repair is not a review of the mathematical arguments. Evidence: the validation packet's `manuscript-reconstruction.json`, `manuscript-integrity.log`, and `provenance.log`.

2026-10-20 — **Correction to earlier RC- diagnosis.** PR #290 at 00c0cb8 clarifies that its 56-specimen complete seed grid has no escaped recurrent labels. Formal productive exceptions refute unrestricted carrier inclusion; those formal cycles alone do not establish seed reachability. Seed-qualified CycleSum- remains open, and real-interior shared-parameter formal cycles can have unbounded sums. Earlier entries asserting an observed seed-qualified RC- counterexample were too strong. The plus work supplies neither that counterexample nor the missing minus lemma. Locator: PR #290 and `docs/class-d-chamber-validation-2026-10-20.md`.

2026-10-20 — **Restore the missing conditional completion record, without satisfying its premises.** A broader governance regression finds the existing two-obstruction claim-map row unregistered (189 other tests pass). Reuse the three-record registration from PR #290 commit 5e9391d: universal aligned coincidence and universal boundary hitting stay open; their assembly stays conditional. Generate the surfaces and two-premise TLA+ model from `tools/make_ledger.py`; regression checks reject inference from either premise alone or from existing scoped class-D lines/wedges. The repaired focused suite passes (73 passed, one optional TLC mutation test skipped). No plus/minus family or universal premise is promoted. Evidence: `evidence/class-d-chamber-validation-2026-10-20/integrity-governance-tests.log` and `ledger-governance-repaired.log`.

2026-10-20 — **Concurrent minus proof advanced during the serial plus replay.** PR #290 at 3b16b5447aa9b3ecdecfdabb5033a381580f230e now records a uniform seed-carrier proof supplying CycleSum- for a>=2,b>=1, the a=0,1 strips, and a native complete-minus-residual receipt. Its existing-wedge assembly covers the PIP minus branch. Source inspection verifies the gated aggregate call sequence and committed exit0, all 335 source hashes and 16 evidence hashes; this plus session does not rerun or import that proof. Earlier open-CycleSum entries describe the prior frontier. Both contributions still distinguish local locked-runtime evidence from full Pixi/CI integration, and neither supplies universal #139/#84 or general PSC. Evidence: `evidence/class-d-chamber-validation-2026-10-20/minus-cross-reference.json` and PR #290's `evidence/issue139-minus-strips-2026-10-20/`.

2026-10-20 — **Native plus aggregate completed.** One uninterrupted lock-matched Mojo run returns exit0 after 3564 seconds and emits the native whole-domain marker only after all six wedge cores, 73 strips (69 distinct lines), six interfaces and 952 finite-prefix PIP obligations complete. Log identities match the earlier same-binary component campaign exactly. The old exit130 aggregate is preserved as interrupted; no receipt is synthesized or relabelled. The native max-vertices field covers only cores/interfaces, while line graphs reach 465 vertices. Full Pixi provisioning still fails and dedicated CI remains queued, so no governed plus-family promotion is made. The latest separate minus result is recorded in PR #290; universal #139/#84 and general PSC remain open. Evidence: `evidence/class-d-chamber-validation-2026-10-20/aggregate.log`, `aggregate-reconciliation.json`, and `docs/class-d-chamber-validation-2026-10-20.md`.

2026-10-21 — **Scoped class-D assembly and actual CI failure.** Reconcile merged #293 with #290: exact inverse lattice maps, complete positive-b strips and b=0 boundaries, common bottom-minus-top overlap convention, strict geometry, and offset-zero versus equal-letter coincidence semantics. The new native minus aggregate and plus b=0 replay pass with the locked compiler; the immutable plus aggregate is reusable only after all 47 imported local source files and its exact log/exit match. A separate open integration gate prevents the assembly from establishing universal #139, A/C obligations or PSC. Historical CI run 39352929916 successfully installed locked Pixi but failed later on the inherited line pin and pytest's missing repository-root import path; preserve that distinction from this session's full-install proxy failure. Evidence and derivation: `docs/class-d-assembly-audit-2026-10-21.md`, `evidence/class-d-assembly-audit-2026-10-21/`.

2026-10-21 — **Class-D CI publication repair.** Actual head 2e7d88f fails because new *.log receipts were ignored, full-suite jobs shallow-checkout the historical provenance revisions, five inherited packets lack checksum manifests, and nested chamber checksum paths are ambiguous to the generic guard. Publish the exact existing receipt bytes, preserve original checksum metadata while correcting paths, pin every packet and enforce Git-tracked evidence in regression. Replace the six already-refusing whole-quadrant/fixed-real-carrier CI attempts with the complete native minus/plus residual certificates, retaining obstruction controls and actual full aggregate acceptance. No mathematical source or status is changed. Failures and repair validation: `evidence/class-d-ci-repair-2026-10-21/`.

2026-10-20 — **Two-obstruction length-window interface.** The standard cyclic-vector argument makes d ordinary inflated-length observations injective on Parikh defects when the incidence characteristic polynomial is irreducible. For ternary PIP, inherited same-position common blocks at levels 0,r,2r already imply balanced prefixes; automatic block inflation is therefore not a missing proximality proof. A productive PIP fixed-ray control has drift (0,-1,-3), and a nonzero algebraic defect has observations (0,0,-1). The new exact Mojo address reader verifies supplied boundary paths while keeping equal-letter coincidence separate; rank-deficient reducible controls and malformed addresses refuse. Neither existence question is closed. Local unpinned runtime success and failed pinned download are recorded separately. Evidence: docs/two-obstruction-moment-interface-2026-10-20.md and evidence/two-obstruction-moments-2026-10-20/.

2026-10-20 — **Original chamber CI finally executed.** Run 39292497570 at pre-repair head 30dc38d passes the lattice partition and fails its aggregate on an exception byte-for-byte identical to the archived low-1 sign-reader refusal. PR #293 already addresses that reader obstruction and has a separate native local aggregate receipt; its head53a4021 run39356406683 remains queued at this inspection. No new chamber/carrier change is indicated. Evidence: evidence/two-obstruction-moments-2026-10-20/original-chamber-ci.log and original-ci-reconciliation.json.

2026-10-21 — **PR #295 conflict reconciliation.** Merge main@d91969e into the length-moment branch, retaining both independently appended side-note histories. Regenerate the proof inventory after combining the status notes. The length-moment implementation, its tests, and the October 20 evidence packet remain unchanged; historical runtime and CI observations remain historical. The universal #138/#139 premises remain open.

2026-10-21 — **Merged class D now passes complete CI.** PR #290 merged as 4996d21. All 64 checks on head a9457d9 succeed, including the last general one-tile census; the tested PR merge, accepted head and main merge have identical tree c325aa5. Full locked Pixi provisioning and fresh full plus/minus/assembly/calibration receipts discharge the separate integration gate at this exact source scope. Preserve the earlier false/pending snapshots and local proxy failure; human review remains pending. The ledger now establishes scoped determinant-two class D without an assumption, while Python and TLA firewalls keep universal #139/#138, G1 and PSC open. Historical class-D next-work items are superseded; A/C and uniform hitting remain. Evidence: `evidence/class-d-integration-accepted-2026-10-21/`; provenance: `tools/check_class_d_integration_ci.py`.


2026-10-21 — **Class-A fixed-depth obstruction beyond accepted class D.**
On A `(p,q,r)=(n+1,n,n+1)`, the explicit A_n=(c,y,n,-n,0) is seed-reachable
in 2n steps and recurrent for every n>=4. A polynomial eigenvector and the
contracting root alpha>1-2/n give n/10<L(A_n); the actual occurrence descent
A_n->B_n->...->B_0->coincidence gives L(A_n)<=n+2. This refutes the historical
parameter-independent K proposal, not BH, and supplies a usable variable-rank
family. Complete graphs n=1..24 hit; the independent Q(beta) oracle matches
all 835 vertices and 17,178 ordered occurrences at n=18. Arbitrary-n all-state
coverage and the remaining A/C domains are open. Class-D #298 acceptance is
unchanged; independent human review of the new written argument is pending.
Locators: `docs/p1b-class-a-run-index-2026-10-21.md`,
`kernel/psc/class_a_run_index.mojo`, `evidence/class-a-run-index-2026-10-21/`.
2026-10-21 — **Human-review policy made operational.** Clarify `AGENTS.md`'s existing post-closure review policy: exact mechanically sufficient results may support continued authorized work and integration once their proof/replay/CI/governance requirements pass, without a separate human-review event. Missing evidence remains a blocker; pending human review remains truthful nonblocking validation debt. Preserve accepted source scope and historical receipts. This changes no mathematical claim or CI requirement. Policy: `AGENTS.md`, Review gate; `claim_governance.toml [review_policy]`.

2026-10-21 — **Class-A integration follow-through.** The first PR #300 dedicated locked replay passed, while both general jobs failed because the historical class-D provenance auditor rediscovered its workflow scope from the growing current checkout. Bind that enumeration to accepted head a9457d9 instead, preserving every original source hash and receipt; added unrelated workflows cannot reopen the gate, while missing/changed accepted sources still refuse. Expand the class-A workflow trigger to the full kernel and independent reference tree. Preserve both side-note histories when merging main. This repairs integration only and proves no new mathematical assertion. Locators: `tools/check_class_d_integration_ci.py`, `tests/test_class_d_integration_ci.py`, `.github/workflows/class-a-run-index.yml`.

2026-10-21 — **Class-A rectangular run-index carrier refuted uniformly.** Even strict real geometry plus |x|<=n+1, |y|<=2 and |sum(w)|<=1 is not child-closed: V_n=(x,c,-n-1,n+4,-2) has the actual (0,3) child W_n=(x,y,-n,n+3,-1), whose sum is 2, for every n>=4. With h=1/(beta-1), normalized lengths (1+h+h^2,1,1+h) give four strictly positive margins and an exact polynomial proof. Complete seed graphs at n=4,18 omit both formal witnesses; no uniform seed exclusion or BH failure follows. A complete cover needs typed coordinate correlations. Canonical Mojo, independent calibration and proof: `docs/class-a-cover-obstruction-2026-10-21.md`, `kernel/psc/class_a_cover_obstruction.mojo`, `evidence/class-a-cover-obstruction-2026-10-21/`.
2026-10-21 — **Rauzy fractals on the 2-torus, exactly.** For a unimodular PIP σ the projection along `v` onto `H = {Σx = 0}` sends the stepped line to the discrepancy vectors `D_n = p_n − n f`, and `D_n mod H_Z = −n(f₀,f₁)`: the toral rotation is the frequency vector, so the whole picture needs only certified `⌊2⁴⁰ f_i⌋` (Sturm–Tarski in Q(β); an iteration hint cut the frame from ~560 ms to ~50 ms) and integer enclosures — no floats. The finite lift profile shows 2–3 lifts on boundary cells even for Tribonacci (`1:3957 2:47 3:1` at 8192 points, 64-grid), so it is a diagnostic and never a covering-degree certificate; non-unimodular specimens are refused (solenoid, not torus). Finite observation: specimen #3742 (`122/201/12`) shows no single-lift cell at all once n ≥ 16384, on 8-, 16- and 32-grids, so this sampler cannot resolve its tiles — resolution-limited, not evidence of covering degree ≥ 2. Kernel: `kernel/psc/rauzy_torus.mojo`; evidence: `evidence/rauzy-torus-2026-10-21/`; note: `docs/rauzy-torus-stop-go-2026-10-21.md`.

2026-10-21 — **Class-A/main integration reconciliation.** PR #303 passed all 63 checks and merged into #300 with an identical source tree. Merge main #304 while preserving both appended histories. Its only Pixi changes register two new Rauzy-torus task names; the accepted runtime/dependency configuration and every pre-existing task remain identical. Preserve the archived class-D manifest/hash checks and accept only this general additive task-table extension, with controls rejecting any accepted task, environment or lock change. No mathematical source in either class-A investigation or accepted class D is edited. Locator: `docs/class-a-integration-2026-10-21.md`.

2026-10-21 — **Lift histogram sized for the encoded window.** Codex's finding on merged PR #304 is real: `LiftProfile.histogram` allocated `Histogram(LIFT_SPAN)`, so a torus cell met in `LIFT_SPAN = 256` or more distinct lifts, which the `256 × 256` window permits, raised on a valid profile and could abort the census driver. The histogram capacity is now `1 + max(profile.lifts)` (at least 1), capped by the encoded `LIFT_SPAN²` bound. Ordinary specimens avoid scanning 65,537 unused slots, while the full 65,536-lift case is admitted. The end-to-end regression invokes `LiftProfile.histogram()` at 255, 256, 257 and 65,536 lifts, with duplicate, empty-profile and malformed-input controls. `Histogram.line` still lists only occurring keys, so the historical archived diagnostic outputs (maximum lift 5) are unaffected by capacity. Original PR #306 named/corpus replay receipts belong to its initial head; new-head Mojo/CI and corpus replay remain required before integration.

2026-10-22 — **Class-A line (n+1,n,n+1): boundary hitting for every n>=4, by uniform carrier closure and an affine potential.** The 89-row typed carrier of PR #307 is forward closed for every integer n>=5 (no conservative clip is needed from n>=8): with h=1/(beta-1), n h(1+h)=1-h-h^2-h^3 turns every margin into an integer polynomial in h whose sign on (0,1/(n0+1)] an exact Sturm count decides, and run positions, child labels and carrier rows are affine in n and the row index, so the nine first/run/last segment pairs, a y'-window of width 11 and the gaps between carrier intervals exhaust every ordered child. A 155-piece potential X=a n+b j+c with depth=floor(X/3) on the exact graphs n=8..24, 8 offset-zero targets and 221 chosen descent occurrences strictly lowers X at every member, giving first-hit depth <= 2n+9 for n>=8; n=4..7 are exact finite certificates. First-hit depth itself is not affine on a row (period-three plateaus), and raising the potential of a piece with no incoming descent is not a control: the valid controls lower a potential or raise a child's. The data-driven generator is not evidence; the two independent verifiers are. Concurrent PRs #308 and #309 proved the geometry and the forward closure of the same carrier independently (Bernstein-coefficient certificates); the closure here is an independent second proof by Sturm interval signs, and the descent is the new step. Other A regions, the C residual d>=4 and universal #139 remain open; human review pending. Locators: `docs/class-a-carrier-closure-2026-10-22.md`, `kernel/psc/class_a_carrier_closure.mojo`, `kernel/psc/class_a_carrier_descent.mojo`, `evidence/class-a-carrier-closure-2026-10-22/`.

2026-10-22 — **Tooling pitfalls met while packaging the class-A closure.** (a) The claim-governance status scanner matches only the synonym keys of `claim_governance.toml [status.synonyms]` (`repository-proved`, `[PROVED]`, …), not the bare class word `proved`; a `**Status:** proved (…)` line therefore satisfies nothing, which is why PR #307's typed-carrier proposition was still reported unlabelled, now repaired to `repository-proved`. A `**Status:**` line within the first ten lines declares a file-level status. (b) `tools/make_proof_bank.py` records statement line numbers computed on the masked text, so in a note with fenced code blocks the recorded lines and quoted headings drift (several entries of `docs/class-a-carrier-closure-2026-10-22.md` quote prose lines); the inventory is deterministic and regenerated, not hand-edited. (c) `tests/test_claim_governance.py` reads `kernel/build/claim-receipts.tsv`, which `kernel/run_tests.sh` rewrites from empty, so it fails while the Mojo suite is mid-run.

2026-10-22 — **Merged #308/#309 Mojo modules do not compile under the locked compiler.** `kernel/psc/class_a_uniform_closure.mojo` and `kernel/psc/class_a_uniform_geometry.mojo` landed on main (8827b9c) while their CI was still queued; `Mojo 1.1.0.dev2026090805` rejects fifteen implicit copies of `Affine`, `Segment` and `List[Int]` values ("does not conform to 'ImplicitlyCopyable'"), so the kernel suite and both dedicated workflows are red on main. Ported the minimal repair on the class-A descent branch: `Affine` and `Segment` declared `ImplicitlyCopyable` (two plain-`Int` and two-`Affine` records), one `^` transfer of the returned list, two explicit `.copy()` of carrier rows; no logic changes. Both tests and the driver then pass with their printed receipts unchanged. Independent of this, the merged #309 statement agrees with the Sturm-interval closure certificate of this branch.


2026-10-22 — **Theorem Ω historical sufficiency audit reconciled on PR #235, not accepted as new human review.** Preserve the October 8, 9, and 11 immutable packet histories, exact cardinality oracle (135,990 images<=4, 24,486 total<=8, overlap 14,670, union 145,806) and five independently replayed exact representative box graphs. The historical refinement makes Minkowski full-rank, the signed realized-overlap embedding, the substitution-power fixed tiling and coincidence padding, and Clark–Sadun flow-to-symbolic transfer explicit. Newer main already records a Sirvent–Solomyak transfer, which is not silently replaced. Historical CI evidence is scoped to its recorded revisions; current-head CI and governed statuses must be checked separately. Human mathematical review stays pending and is nonblocking research-validation debt under AGENTS.md, not a claim of independent acceptance. Locators: `docs/audit-theorem-omega-2026-10-08.md`, `docs/audit-theorem-omega-2026-10-11.md`, `evidence/omega-box-audit-2026-10-08/`, `evidence/omega-audit-reconciliation-2026-10-09/`, `evidence/omega-audit-reconciliation-2026-10-11/`.

2026-10-22 — **Class-A minus line (n+1,n,n-1): boundary hitting for every n>=1, by the #310 method on a line-parametric certificate.** With h=1/(beta-1), P=1-(n-1)h-(n+3)h^2-h^3, n h(1+h)=1+h-3h^2-h^3, h_n in (1/(n+1),1/n) (larger than on the plus line, so the Sturm interval is (0,1/n0], not (0,1/(n0+1)]), L=(1+3h+h^2,1+2h,1+h) and T=s(1+2h)+k h(1+h)-y h; y'=k+ns-y+Δm and the y run of sigma(y) has length n-1. A 104-row/99-slice typed carrier, fitted exactly to exports n=5..24 (n=4 splits two slices differently), is forward closed for n>=8 (56 conservative clips; none from n>=10; n0=7 closes, n0<=6 refuses), and a 176-piece potential with 265 descent occurrences gives first-hit depth <= 2n+11 for n>=8; n=1..7 are exact complete graphs. The Python verifier re-derives P from the incidence matrix and matches every count. Finite observations: |G_n|=40n+138 for n>=5, max first hit = ceil(2n/3)+3 for 4<=n<=24. Gap d>=2, other A regions, the C residual and universal #139 open; human review pending. Locators: `docs/class-a-minus-line-2026-10-22.md`, `kernel/psc/class_a_line.mojo`, `kernel/psc/class_a_minus_carrier.mojo`, `evidence/class-a-minus-line-2026-10-22/`.

2026-10-22 — **Descent-table generator pitfalls on the minus line.** (a) The exact `depth = floor(X/3)` fit has no solution on the minus target row (y,y,0,0): its first-hit plateaus shift with n mod 3 (0/3/4 unit decrements at k=-n for n=2/0/1 mod 3), so no affine piece boundary separates them. A potential only needs to dominate and strictly drop, so the generator now retries such a row with `depth <= floor(X/3) <= depth+1`; the generated header names the slack rows. (b) That row has width 2n, and its uniform-type sub-interval ends at 2n-1, outside the breakpoint slopes {-1,0,1}; breakpoints `hi-1, hi-2` relative to the piece end were added. Both changes leave the plus-line tables byte-identical (regenerated from re-exported graphs whose digests equal the archived ones). Locator: `oracles/python/class_a_descent_table.py`.

2026-10-22 — **Merged d=2 class-A Mojo sources (#312/#313/#314) do not compile under the locked compiler.** `Mojo 1.1.0.dev2026090805` rejects thirteen implicit copies of `List[Int]`/`List[List[Int]]` values in `kernel/psc/class_a_d2_parity_carrier.mojo`, `kernel/psc/class_a_d2_uniform_closure.mojo` and the three `kernel/tests/test_class_a_d2_*.mojo`, so those tests and drivers are red on main (46a6fae), reproduced on a clean main worktree. Ported the minimal repair while merging main into the minus-line branch: explicit `.copy()` on element reads/assignments, `^` on returned locals; no logic change. All three tests and the four d=2/residual drivers then pass. Same class of pitfall as the #308/#309 entry above.

2026-10-22 — **Class-A residue rays: boundary hitting on (n+2,n,n-1), (n+3,n,n-1) and (n+3,n,n+1), each on its whole domain.** For gap d>=2 no carrier is affine in n, but with n = d l + r every label set of n=8..35 (d=3 minus from n=11) is an exact union of intervals affine in l. The gap-one certificate then transfers by three facts: d(a l+b) = a n + (d b - a r) puts every Perron sign back in the A(h)+nB(h) form; the child index y' = d k + n s + eps y + Δm makes realizable row indices [ceil(./d), floor(./d)], affine in l because every run has l-slope d; T' still increases in j and y'. n^3 P(n,1/n) < 0 for both signs and every d gives the Sturm interval (0,1/n0]. Eight rays certify (floors 14..20, depth <= 2l+11), Mojo and the independent Python verifier agree on every count, and every n below a floor is an exact complete graph; the d=1 receipts stay byte-identical. The d=2 plus line is left to PRs #312-#319. Finite: certified floors are where both certificates are first accepted (undecided signs, a vanishing bound at q=1/15 on (n+3,n,n+1) n=3l, or a negative-length piece below). Tooling: complete-graph exports with edges grow slowly past n~35 at d=2 (minutes each); `pkill -f PATTERN` inside a shell whose command line contains PATTERN kills that shell. Locators: `docs/class-a-residue-rays-2026-10-22.md`, `kernel/psc/class_a_line.mojo`, `kernel/psc/class_a_ray_tables.mojo`, `evidence/class-a-residue-rays-2026-10-22/`.

2026-10-22 — **Class-A d=2 plus line (n+2,n,n+1): boundary hitting for every n>=1, by the generic residue-ray certificate.** The parity-carrier program (#312-#314, open #318/#319) was growing fixed productive subsets (80, then 598 states) toward a whole-carrier potential; the #321 certificate is parametric in (d,eps,r) and only omitted this line by ownership. Generating `class_a_ray_d2p.mojo` from exports n=4..39 gives rows 93/87 (= #312's carriers exactly; independent Fraction-field profiles agree at n=8,9,12,13,16,17,22,23), and both rays certify: closure + descent from n>=14 (n=2l: 149 pieces, 207 descents, depth <= n+9) and n>=13 (n=2l+1: 141 pieces, 186 descents, one slack row, depth <= n+10); n<=12 is exact complete graphs; n=0 is on p=2q+2. Mojo and Python verifier counts agree. Finite: `certify 2 1 0 12` / `2 1 1 11` stop at an undecided Sturm sign; the even descent table generated from n=10 has two incomparable clipped pieces. Lesson: before constructing a bespoke corridor/shell for one line, check whether a parametric certificate already on main covers it. Tooling: the `pkill -f` self-kill pitfall of the #321 entry recurred (a `pkill -f "ray export ..."` inside a compound command). Locators: `docs/class-a-d2-plus-rays-2026-10-22.md`, `kernel/psc/class_a_ray_d2p.mojo`, `evidence/class-a-d2-plus-rays-2026-10-22/`.
2026-10-22 — **d=2 plus line shown in Mojo.** `psc.class_a_d2_plus_line` assembles the theorem with one receipt per part. Its `witness N` re-derives every chosen child from w' = (k+s, s-k, ns+2k+y) + prefix_b(j) - prefix_t(i), independently of the Perron-field engine: 5,598 steps over n=13..24, all agreeing. Finite observation: chosen-chain lengths (11..16) exceed the maximum first-hit depths (7..11) but stay under X. `replay_descent_finite_line` now delegates to the record-returning `descent_witnesses_line`; gap-one plus/minus and residue-ray native logs are unchanged (blank lines aside). The carrier = #312 identity is now an exact affine-table comparison rather than a sampled one. Locators: `kernel/class_a_d2_plus_line.mojo`, `evidence/class-a-d2-plus-rays-2026-10-22/witness/`.

2026-10-22 — **Actions queue starvation; superseded runs now cancel.** At 22:00 UTC the repository had 746 queued workflow runs, and the runner had reached runs created at 09:17. No workflow declared `concurrency`, so every push to a research branch queued five push workflows plus the PR set. Every older commit's runs stayed queued even after a newer commit superseded them. PR #323's checks for its head never started before it merged. All 32 workflows without a block now share one: group `workflow-event-ref`, `cancel-in-progress: true`; on `main` the group is the run id, so every main commit keeps its receipts. `grow-corpus-daily.yml` keeps its own non-cancelling group. Nineteen of the workflows are byte-pinned by the class-D provenance auditor (accepted head a9457d9). `tools/check_class_d_integration_ci.py` now accepts a pinned workflow only if deleting exactly one added top-level `concurrency:` block restores the historical bytes exactly, following the `kernel/pixi.toml` additive-task precedent. Any other change still refuses. A cancelled run yields no receipt, so the exception cannot manufacture an acceptance. Locators: `.github/workflows/*.yml`, `tools/check_class_d_integration_ci.py`, `tests/test_class_d_integration_ci.py`.
2026-10-23 — **#323 merged with two Python-suite failures, now repaired.** (a) `tests/test_recorded_data_integrity.py` reads a `SHA256SUMS` path containing `/` as repository-relative unless it starts with `./`. The packet's `witness/…` entries pass `sha256sum -c` but failed both the checksum and the tracked-file tests. They are now written `./witness/…`. (b) The note linked the descent-obligations note, which exists only on the unmerged #318 branch (`tests/test_markdown_links.py`). It now cites #315 in plain text. Lesson: run the full `pytest` before relying on a targeted subset when a PR adds a nested evidence directory or links notes from other branches. The full suite takes about 25 minutes locally. Locators: `evidence/class-a-d2-plus-rays-2026-10-22/SHA256SUMS`, `docs/class-a-d2-plus-rays-2026-10-22.md`.

2026-10-22 — **#139's A/C targets advance through gap four.** Eight A residue rays certify closure and integer rank descent (floors 19..25), with exact prefixes including plus n=0; both C gap-four lines certify completely (plus q0=49 / 201 vertices / 46 PIP prefix members; minus q0=85 / 216 vertices / 76 PIP prefix members). A short finite descent fit can pass all sampled occurrences while its rank difference has negative eventual slope; an archived candidate rejects under the exact verifier, then fixed-occurrence rank refitting succeeds. LP is synthesis only, with integer reconstruction and independent exact checks before writing; canonical Mojo remains the certificate. C's entire d>=4 residual has an exact two-wedge cover, but direct wedge execution refuses a non-affine run-position bound at the first seed. Tooling: A finite differential helpers had a deliberate n<=24 budget; the new second tail samples require n=28,29, so the explicit bound is now 32 and its refusal control is 33. Neither a failed heuristic nor a raised finite budget changes mathematical scope. Remaining A/C gaps d>=5 and universal #139 are open. Locators: `docs/issue139-ac-gap4-2026-10-22.md`, `evidence/issue139-ac-gap4-2026-10-22/`.
2026-10-23 — **Class-A gap four, both signs: boundary hitting on (n+4,n,n+1) for every n>=0 and (n+4,n,n-1) for every n>=3, by the residue-ray certificate.** No new certificate code was needed: eight rays n=4l+r generated from exports (plus n=1..55, minus n=3..47) and registered. Floors are plus 24/21/22/15 and minus 24/25/22/23. Depth is at most 2l+11. Carriers are 40l+{88,90,88,92} and 40l+{75,145,129,125}. Mojo and the Python verifier agree on every count. Finite observations: the carrier fit starts only at n=12..17 on five rays (run counts and endpoints are not affine earlier). Below the floors the certificate refuses: Sturm polynomial vanishing at the bound on plus r=0 at 16 and 20; root in (0,q] elsewhere. The plus line's n=0 member (x->xy^4x, c->cx, y->xyc) is on no previously certified line and is checked as an exact graph (319 vertices, depth 5). That needed `ALine.check_domain` to state the note's full domain, which it had over-restricted to n>=1. Tooling: exports with edges take minutes each past n~45 at d=4; budget a 2h background run for n<=47. The finite replay budget of the carrier and descent replays rises from n<=24 to n<=48 for floor-24/25 rays. The open frontier is d>=5: one line per (d,eps), an infinite family, so ray-by-ray tabulation does not close it; a certificate uniform in d is the next design question. Locators: `docs/class-a-d4-rays-2026-10-23.md`, `kernel/psc/class_a_ray_d4p.mojo`, `kernel/psc/class_a_ray_d4m.mojo`, `evidence/class-a-d4-rays-2026-10-23/`.
2026-10-23 — **Class-A gaps d>=5: stop/go for a d-uniform certificate; finite regime profile.** With d<=4 certified on both signs, the remainder is one line per gap, so ray-by-ray tabulation cannot finish. `profile D EPS 64` fits per-residue exact vertex counts as 40l+c(d,r). For d<=13 the constants settle into boundary regimes plus one middle value: minus 73,147 | 139 | 135,127,123; plus 86,98,118,114 | 112 | 108,100,96,86,90. Every graph hits, and the maximum first-hit depth falls with d (46 at d=1, 5-9 for d>=8, n<=64). Mechanism (sketch): rounding ceil((c - r s)/d) in the child index is constant except for r within bounded distance of 0 or d. Prior art: Berthé-Bourdon-Jolivet-Siegel's infinite-family framework needs unimodularity (class A is determinant two); Akiyama-Gähler-Lee (trace<=2) excludes class A (trace q+s+3>=3). Decision: proceed, narrowed. Next, fit carrier rows per regime affine in (l,d) and (l,d,r) from exports n<=~8d; the stop condition is a failed fit. Pitfall: profile flags at small l are an l-threshold (proved rays need l>=4..7), and at d>=14 the n<=64 window only reaches pre-threshold l. Locators: `docs/class-a-gap-uniformity-stopgo-2026-10-23.md`, `evidence/class-a-gap-profile-2026-10-23/`, `kernel/tests/test_class_a_gap_profile.mojo`.
2026-10-23 — **Class-A gap regimes, step (a): label sets fit exactly per regime and depend only on l.** New Mojo datasets (`kernel/class_a_gap_regimes.mojo build`) store each member's complete-graph label set losslessly as typed k-intervals, built on parallel_fold workers and appended in canonical order. Files are byte-identical at any worker count (replayed d=6 minus at 2 workers/batch 5 against the archived 4/16), resumable, and loads fail closed. Coverage: d=1..16 both signs, l=5..9; d=17 partial. Exact fits over Q (basis n,l,d,(r),1) hold on every regime. Minus, J=3: r=0,1,2 | 3<=r<=d-4 | d-3,d-2,d-1, from d>=5/6. Plus, J=5: r=0..4 | 5<=r<=d-6 | d-5..d-1, from d>=5..10; the middle needs d>=11. Plus refuses at J=3,4. Every fit has full rank and no endpoint uses n, d or r: each regime is one l-affine table for all gaps. The open obligation is the Perron sign lemma in (h, u=d h) plus the rounding by d. Tooling: (1) edge enumeration (`ordered_child_occurrences`) costs ~80x the graph closure (300 s vs 3.7 s at d=16,n=64), so label datasets omit edges. (2) The session disk allowance was exhausted by two 7.9 GB orphaned Lean-verifier temp dirs (`/tmp/tmp.*`, `download-cache/*.ltar`) left by killed `check_lean.sh` runs whose EXIT trap never fired. Locators: `evidence/class-a-gap-labels-2026-10-23/`, `kernel/psc/class_a_gap_dataset.mojo`, `kernel/psc/class_a_gap_regimes.mojo`, `docs/class-a-gap-uniformity-stopgo-2026-10-23.md`.

2026-10-23 — **#326/#327 conflict resolution preserves both certificates.** Main's independently generated A gap-four tables remain in the default registry, including the earlier plus r=3 floor 15 and the full n=0 domain. #326's byte-identical alternative tables move to `_rank` modules and a dedicated registry/test; their minus r=0,1 bounds l+4 remain available. The finite-fit countercontrol explicitly selects those tables, not main's different occurrences. Main's finite helper budget 48 is retained with refusal at 49. Both archived evidence packets and side-note histories survive unchanged. The #326 review's shifted C4 proof-bank locator is repaired at the generator and guarded by a fenced-block regression. Locator: `docs/issue139-ac-integration-2026-10-23.md`.
2026-10-23 — **Graph exports were sign-bound, not graph-bound.** On `(n+16,n,n+1)` at n=64 the complete graph built in 3.7 s but exporting its 16,971 edges took 370 s: `ordered_child_occurrences` evaluated every Sturm–Tarski sign afresh while the graph builders shared a `Dict[CubicElt, Int]` cache. One shared cache per export (`ordered_child_occurrences_cached`, `class_a_line_graph.survey`) makes it 5 s (n=128: 17 s) with byte-identical records against the archived `graph-d4p-n24.log` and `graph-d2m-n14.log`. The other many-parent callers (`class_a_run_index`, `class_a_carrier_descent`, `class_a_typed_carrier`, `boundary_hitting_spine`) still use the fresh-cache wrapper and would gain the same.
2026-10-23 — **Tooling pitfall: generated Mojo tables are compiled into the binary.** Regenerating `kernel/psc/class_a_gap_regime_descents_minus.mojo` and re-running an already built driver re-tests the *old* tables; three generator variants were judged "still refused" before the binary was rebuilt. Rebuild after every table regeneration, or read tables at run time.
2026-10-23 — **Descent-table generator rules for regime mode.** (a) Every part the uniform verifier tiles must be non-empty for every `l >= l0`, so a candidate boundary that empties a piece or sub-interval at any sample `l` is now rejected in `--src` mode (`NONEMPTY`); the ray mode is unchanged and `d = 2, 3, 4` tables regenerate byte-identically from fresh exports whose digests equal the archived ones. (b) Among descent types with equally few child pieces the first whose clips are all comparable on the tail is taken; an incomparable clip is a crossing of two affine ends that no affine row expresses. (c) `--tail-floor NLO` is needed in regime mode: without it `floor_fit` admits potentials with negative eventual slope, which the verifier refuses as "potential is negative on a piece". (d) Eight samples `l = 5..12` of one ray at the regime's closure floor sufficed for all 18 regimes (0 failures); three samples did not. Locator: `oracles/python/class_a_descent_table.py`, `evidence/class-a-gap-theorem-2026-10-23/generator-regimes.log`.
2026-10-23 — **Box artefact in the regime Perron signs.** Two plus regimes (low r=1, r=2) refused the descent on the plain `(u, t)` box at every `d0 <= 24` with "a box cell is still mixed at depth 12": the margin `h(1+h)(1 - 5u(1+h))` is positive at every member but about `1/(5d)` at `l = 5`, so the member images accumulate at the corner `(u, t) -> (1/5, 0)` where the margin and the hull condition `E - 5u(1+h)` vanish together. Skipping cells outside the hull does not separate them (the corner is in every cell around it); subtracting the hull multiple that cancels the `h`-free part leaves `h(1 + u + u h) > 0`, decided at depth 0 (Lemma 3' of the design note, `poly_hu.sign_within_hull`). Every other regime sign was decided on the plain box; the closure receipts are identical with and without the hull.
2026-10-23 — **Seven plus residues below every fitted regime floor.** `(d, r) = (5,1), (5,2), (6,1), (6,2), (7,2), (7,3), (8,3)` are reached by no regime of `J = 5` at their gaps; their own ray tables (`class_a_ray_d{5,6,7,8}p.mojo`) certify at `n0 = 26, 22, 31, 32, 44, 31, 43`, and `oracles/python/class_a_carrier_closure.py --ray` reproduces every count. The minus sign has no such residue: low 0..2 and high 1..3 cover `d = 5, 6` and the middle regime starts at `d = 7`.

2026-10-23 — **Gap-five continuation separates C proof from A calibration.** Both class-C lines (n+5,n,n-4), n>=5, and (n+5,n,n-6), n>=11, pass the unchanged complete native symbolic-line checker. Tail floors 62/132, vertices 196/214, sign reads 6858/7658, and all 57/121 PIP finite-prefix members pass, with exact graph comparisons at floor and floor+5. The immediately preceding C normal forms n=4/10 are non-PIP, not counterexamples. Class-A d=5 passes only the 23-member n<=12 pilot (plus includes n=0); no whole-line A claim follows. Native endpoint and target-free-cycle controls plus corrupted-receipt regressions bound the evidence. Local minimal lock-matched runtime success is separate from hosted acceptance and human review. Next: A gap five and C gap six, ultimately a uniform-in-gap mechanism; universal #139/G1/PSC stay open. Locators: `docs/issue139-gap5-2026-10-23.md`, `evidence/issue139-gap5-2026-10-23/`.

- 2026-10-23: PR #328 replay scheduling omitted transitive graph/arithmetic inputs; use conservative `kernel/**` and guard omitted, vendored, lock and future paths in `tests/test_gap_five_evidence.py`. Certificate scope is unchanged.

2026-10-22 — **Class-D continuation must start after accepted #277/#298, not from the old #263/#266 candidate labels.** Source/CI provenance at tree c325aa5345e1f49b2fb50b37565bd2902104aab7 establishes the unchanged scoped hitting certificates. Both full b=0 branches have uniform all-seed depths (minus <=4, plus <=6), despite the absence of a uniform spectral contraction margin. Existing Proposition 4 and its integer-bound refinement give scoped finite BPA on determinant-two class D and b=0 all-level bounds 2(3a+8)^6 and 2(3a+5)^8; no new native mechanism, universal G1 or spectrum conclusion. Historical packet limitations and the generated universal gates remain intact. Locator: `docs/class-d-g1-corollary-2026-10-22.md`; primary-source stop/go reuse and exact occurrence/negative-control distinctions are recorded there.

2026-10-22 — **Scoped class-D G1 registered without closing universal G1.** `ClassDFiniteBPA` instantiates the existing half-coincidence implication on accepted `ClassDBoundaryHitting` plus `SwapOverlapFiniteness`; it must not depend on the universal `G1HalfCoincidenceRoute` node, which bundles an open all-PIP premise. Generated Open-model reachability includes the scoped corollary and excludes G1/PDS/universal hitting. Making either input open blocks the corollary; TLC rejects the false scoped-nonestablishment invariant. All 18 TLA models pass their expected outcomes. Main #323/#325 was merged into #324 with both side-note histories preserved, and the unchanged class-D mathematical source acceptance still validates. Current-head hosted CI remains separate. Locators: `docs/class-d-g1-corollary-2026-10-22.md`, `tests/test_ledger_generation.py`, `evidence/class-d-g1-ledger-2026-10-22/`.

2026-10-23 — **#324 class-D G1 corollary independently rechecked; no defect.** Every step of `H_-=2(3a+8)^6`, `H_+=2(3a+5)^8` reproduces (L, the two-edge Perron ratio, beta<=L, K+2 exponents, 9-power state sum, run-index interval, prefix/tail joins). Easy-to-miss point: the plus driver's printed "finite prefix a=0..6: all hitting" understates the check; `certify_boundary` asserts the depth bound itself on every prefix vertex, which is what H needs. Fresh local native Mojo (3 commands) and TLC (18 models; jar digest equal to the earlier pin) exit 0 on the merged tree; this is new local validation, separate from the archived acceptance and from hosted CI. The PR's non-mergeability was an append-only side-notes conflict plus the generated proof bank, resolved by appending and regenerating. The corollary note is left byte-identical so the 2026-10-22 packet's digest pin of it stays current. Locator: `evidence/class-d-g1-review-2026-10-23/README.md`.

### 2026-10-23 — High-degree Pisot literature/PSC audit, status-only
The literature comparison records that number-field exactness does not itself certify occurrence-compatible overlap productivity; full-rank/defect-theorem UD is already proved, whereas the historical UD⇒G1/PDS and ban-on-noncoincident-cycles routes are withdrawn. Fibonacci's explicit productive noncoincident two-cycle is a small calibration alongside the existing flipped-Tribonacci control. GitHub tracker #139 is closed but universal BH remains open on live claim surfaces; reconcile the tracker without theorem promotion. Locator: `docs/high-degree-psc-research-comparison-2026-10-23.md`. No executable or governance mutation.

### 2026-10-23 — Correction to earlier high-degree comparison's #139 tracker snapshot
The preceding high-degree comparison entry accurately reported **historical** GitHub closure of #139 at 10:09:55 UTC, but the mathematical BH predicate was not discharged. Issue #139 was **reopened** at 17:45:32 UTC to align its state with the live theorem-obligation ledger. Scoped class-A/C/D certificates remain scoped; all universal BH, #84/#138, G1 and PSC claims remain unchanged. Record: `docs/issue-139-tracker-mathematics-reconciliation-2026-10-23.md`; issue https://github.com/larsbx/pisot-substitution-conjecture-research/issues/139. Append-only correction, no alteration of the original provenance entry.

### 2026-10-23 — #138 historical closure was already reversed on 2026-10-01
GitHub #138 has one historical `closed` event (2026-09-26 06:15:09 UTC) and a `reopened` event (2026-10-01 20:50:15 UTC); the October 23 audit found it *already open*. The reopening comment records no theorem-bearing artifact attached to the old closure. Current minimal A1′ (residual fixed-letter hub-edge eventual coincidence) is **one-sided**; full two-sided strong coincidence is a stronger historical target, not an extra premise in the two-obstruction completion theorem. Do not claim both #138 and #139 needed new administrative reopening on October 23. Live A1′, BH, #84 and PSC remain open. Locator: `docs/issue-138-tracker-history-2026-10-23.md`; issue https://github.com/larsbx/pisot-substitution-conjecture-research/issues/138. Historical entries preserved.

### 2026-10-23 — G1 necessity direction already closed by PDS (status clarification)
Theorem S / manuscript `prop:PDS-implies-G1` is **repository-proved** as `PDSImpliesRepoG1`, audited 2026-10-04 with repository dependency nodes added 2026-10-05; `PDSImpliesSeedwiseTermination` is also repository-proved. The comment that "G1 remains open" is only correct for **unconditional universal G1**, a distinct ledger node with status:open; no general PDS premise was proved in this audit. Keep #44 (direct renewal route) open and do not reclassify the established PDS⇒G1 implication. See `docs/g1-pds-necessity-status-2026-10-23.md`. This records existing status, no new theorem promotion.

2026-10-23 — **Narrowed-target frontier for #84/#138/#139.** The trackers stay open, but their targets are much narrower than their original issue text. #84 has no independent work target: it closes exactly when one-sided A1′ (#138) and occurrence-compatible existential BH (#139) close. On the catch-up-free |det M|=2 class, A1′ is proved except for a residue of Theorem K's family F, and BH is proved on class D, class B below slope 5/2, A gaps d<=4 and C gaps d<=5. Ranked next lines: a d-uniform A/C certificate, the F residue, the B top layer, then non-unit good-branch existence and fixed-ray proximality. Retired routes are listed in one place. Orientation only; no claim status changed. Locator: `docs/direct-attack-frontier-2026-10-23.md`.

2026-10-23 — **Lateral move 1: conjugacy transfer is empty except for class B, where it opens the catch-up regime.** Powers and roots cannot add `|det M|=2` members, since (±2)^n ≠ ±2. Theorem E classes A, C and D have no letter rotations at all: x and c head their own images, and the endings are never constant. Every class-B member has exactly min(p,q,r)+2 conjugates (the right-step chain). The nontrivial conjugates are not catch-up-free (proper prefix y^{k-1}xx lies in Λ), yet inherit PDS from Theorem C by conjugacy invariance, hence G1 and, via Theorem S plus Proposition V, BH. This gives an explicit infinite catch-up-regime family on which BH is known to hold: a calibration and negative-control set for catch-up mechanisms. Bounded census p,q,r<=30: 667 Theorem C members yield 8,576 conjugates, 8,571 outside Ω and none with a Barge witness up to power 2. An earlier remark that rotations would move certified families generally into the catch-up regime was wrong for A, C and D; it holds only for B. Locators: `docs/lateral-generalization-strategy-2026-10-23.md`, `kernel/psc/conjugacy_orbit.mojo`, `kernel/lateral_conjugacy_census.mojo`, `evidence/lateral-conjugacy-2026-10-23/`.

2026-10-23 — **Catch-up is a presentation property: one conjugation step turns simultaneous births into catch-up hits on class B (finite observation).** Complete seed graphs were built for all 203 Theorem C members with q<=8 and their conjugates (1,385 graphs, at most 1,848 vertices, depth at most 9). Every vertex hits offset zero, consistent with the conjugacy Corollary. σ has 0 of its 52,452 recurrent nonzero vertices with a catch-up hit (Lemma P); the conjugates have 267,058 of 267,058. A catch-up-keyed BH mechanism therefore has to be conjugacy-aware, and one-tile failures on catch-up-free specimens may be presentation artifacts where a conjugate exists (in Theorem E's classes, only B). Proving the conversion on class B is the next move-6 target. Locators: `docs/lateral-generalization-strategy-2026-10-23.md` §2, `evidence/lateral-conjugacy-2026-10-23/bh-qmax8.log`.

2026-10-23 — **Independent #335 audit: floor cap alone is not a generic polynomial overflow guard.** The original box conversion maps the positive h^11 coefficient to a negative rational at (l0,d0)=(1,53), since 53^11 wraps Int64. Exact rational reciprocal powers repair it without changing the scoped low-degree theorem or the supported 1..64 floor interface. The polynomial grid test also caught its own assertion failures; assertions now sit outside the refusal handler. New dedicated hosted replay covers arithmetic, all 18 regimes, exceptional rays and assembly. Six independent Fraction/Sturm stress rays at d=1,000,003 pass for every l>=64, a fixed-gap check rather than a uniform-gap proof. n<5d, class C and universal obligations stay open. Locators: docs/class-a-gap-independent-audit-2026-10-23.md, kernel/tests/test_poly_hu.mojo, oracles/python/class_a_gap_regime_adversarial.py.

2026-10-23 — **Stronger overflow control for the #335 audit.** The original `sign_on_box((1-53h)^2-h^11,1,53)` returns +1, but its value at h=999999999999/53000000000000 (u=999999999999/10^12,t=1/53) is strictly negative by exact Q evaluation. This is a false generic sign certificate, beyond a corrupted coefficient. The exact-power repair refuses it. Locator: kernel/tests/test_poly_hu.mojo; docs/class-a-gap-independent-audit-2026-10-23.md.
2026-10-23 — **Class B's top layer is residue-ray shaped: period = gap to the Pisot boundary, +112 vertices per period (finite profile; go).** Write g = 3q+12-p (plus) or 3q-p (minus). On all 8 probed lines (plus g=1..5, minus g=1..3, q<=30) every vertex hits offset zero. Vertex counts are periodic-affine in q with period exactly g and increment 112 per period on both branches. The first-hit depth grows with q (g=1: about q/2+6, reaching 19-21), so the rank must depend on the parameter, as for class A slope one. Barge: 0 power/rotation witnesses among the 708 PIP top-layer members with g<=12, q<=40. Pitfall: a three-point fit at q<=18 missed a late floor on plus g=3, residue 1 (fixed by q<=30); use longer windows before trusting a fit. Decision: per-gap residue-ray certificates g=1..5 first, then a g-uniform regime certificate on the #334/#335 engine. Locators: `docs/class-b-top-layer-stopgo-2026-10-23.md`, `kernel/class_b_top_layer_profile.mojo`, `evidence/class-b-top-layer-profile-2026-10-23/`.

2026-10-23 — **Class-B top-layer full label fits survive all eight pilot lines through q=42 (finite only).** Regenerated 289 complete native graphs: all 177 historical count/depth summaries agree, and all 112 later graphs pass models fitted only within the original bounds. Coordinates s=3k+c+y, d=c−3k compress labels along (1,3,−6); all 21 rays have exact integer-affine typed interval ends and +112 labels per l-step, with 190 native full-interval comparisons and independent compression/expansion. Intervals remain nonempty/disjoint on their formal infinite tails, but graph equality, real geometry and closure there are unproved. Real count-only negative control: plus g=2 q=9,11,13 has +112 counts but type (0,2,−1,−3) acquires an internal hole. Rank warning: 290/389 bounded depth-envelope candidates on plus g=1 survive q=27..42; 99 rows refuse, and 202 of the selected actual shortest-child edges do not lower X. All 5,626 selected occurrences at q=9,10 replay independently; q=9 parent (y,x,1,3,−5) to (x,x,0,−3,5), indices (11,0), has X=10 on both ends. Go for finite carriers, redirect to joint piecewise-rank/occurrence synthesis; no infinite BH/G1/PSC promotion. Locators: docs/class-b-label-rays-2026-10-23.md, evidence/class-b-label-rays-2026-10-23/, kernel/class_b_label_rays.mojo.

2026-10-26 — **Class-A l=0 boundary-layer contraction control:** for each fixed k>=0 the admissible rays d=2n+6eps+5-k contain a real non-Perron eigenvalue in (-1,-1+(k+2)/n); hence no uniform strict contraction margin and no transfer of #335's u<=1/5 chamber into this strip. A separate exact 261-state / 12,546-child finite BPA oracle for (n,d,eps)=(3,5,-1) hits a diagonal from every state but one seed witness begins at an outer boundary, so it proves no occurrence-compatible interior BH. Scoped algebra plus finite prototype only; no #139/C4/G1/PSC promotion. Locator: docs/class-a-boundary-layer-2026-10-26.md; evidence/class-a-boundary-layer-2026-10-26/probe.json.

2026-10-26 — **Boundary-ray u>1 on the entire l=0 chamber; same-letter is not geometrically realizable.** For class-A d=2n+6eps+5-k, n=k+3+t (minus) or n=2(k+2)+t (plus), the exact Z[t,k] sign-cone certificate gives three Pisot-root brackets and beta<d+1 for every k,t>=0, *including* the minus floor t=0 omitted from the original conservative observation. The aligned (x,c,0) swap-seed first y/y run pair has correct symbolic Parikh residual (-1,1,0) but physically disjoint intervals since Lx-Lc=u Ly>Ly. Do not mistake identical child letters, a quotient pair, or an algebraic index pair for an actual overlap or target packet. See docs/class-a-boundary-chamber-2026-10-26.md, kernel/psc/class_a_boundary_signs.mojo and kernel/psc/class_a_boundary_occurrences.mojo. Scope: spectral/typed child filter only; no BH/C4/G1/PSC promotion.

2026-10-26 — **Complete y/y run-pair geometric sieve for the aligned class-A boundary-ray (x,c,0) parent, not for the whole seed graph.** Exact u=d/(beta−1) is in (1,2) for eps=-1; for eps=+1 it is in (2,3) at k=0..3 and (1,2) at k>=4. The separating polynomial 8*f(1+d/2) has exact positive k<=3 or negative k>=4 coefficient-cone proofs. For genuine run indices i,j, a y/y strict child exists iff |j-i-u|<1: possible j-i are {1,2}, {2,3}, {1,2} in those chambers. Same-index y/y was unrealizable, so keep physical geometry and actual ordered occurrences; this does not enumerate first/last or prove BH. Reuses existing exact Q[t,k] and Perron kernels. Locator: docs/class-a-boundary-chamber-2026-10-26.md §run-pair classification; kernel/psc/class_a_boundary_run_pairs.mojo; tests/test_class_a_boundary_chamber.py. Human review pending.

2026-10-26 — **Aligned class-A boundary seed: complete first/run/last outgoing star, not closed carrier.** With r=floor(u), actual children are first/first, first/run j=1..r+1, run/run j-i in {r,r+1}, and run/last i=n-r..n+2 minus or n-r..n+1 plus. The distinction follows from Lc/Ly=1-eps/beta, so copying the minus endpoint to plus is geometrically false. Exact occurrence counts are 2n+4 minus, 2n+3 plus. Independent rational replay checks 56 members / 23,828 pairs. Every successor of T_m=(y,y,-1,1,m) has c-coordinate m+1>=2, outside this star (c<=1); the star is not closed and c itself cannot be a decreasing rank. Remaining symbolic guards for all nine T_m child kinds are explicit. No BH or theorem-status promotion; native/Lean acceptance remains head-specific. Locator: docs/class-a-boundary-child-carrier-2026-10-26.md; kernel/psc/class_a_boundary_children.mojo; evidence/class-a-boundary-children-2026-10-26/probe.json.

2026-10-26 — **Next boundary T_m first/first chamber resolved, not descent.** For actual seed run/run targets, minus admits first/first exactly at m=1,t<=1; plus exactly at m=2,k<=6. Polynomial division/remainder and positive shifted cones prove all k,t; independent exact geometry checks 208 members / 416 choices across t=1/2,k=6/7. Other eight child-kind guards and closure/rank remain open. Locator: docs/class-a-boundary-child-carrier-2026-10-26.md (last section), kernel/psc/class_a_boundary_next_first.mojo.

2026-10-26 — **Lean inventory integration guard.** Adding even an unregistered algebraic helper module changes the generated proof bank and all-source provenance checks. Native boundary certificates passed on 9de8b828, but scoped class-D assembly correctly refused the stale named-proof inventory. Regenerate proof/proof-bank.json and docs/proof-bank.md; do not waive the guard or reinterpret it as a mathematical failure. The bank now inventories 30 named proofs, retaining all existing claim statuses. Locator: tools/make_proof_bank.py; PR #348.

2026-10-26 — **Proof-bank byte-order correction.** The incremental 30-proof inventory had the correct parsed data but ordered two input-digest keys differently from the full generator (Path ordering differs from string ordering for a directory and a same-prefix .lean file). A clean full checkout and the unchanged python tools/make_proof_bank.py regenerate the exact bytes; --check passes. Do not credit parsed JSON equality as generated-artifact byte identity. Locator: PR #348; proof/proof-bank.json.

2026-10-26 — **Complete first/run classification for boundary T_m sources.** Exact identity u-alpha=1+2eps/beta with alpha=beta-(n+3+eps) reduces all chambers to bounded integer ranges: minus T1 j=max(1,t-1)..t+1; plus k<=3 T2 j=1..4-k; plus k>=4 T1 j=k+t+10..min(k+t+13,2k+t+5); other source cases disjoint. The k=4 plus packet is empty and k=5..8 exposes the actual-word upper clip. Polynomial remainder/cone proof and finite all-ordinal replay remain distinct. First/last and six other kinds, global closure and descent remain open. Locator: docs/class-a-boundary-first-run-2026-10-26.md; kernel/psc/class_a_boundary_next_run.mojo; evidence/class-a-boundary-next-run-2026-10-26/probe.json.

2026-10-26 — **First/last boundary T_m guard also complete.** Only plus T1 with 4<=k<=7 has an interior (first,last) child, at actual ordinal pair (0,n+2), target (x,c,1,2,k-9). The margins are B+N=k-7-2/beta and B+N+a+b=k-4+alpha-2/beta>0. All other source chambers violate B<-N. Independent exact replay accepts 64 of 1024 first/last pairs. Six remaining child-kind guards, global closure and descent stay open. Locator: docs/class-a-boundary-first-run-2026-10-26.md (last section); PR #349.

2026-10-26 — **Both boundary T_m sources: complete nine-kind outgoing carrier, exact 50-label union.** The first/run calculation extends by the same alpha bounds to all actual first/run/last pairs. An O(N) canonical carrier covers exactly two run/run strips and bounded endpoint ranges; exact Parikh cancellation gives 50 typed target labels uniformly over all chambers, with actual finite witnesses for all 50. Independent geometry replays 182 members / 133,042 pairs / 6,370 accepted. The union is not claimed closed. Next source U=(x,y,1,2,-3) is uniformly reached on minus by seed (1,2), then T1 (0,t+1). Its descendants and the other image labels, rank and universal BH remain open. Locator: docs/class-a-boundary-tm-carrier-2026-10-26.md; kernel/psc/class_a_boundary_tm_children.mojo; evidence/class-a-boundary-next-run-2026-10-26/tm-probe.json.

2026-10-26 — **Minus boundary U: complete nine-kind outgoing carrier, exact 12-label image, nontrivial four-cycle.** U=(x,y,1,2,-3) has only run/first, run/run, last/first (k+t<=1) and last/run children, exactly 2n-1 ordered occurrences. Full prefix transport and 1<u<2 prove the table; finite independent replay checks 117 members / 61,308 pairs / 2,925 accepted and all 12 target labels. For n>=5 the actual cycle T1 -> U -> R(T1) -> R(U) -> T1 rules out a strict rank decreasing on every child edge, but not existential descent or BH; no closed obstruction is established. Next uniform source V=(y,x,0,-1,2) is reached from U at (d+2,0). Native acceptance remains head-specific. Locator: docs/class-a-boundary-u-carrier-2026-10-26.md; kernel/psc/class_a_boundary_u_children.mojo; evidence/class-a-boundary-u-2026-10-26/probe.json.

2026-10-26 — **Uniform alternative to the U four-cycle has a forced next step.** V=(y,x,0,-1,2), always reached from U at (d+2,0), has only its (n,0) child W=(c,x,0,1,-1). The exact identity beta-a=n+1/beta excludes all other first/run/last kinds, and the full incidence/prefix update gives W, whose shift is 1/beta. The independent oracle checks a further 61,308 V pairs with 117 accepted occurrences. W, rather than V, is now the next unresolved outgoing/target-compatibility case. No BH or status promotion. Locator: docs/class-a-boundary-u-carrier-2026-10-26.md (V section); kernel/psc/class_a_boundary_u_children.mojo.

2026-10-26 — **Local locked Mojo replay is now available; hosted queue and Lean launcher remain separate.** Installing Pixi with TAR_OPTIONS=--no-same-owner avoids the container archive-ownership error without changing repository/runtime pins. Native T_m full-table and endpoint tests, U/V full-pair tests and both drivers pass under locked Mojo 1.1.0.dev2026090805. All 18 TLA expected outcomes pass. The local Lean launcher still fails before compilation; this is not a Lean proof pass, and neither local receipt substitutes for the pending hosted head-specific acceptance. Locator: evidence/class-a-boundary-u-2026-10-26/native-local.txt and formal-local.txt; PR #352.

2026-10-27 — **Boundary continuation stop/go: one-seed coincidence is narrower than BH.** Revisited Akiyama--Lee, Barge--Stimac--Williams and Minervino--Thuswaldner before extending W to a six-step actual minus seed path. Proceed with full child stars and the physical one-seed witness; no every-overlap/internal-space/strict-zipper transfer is supplied. Distinct types with zero Parikh offset are a required false-coincidence control. Locator: docs/class-a-boundary-w-stopgo-2026-10-27.md.

2026-10-27 — **#349 and #352 accepted at exact hosted heads and merged.** #349 a1eb9692 passed native/Python run 40427655699, full Python/Lean/TLA/provenance run 40427655703 and evidence policy; merged as 95ad389a. #352 7540e432 passed native/Python run 40431497735, full Python/Lean/TLA/provenance run 40431497863 and evidence policy; merged as d1d7a1c9. Earlier queued and local Lean-launcher failures remain historical, not current acceptance blockers. Scope remains one-source child carriers; human review pending and no BH/PSC promotion.

2026-10-27 — **Uniform minus six-step physical seed coincidence; cycle has an explicit exit.** Completed all nine child kinds for W/Z/X/Q, exact outgoing union 17, with local locked native 56 members / 93,604 pairs / 3,220 accepted. The aligned seed -> T1 -> U -> V -> W -> Q -> (y,y,0) uses actual indices (1,2),(0,t+1),(d+2,0),(n,0),(1,0),(1,2) for every k,t>=0. Q has both a true y/y coincidence and a zero-offset c/y noncoincidence, so tile type cannot be erased. V->W->Z->X->V exists throughout the chamber, but W->Q exits to coincidence; it is not closed obstruction. A selected seven-state stage rank is scoped to that path only. Next unclassified closure target E=(x,x,0,0,-1); all-source strict-zipper and plus coverage still open. Locator: docs/class-a-boundary-w-carrier-2026-10-27.md; kernel/psc/class_a_boundary_w_children.mojo; evidence/class-a-boundary-w-2026-10-27/probe.json.

2026-10-24 — **Class-B top layer, step 1: carriers are affine in the bounded basis u = 3k+c+y, v = 3k-c, not in class A's.** Class A's grouping (k-intervals at fixed k+c+y and y) finds no affine floor on plus g=1 (q<=26), because every raw offset coordinate grows with q (k ~ q, c ~ 3q, y ~ 6q). The bounded functionals span a rank-2 lattice whose kernel is the growth direction (1,3,-6). Since (k,c,y) -> (u,v,k) is unimodular, k-intervals at fixed (top,bottom,u,v) are lossless. In that basis all six probed lines (plus g=1..4, minus g=1..2) have every residue class affine in q from floors q=9..18 (218-417 rows), with endpoint slopes in {-1,0,1} on plus g=1. Lesson: before declaring a carrier non-affine, search the integer functionals for the bounded ones. Tooling pitfall: `pkill -f PATTERN` inside a command line containing PATTERN killed the issuing shell again. Locators: `docs/class-b-top-layer-stopgo-2026-10-23.md` (step 1), `evidence/class-b-top-layer-labels-2026-10-24/`, `kernel/class_b_top_layer_profile.mojo`.

2026-10-27 — **Class-B top layer, step 2: all 21 fitted rays certify (plus g=1..5, minus g=1..3), with a q-free potential.** Closed form first: with L_y = β(β+1), L = (3β²+(3+3eps−g)β+3eps, (β+1)(β−eps), β(β+1)) and T = (β+1)(uβ − eps·d) − gβk. The k coefficient L_x+3L_c−6L_y is exactly −gβ, and qβ(β+1) = A(β) eliminates q linearly, so class A's Sturm/affine-ray machinery transfers unchanged. Closure passed at the fitted floors on 18 rays. On minus g=3 an affine max/min is undecided at 18/16/17, and closure first accepts at 21/22/20. Descent: the first-hit depth is about |k|/2 + O(1) and independent of q (plus g=1, q=20..42). So X = |k| + b(top,bottom,u,d,sign k) with b the least fixed point of the descent inequality (b ≤ 6, from two graphs per ray) descends symbolically on every ray. It needs no l term, and it avoids the depth-envelope failure recorded on 2026-10-23. Mojo and the independent Python oracle agree on every count; a removed row, a lowered or zero potential and a sub-floor certificate refuse. Not uniform: 466/1017 potential keys conflict across rays, so step 2b (g-uniform) needs another idea. Tooling: from kernel/, `python3` resolves to the pixi interpreter, which has no pytest; use /usr/bin/python3. Locators: `docs/class-b-ray-certificate-2026-10-27.md`, `kernel/psc/class_b_ray_certificate.mojo`, `evidence/class-b-ray-certificate-2026-10-27/`.

2026-10-26 — **#331 negative control, filed late: equal-length same-orientation SP edges need not be identities, even on PIP.** For `0↦12, 1↦01, 2↦120` (det −1, χ = x³−2x²−x+1 irreducible, M³ > 0), `120 = 12·0` gives the reachable initial residual `u=0`, and `0·12 = 01·2` gives the edge `0→2` with `|u|=|v|`, `u≠v`, source letters 0≠1. This rules out the v5-thread SP/integral-residual proof of UD, and with it `UD ⇒ finite BPA`. The proof erred in reading `u·σ(a)=σ(b)·v`, `|u|=|v|` as making σ(a), σ(b) conjugate. UD itself stands, via the defect theorem (manuscript Thm 2.8); do not reopen it. The same audit rules out "minimum-length vertex ⇒ equal-length subcycle" (lengths 1→2→1), "Rauzy-bigram walk ⇒ legal Wⁿ", and finite-word UD as a substitute for bi-infinite recognizability (`{01,12,20}` on `(012)^∞`). The requested Mojo regression is not yet written. The fixture was rechecked by hand on 2026-10-26: matrix, det, χ, M³ and both factorizations agree. Documentation only; no status change. Locator: `docs/psc-v5-thread-salvage-audit-2026-10-23.md` §§B–C.

2026-10-26 — **Theorem E line gate red on main: verdict drift, not refutation.** Scheduled run 40180359004 of `class-b-lines-evidence.yml` on `main@4eb0427d` fails (16 of the first 30 of its 142 jobs), as has every PR run since run 31 (2026-10-20). On class B `(2n, n, n+1)` the builder still reports 76 symbolic vertices, all with an offset-zero descendant, and all 30 members below the floor hitting. But the floor is `q0 = 31`, while `certified_lines()` pins `q0 = 20` with 19 members below it. The line statement survives at the larger floor. Cause not identified; the first red run follows the 2026-10-19 symbolic-line changes. Do not re-pin without a recorded reason. Locator: `docs/completion-ledger-2026-10-26.md` §"CI and governance state", `kernel/symbolic_line_certificate.mojo`.

2026-10-26 — **Correction to the #331 entry above.** The fixture refutes the equal-length identity lemma, which invalidates the SP proof of UD and its derivation of `UD ⇒ finite BPA`. It does not refute the implication. The fixture has finite BPA: `reference/psc_research/bpa.py::build_bpa` on `1→23, 2→12, 3→231` completes with 11 states. Also: the code `{01,12,20}` gives two distinct bi-infinite parsings of `(012)^∞`, with cut sets `2Z` and `1+2Z`, not three; cuts are counted modulo the codeword length. Locator: `kernel/tests/test_sp_equal_length_negative.mojo`, PR #345 review.

2026-10-26 — **Scoped class-A/C ledger claims registered; class-B label rays as evidence.** Three new claims are added to `tools/make_ledger.py` as repository-proved, computer-assisted, human review pending: `ClassABoundaryHittingLowGaps` (A gaps `d<=4`, whole PIP domains), `ClassABoundaryHittingHighGaps` (A gaps `d>=5`, members `n>=5d` only) and `ClassCBoundaryHittingLowGaps` (C gaps `d<=5`). The C claim depends on `DetTwoBoundaryHittingLines`, whose six class-C lines are gaps 1–3. `ClassBTopLayerLabelRays` is a hand-written `evidence` claim guarded by `test_class_b_label_fit.mojo`. None is a premise of `UniversalBoundaryHitting`, and no class-A/C G1 corollary is registered. Caveat: the Theorem E line gate that replays `DetTwoBoundaryHittingLines` is red on main because of pin drift; see the entry above. Locator: `docs/claim-status-and-source-map-2026-09-13.md`, `docs/proof-ladder.md`.

2026-10-26 — **Theorem E line gate: drift root-caused and re-pinned.** The red gate traced to PR #288, commit `7a74eda` ("Clip empty run blocks before affine bound fitting"). The last green run is 17 (`2d1d891`) and the first red one is 18 (`e28854c`, the #288 head). The repair tests a run block's emptiness at its legal endpoints before fitting any bound, so the closure makes different sign reads and the tail floor `q0` moves. It moves in both directions: up on 11 lines, down on 5. On all 16 lines the vertex count and the non-PIP and outside counts are unchanged, PIP-below changes by exactly Δq0, and the `q0`/`q0+5` cross-checks pass. The pins were therefore regenerated from scheduled run 40180359004, with dated corrections under both tables. They also moved out of the driver into `kernel/symbolic_line_pins.txt`, read at run time by `report`/`report_wedge` only. The driver is in the import closure that class-D acceptance froze byte-for-byte (`tools/check_class_d_assembly_evidence.py`), so this one driver edit is rebound by a fresh native plus-chamber replay in a dated packet. Future re-pins touch only the data file. Lesson: a change to the `symbolic_line.mojo` closure must re-run the line workflow and re-pin in the same PR. Correction to the earlier entry: the floor change is not monotone. Locator: `kernel/symbolic_line_pins.txt`, `kernel/symbolic_line_certificate.mojo`, `docs/p1-seed-strength-2026-10-08.md`, `docs/p1b-boundary-hitting-progress-2026-10-08.md`.

2026-10-26 — **Tooling pitfall: some tests are byte-diffed against archived logs.** `class-c-gap-four.yml` diffs the full output of `test_class_c_gap_four.mojo` against `evidence/issue139-ac-gap4-2026-10-22/native-c-tests.log`, and `gap-five-evidence.yml` does the same for its logs. Appending even a `require_claim` receipt line to such a test breaks the archived replay. `ClassCBoundaryHittingLowGaps` therefore names no guard test. The coverage check requires guards only for finite-domain and evidence claims, and the gap-four certificate stays replayed byte-for-byte by its own workflow. Before adding a declaration, grep `.github/workflows` for `diff ../evidence` on that test.

2026-10-27 — **Theorem E re-pin completed; two Theorem W wedges lost coverage.** The 2026-10-26 re-pin of 16 lines was incomplete: it came from the first page of a failed-jobs listing. The full PR #345 run 40427511787 (head `7a36f91`, 142 jobs) had 74 pin mismatches, every one from the same PR #288 change and none of another kind. 71 lines (3 class B, 9 classes A/D, 59 norm-mode boundary lines) and the wedge `D 3 2 1 4 2 1 5 3 2` (`b0` 7 → 1) re-pin under the same rule: vertices and non-PIP/outside counts unchanged, PIP-below moving by exactly Δq0, and every boundary line of a moved wedge already pinned. A guard script refused the other two wedges. `D -1 2 1 -2 2 1 -4 3 2` (`a0` 3 → 7) and `D 4 1 3 5 1 3 7 1 4` (`b0` 7 → 31) now need 4 and 24 boundary lines that were never certified. Their pins are left unchanged and stay red. The 28 lines run once in a temporary probe workflow and are pinned from its logs. Until then, the current code reproduces Theorem W and Corollary W1 only outside those strips. Lesson: a floor can rise, and a wedge re-pin is sound only if its new boundary lines are themselves pinned. Re-pin from the complete job list, never a single page. Locator: `kernel/symbolic_line_pins.txt`, `.github/workflows/theorem-w-boundary-probe.yml`, `docs/p1b-boundary-hitting-progress-2026-10-08.md` §4b.

2026-10-27 — **Class-B step 2b: the g-uniform carrier is the forward closure of the strict core, not a fit of the reachable graph (exploratory, floating point).** The reachable core rows (|u|<=3, |k|<=2, |d|<=6; l-slope (0,0)) change with g (106..51 rows at plus g=1..10) independently of residue, so reachable-graph tables cannot be g-uniform. C_q = closure(strict core) contains every native graph tested (plus g=1,6,8,10, minus g=3) and every C_q state reaches offset zero (1,188 members); its core strictness pattern is constant past the asymptotic threshold g=9 on both branches. With C_q, minus has a candidate low/middle/high cover for g>=12 (middle 6<=r<=g-6, one 529-row table on g=12..14); plus has an anchored turbulent band around (q+5) mod g = 0 and no middle regime for g<=16. The window strict set {|u|<=5,|d|<=8} is not closed (negative control). Probe pitfall: a slice (t,b,u,d) can hold several k-intervals; keying rows by the slice alone silently drops intervals. Note: docs/class-b-gap-uniformity-stopgo-2026-10-27.md; oracles/python/class_b_core_closure.py, class_b_regime_probe.py.

2026-10-27 — **Follow-up to the step-2b entry above: both regime stop conditions checked, not met.** Extended to plus g<=20 and minus g<=16 (1,818 core-closure members). The minus middle table (6<=r<=g-6, 529 rows) holds on 15 rays g=12..16, and plus has a middle regime 2<=r<=g-14 (529 rows, 15 rays g=16..20) with the same 529 slices. Candidate covers: minus g>=12 (low j<=5, middle, high j<=5), plus g>=16 (low j<=1, middle, high j<=13); leftover gaps plus 6..15, minus 4..11. Still floating point and finite. Note: docs/class-b-gap-uniformity-stopgo-2026-10-27.md.

2026-10-27 — **Class-B leftover gaps: step 2's ray certificate certifies plus g=6..10 and minus g=4..7 unchanged (62 rays, 83 in all).** Carriers fitted from 627 exact native label sets, potentials as in step 2. 27 rays certify at the fitted floor; 35 refuse there (19 UNDECIDED affine max/min, 16 NO DESCENT) and certify one period higher (two minus rays, g=5,6 r=1, two periods). Native and Python counts identical on all 83 rays; 166 replays and 83 below-floor graph checks pass. Counting pitfall: plus 6..10 and minus 4..7 are 40+22=62 rays, not 56; a first per-index run missed minus g=7 r=1..6. Note: docs/class-b-gap-rays-2026-10-27.md; packet evidence/class-b-gap-rays-2026-10-27/.

2026-10-27 — **Correction to the leftover-gap entry above:** the packet holds 544 native label sets, not 627; the earlier copy swept in 83 `.labels.err` stubs (members outside the open top layer), since removed. The refit from the 544 labels still reproduces carriers.json.

2026-10-27 — **Continuation acceptance distinction and E/H stop/go.** #355 is observed merged as 316ebdc5, with native/Python run 40474073394 successful but fresh Lean/full Python/TLA still queued at inspection; no formal pass is inferred from merge status. Reuse its three-source stop/go for complete E/H1/H2 stars and their actual orientation reversals, with at-most-two-step physical coincidence exits and no global coverage claim. Locator: docs/class-a-boundary-e-stopgo-2026-10-27.md.

2026-10-27 — **Complete six oriented E/H packets with uniform <=2-step coincidence exits.** E+=(x,x,0,0,1), E-=R(E+), H1=(x,y,0,-1,1), H2=(x,y,0,-1,2) and both H reversals have complete nine-kind child tables. Exactly 29 typed labels occur in every member; counts are 2d+1, n+2, 2n+3 per oriented family. The inherited exact bound alpha+1/beta<1 excludes a false extra H2 run/last child even when word-legal. Native replay: 56 members / 148,288 pairs / 7,112 accepted / 560 selected edges. Independent replay: 117 members / 542,880 pairs / 19,422 accepted / 1,170 selected edges. Actual orientation is retained, zero-offset unequal-type edges are retained as edges, and the rank is only on the selected seven-state packet. Next unclassified source H3=(x,y,0,-1,3) from E- at (0,n+3); no global closure or BH/PSC promotion. Locator: docs/class-a-boundary-e-carrier-2026-10-27.md; kernel/psc/class_a_boundary_e_children.mojo; evidence/class-a-boundary-e-2026-10-27/probe.json.

2026-10-27 — **#357 ledger merge reconciliation.** Concurrent class-B and class-A E/H work appended independent entries to the same ledger. Preserve the complete main ledger, including its historical class-A audit addition, as the prefix and retain both E/H entries unchanged after it; no research calculation, theorem status, source kernel or archived receipt changes. Locator: PR #357 conflict-resolution merge of main c7cbee0e.

2026-10-27 — **H3 continuation stop/go.** Reuse the three-source actual-overlap review for H3 and its selected intermediates, with an exact alpha=1/2 polynomial split and at-most-five-step physical exits. Proceed without an all-source or internal-space transfer; retain the two small diagonal exceptions as explicit negative controls. Locator: docs/class-a-boundary-h3-stopgo-2026-10-27.md.

2026-10-27 — **H3 exact half-chamber and eight-source five-step exits.** The cleared separator 8f(n+5/2)=4k^2+20k-4t^2-24t+5 has alpha>1/2 exactly when t>k or t=k>=2; the two smaller diagonal points have the opposite sign and no equality occurs. Complete H3/J/K/L stars and their true reversals yield a 76-label union. The uniform path uses (2n+2,0),(t+2,0),(k+1,0),(0,n-2),(1,2) to typed y/y zero. Native: 56 members / 132,384 pairs / 5,824 accepted / 1,568 selected edges. Independent oracle: 117 members / 490,464 pairs / 15,912 accepted / 3,276 selected edges. The rank is restricted to eleven selected labels, and L also returns to H3, so no closed obstruction follows. Next packet P=(y,y,-1,-1,3) is reached from L at (1,n); no all-source, plus, internal-space or BH/PSC promotion. Locator: docs/class-a-boundary-h3-carrier-2026-10-27.md; kernel/psc/class_a_boundary_h3_children.mojo; evidence/class-a-boundary-h3-2026-10-27/probe.json.

2026-10-27 — **#357 reconciliation with accepted main #345.** Preserve main 78ace27 in full, including scoped claim-status updates and generated proof/ledger surfaces, then append all unchanged E/H and H3 findings. Only the shared side-notes ledger conflicted; the physical child kernels and archived receipts are unchanged. Fresh exact-head acceptance remains required. Locator: PR #357.

2026-10-27 — **Boundary stack reconciliation after class-B #363.** Preserve main e2dc81f in full, including its finite class-B ray evidence and generated proof bank, then retain all unchanged E/H and H3 findings. Only the shared ledger conflicted. No new theorem status or child-kernel changes; fresh head-specific hosted validation remains required. Locator: PR #357.

2026-10-27 — **Dependency validation reconciled after stacked integration.** #355 head eaff85f1 now has successful native/Python, full Python, Lean, TLA, provenance and evidence-policy receipts; Lean job 122087859542 reports 173 declarations / 117 theorems, all 34 named proofs reached. Earlier queued receipts remain historical. #358 was merged into #357's branch as 053572e8, not main; #357's current head therefore includes both E/H and H3 work. Its fresh native/formal/Python gates were still queued at this inspection, with no pass inferred from the stacked merge. Human review remains pending and theorem statuses unchanged. Locator: PRs #355, #357, #358.

2026-10-27 — **P continuation stop/go and precise clipped-occurrence controls.** Reuse the three-source physical-overlap review for ten oriented P/Pplus/A2h/B2h/D packets. At k=0, P's proposed (1,t+3) run/run shortcut actually ends at a last c, producing a y/c child rather than B2h; the ordinal exists, so rejecting it as unavailable would itself be wrong. At n=3, A2h's (3,1) is a genuine zero-offset c/y half-coincidence, not typed y/y C. Certify k>=1 and n>=4 on shifted parameter cones; the indexed-prefix kernel correctly refuses an unshifted all-cone RUN(3). Locator: docs/class-a-boundary-p-stopgo-2026-10-27.md; docs/class-a-boundary-p-carrier-2026-10-27.md.

2026-10-27 — **Ten complete oriented P stars and uniform <=5-step typed exits.** All nine first/run/last kinds of P/Pplus/A2h/B2h/D and their true reversals have an exact 51-label chamber-wide outgoing union, with counts 2k+4, 2t+4, n+2, 2 and 2n+3 per orientation. P has a uniform alternative through D->K->L->H1->C, including k=0; k>=1 has a shorter B2h exit. A2h reaches C in one step at n>=4; its sole n=3 exception has a four-step typed path through F=(y,x,-1,0,2) and B2h. Native replay: 56 members / 86,632 pairs / 6,328 accepted / 1,490 selected edges. Independent replay: 117 members / 325,416 pairs / 17,316 accepted / 3,084 selected edges. L->P->D->K->L is a genuine all-chamber cycle with an H1 exit, not a closed obstruction. Next unclassified target E2=(x,x,0,0,2) is A2h's actual first/first child throughout the chamber. No forward closure, full F star, plus/strict-zipper/internal-space transfer or BH/PSC promotion. Locator: docs/class-a-boundary-p-carrier-2026-10-27.md; kernel/psc/class_a_boundary_p_children.mojo; evidence/class-a-boundary-p-2026-10-27/probe.json.

2026-10-27 — **#359 stacked-parent reconciliation.** Incorporate #357 fe733fc (including accepted main 78ace27 and all unchanged E/H and H3 work), retain its complete ledger as prefix, then append the three unchanged P entries. No kernel, archived receipt or theorem-status changes from this reconciliation. Locator: PR #359.

2026-10-27 — **PR #359 stack reconciliation after #363.** Preserve the updated parent ledger as prefix, then retain this increment's unchanged findings. Canonical kernels, archived receipts and theorem scopes unchanged. Exact-head hosted acceptance remains required.

2026-10-27 — **Reconciliation acceptance terminology clarified.** #357 now has ledger reconciliation head fe733fc and #359 head cd2a309, preserving main 78ace27 plus all unchanged carrier work. In the earlier reconciliation entry, "accepted main #345" identifies integrated main, not a new assertion that #345's latest hosted checks passed; its head 7549964 also has queued hosted checks. No hosted proof acceptance follows from merge status. Main's 124 existing governed claims and 34 named proofs are retained; this continuation promotes none. Locator: PRs #345, #357, #359.

2026-10-27 — **E2 continuation stop/go: last x is a real occurrence, not a fictitious run.** Reuse the three-source actual-overlap review for complete E2/Dxx stars and real reversals. At t=0, E2's proposed run/first ordinal 2n+3 equals A+1, the actual LAST x. Complete classification gives a sole child Dxx, whose valid K exit resolves the endpoint. At t>=1 the run/first J exit exists. Proceed with the inherited exact half-chamber separator and shifted parameter cones, without every-overlap/internal-space transfer. Locator: docs/class-a-boundary-e2-stopgo-2026-10-27.md.

2026-10-27 — **E2 and Dxx: complete four oriented stars, 46-label union and five-step typed exits.** Counts are 2t+1 and 4n+3 per orientation throughout the minus chamber. E2->J->K->L->H1->C applies at t>=1; E2->Dxx->K->L->H1->C at t=0, with Dxx's own four-step suffix uniform. Native: 56 members / 164,192 word pairs / 5,376 accepted / 1,008 selected edges. Independent replay: 117 members / 595,296 pairs / 14,976 accepted / 2,106 selected edges. Dxx(t+3,1) gives a disjoint y/y label (0,-2,4), whereas its actual last/run child at (A+1,2n+1) has the same offset and x/y types and is interior. That H4=(x,y,0,-2,4) is the next uniform unclassified source. For k>=2 an exact six-cycle through L/P/A2h returns to E2, with L's H1 exit, hence no closed obstruction. The 46-label union is not proved forward closed; no universal BH, plus, strict-zipper, internal-space or PSC promotion. Locator: docs/class-a-boundary-e2-carrier-2026-10-27.md; kernel/psc/class_a_boundary_e2_children.mojo; evidence/class-a-boundary-e2-2026-10-27/probe.json.

2026-10-27 — **PR #360 stack reconciliation after #363.** Preserve the updated parent ledger as prefix, then retain this increment's unchanged findings. Canonical kernels, archived receipts and theorem scopes unchanged. Exact-head hosted acceptance remains required.

2026-10-27 — **H4 nine-kind literal child classification, not a BH carrier.** In the minus class-A boundary k,t>=0, Dxx's real child H4=(x,y,0,-2,4) has B=2beta-2=2n+2+2alpha and exactly 2t+5 strict child occurrences. Exact alpha>1/2 iff t>k or t=k>=2 determines which two y/y run strips survive, while the whole-child count stays invariant. The union is 13 typed labels, all inside #360's E2/Dxx 46-label image. The low t=0 and diagonal alpha chambers are explicit negative controls; no other successor closure, productive descent or seedwise BH follows. Source: docs/class-a-boundary-h4-2026-10-27.md, kernel/psc/class_a_boundary_h4_children.mojo and the independent actual-word oracle. Unreviewed theorem package pending exact-head CI, no governed promotion.

2026-10-27 — **H4 has a uniform actual five-edge typed-coincidence exit, but its outgoing image is not closed.** For every minus class-A boundary k,t>=0, H4=(x,y,0,-2,4) has strict child at top run (2n+1), bottom first 0 equal to J=(y,x,1,2,-4); the accepted J->K->L->H1->C chain uses (t+2,0),(k+1,0),(0,n-2),(1,2), ending at typed y/y zero shift. The stage rank 5..0 is valid *only* on this selected six-label path. It does not give productivity of every H4 child, the 13-label or E2 46-label union, uniform #139 BH, C4/G1 or PSC. The exact all-parameter source guard and the inherited J suffix are in docs/class-a-boundary-h4-2026-10-27.md §constructive exit and kernel/psc/class_a_boundary_h4_children.mojo. Independent validation pending.

2026-10-27 — **PR #361 stack reconciliation after #363.** Preserve the updated parent ledger as prefix, then retain this increment's unchanged findings. Canonical kernels, archived receipts and theorem scopes unchanged. Exact-head hosted acceptance remains required.

2026-10-27 — **H5 conditional actual-word typed coincidence: k=0/1/≥2 split.** The H4 last/run child H5=(x,y,2,2,-5) exists with literal (A+1,t+2) for every minus class-A boundary member k,t>=0. It has physical shift 1+2alpha (strictly interior since alpha+h<1) and an exact selected y/y coincidence exit: k=0 via (A+1,0) to (x,x,0,-3,4), then (t+1,0) to (y,x,0,1,-1), then (2,1) to C; k=1 via (A+1,0) to (x,x,0,-3,3) then (1,4) to C; k>=2 via top RUN i=2d-n+3=A+2-k, bottom FIRST 0 to (y,x,0,-3,3), then (1,4) to C. **False uniform RUN guard:** i=A+2-k is outside the image for k=0 and is LAST for k=1; only k>=2 is a true RUN. Preserve this refusal, exact Parikh verification and strict physical overlap. H5 has an existential depth≤3 exit, not a complete outgoing star, closed H4 image, all-state BH or PSC. Locator docs/class-a-boundary-h5-exit-2026-10-27.md and kernel/psc/class_a_boundary_h5_exit.mojo. Human review pending.

2026-10-27 — **PR #362 stack reconciliation after #363.** Preserve the updated parent ledger as prefix, then retain this increment's unchanged findings. Canonical kernels, archived receipts and theorem scopes unchanged. Exact-head hosted acceptance remains required.

2026-10-27 — **Repaired #354 is merged into its historical U parent, not fresh hosted acceptance.** Observe the documentation repair at 89675ac merged into the old U branch while its new Python, native, Lean/TLA and provenance checks remain queued. Do not infer a proof pass from that merge. Reconcile the active #357/#359/#360/#361/#362 stack with main e2dc81f, preserving all independent class-B evidence and all class-A kernels and archived receipts. New heads are f969772, ac4b586, e779f0a, 15b99b4, db40f96; exact-head hosted gates remain required. Local inherited H4 and H5 native tests pass. Locator: PRs #354, #357, #359–#362.

2026-10-27 — **H5 complete-star stop/go and exact t separator.** Reuse the same three-source actual-overlap review after #362's selected exit. With eta=alpha-4/beta, the exact identity beta^2*eta=(t-1)*beta-2 proves eta<0 at t=0,1, eta>0 at t>=2, and no equality. In particular t=1 gives -2, not zero. Proceed with all nine child kinds and real reversals, preserving conditional occurrence bounds and no global-transfer implication. Locator: docs/class-a-boundary-h5-children-stopgo-2026-10-27.md.

2026-10-27 — **H5 complete oriented child stars: exactly 2k+1 occurrences and 30 chamber-union labels.** RF, RR, LF and LR are the only strict kinds; the exact eta split controls adjacent run strips and k=3's last/first endpoint. Native: 56 members / 33,096 pairs / 896 accepted / 238 selected path edges. Independent literal-prefix/Fraction replay: 117 members / 122,616 pairs / 3,042 accepted / 486 selected edges. Every target label has an actual witness, and the original k=0/1/at-least-2 selected typed exit is verified under actual reversal. A wrong interior target inside the image still fails full Parikh transport. Next explicit unclassified source F=(x,y,1,-3,3) is H5's LR(A+1,k) child only when k>=1; j=0 is not a run at k=0. The 30-label image is not proved forward closed. All-source strict-zipper, plus, target-aware BH and non-unit internal-space gaps remain; no BH/PSC or governed-status promotion. Locator: docs/class-a-boundary-h5-children-2026-10-27.md; kernel/psc/class_a_boundary_h5_children.mojo; evidence/class-a-boundary-h5-children-2026-10-27/probe.json.

2026-10-27 — **F continuation stop/go: all first choices is still narrower than forward closure.** Reuse the three-source actual-overlap review for F=(x,y,1,-3,3) and its three genuine children. Preserve H5->F ancestry only at k>=1; j=0 is FIRST x, not RUN y. Proceed with complete eight oriented F/Z/E3/G2 stars and typed tails for every direct F child, without an all-source or non-unit transfer. Locator: docs/class-a-boundary-f-stopgo-2026-10-27.md.

2026-10-27 — **F has three genuine children, all with uniformly bounded typed tails; a true two-cycle survives.** F children are Z at (A,0), R(E3) at (A+1,0), G2 at (A+1,1). All eight source orientations have complete nine-kind tables with counts 3, 2k+6, 2A-2k-1, 2k+5 and a 64-label chamber-wide outgoing union. Every direct F child admits a typed C tail within three steps; a full walk through any first choice is at most four. Native: 56 members / 181,384 pairs / 7,616 accepted / 1,232 selected source-path edges plus 1,232 direct-child exit-walk edges. Independent replay: 117 members / 665,496 pairs / 20,826 accepted / 2,574 plus 2,574 walk edges. The genuine cycle F->G2->F uses (A+1,1),(A+1,k+2) throughout the chamber; N-(k+2)=t proves the return is a real run, even at t=0. G2 has its G->C exit, so the cycle is not closed. Its return increases the selected rank, ruling out an all-edge decrease. Next P3=(x,y,1,3,-4) is E3's actual (A+1,A-k-1) child with shift 1+w<a. Its full star and the 64-label forward closure remain open; no BH/PSC or governed-status promotion. Locator: docs/class-a-boundary-f-carrier-2026-10-27.md; kernel/psc/class_a_boundary_f_children.mojo; evidence/class-a-boundary-f-2026-10-27/probe.json.

2026-10-28 — **Class C, gaps d>=6: the tail is frozen (finite profile; go for one graph per sign).** For (n+d, n, n−d+eps) the complete swap-seed graph has **the same** label set for every gap 5..30 and every n from the onset 4d (plus) or 4d+4 (minus) to 24 beyond. That is 650 members per sign, with 196 labels (77 typed rows) on plus and 214 labels (81 rows) on minus. The gap-5 note's per-line tail counts are the d=5 case; equality across gaps is new. The first PIP members are n = 2d−5 (plus) and 2d+1 (minus); the members just below are refused by screening. Strip: the diagonals n = 4d−j become constant in d past a j-dependent floor. On plus, the middle band 10<=j<=16 is a second frozen set (280 labels, 21 members at d=20,25,30); near the domain edge the counts grow by about 150 per gap. χ = A(t) − n t(t−1), with A(t) = t(t−1)(t−2) + (d−eps)t(t−3) − 2eps, so n eliminates linearly as in class B; on the tail u = d/β ≲ 1/3 gives a compact Bernstein box. Decision: go for a frozen-tail certificate (one finite labelled graph per sign, all (n,d) on the tail cone); redirect the strip to a later stop/go. Finite observation only; no claim changes. Locators: docs/class-c-gap-uniformity-stopgo-2026-10-28.md, kernel/class_c_gap_profile.mojo, evidence/class-c-gap-profile-2026-10-28/.

2026-10-28 — **Theorem T_C: class-C BH on the whole frozen tail, every gap d>=6 (d>=6, n>=4d plus; n>=4d+4 minus), label set exactly the profile's F_eps (196/214).** The class-C tail is a two-parameter cone of the existing engine psc.symbolic_cone (s=(d,m), n=4d+c+m, runs affine), so the (h,u) Bernstein box planned at stop/go was not needed: certified region signs plus Perron brackets from beta = r + 2(n + (n+d)/(beta-2))/(beta-1) do it unchanged. The shift-0 and shift-1 cones refuse because an intermediate run-clip sign at beta flips inside the region (at d=6: -m t^2+(3m+18)t-(2m+36), positive at m=0, negative for m>=1) while the label set does not; the cover takes the cone d>=8,m>=2, gap lines d=6,7 (m>=2), diagonals m=0,1 (d>=8) and 4 exact members. Finite observations worth not recomputing: the below-onset diagonals n=4d-1 (plus) and n=4d+3 (minus) also certify uniformly for d>=8, with different sets of 198 and 216 labels, which suggests diagonal-by-diagonal certification for the strip. Prototype pitfall: a swapped (d,n) unpacking produced 1500 phantom closure violations. Locators: docs/class-c-tail-theorem-2026-10-28.md, kernel/psc/class_c_tail_certificate.mojo, evidence/class-c-tail-theorem-2026-10-28/.

2026-10-28 — **Retired route: affine-in-q piecewise ranks on symbolic edges for class B's top layer (closed PR #369, superseded by Theorems A_B/B_B).** In parallel with step 2, a different rank class was built and conditionally certified on the same 21 rays (plus g=1..5, minus g=1..3). Pieces were cut at every edge-domain endpoint of k' = s − k + Δx, Δx ∈ {−1,0,1} (Lemma 4's k' = u − k + dx, read as a map on labels). Each segment got one potential X = a·q + b·k + c, chosen by an LP/MILP proposal and checked exactly at polyhedron vertices and recession rays. It was conditional on carrier inclusion and actual edges, which A_B/B_B prove, and B_B's |k| + b is far tighter: here |b| saturated ±60, and max X was 3,008 against depth 30 at plus g=1, q=48. Do not re-spend cycles on it. Findings worth keeping: (i) one affine potential per carrier interval cannot exist on long intervals, because depth is V-shaped in k and each wing descends along a different edge; a 0/1 MILP over 4,953 edge choices on plus g=1 found nothing in 15 min. That is the negative counterpart of B_B's |k| term. (ii) On minus, this route's floors sit one or two periods above B_B's (16, 20/19, 24/22/23 versus 15, 18/17, 21/22/20): segments empty at the lower floors, not geometry. (iii) Tooling: a Mojo checker that parses certificate text must bound every parsed value, header included, not only coefficients; an unbounded gap/q0 let a·q0 wrap in 64-bit Int and pass a negative potential, which the unbounded-int Python oracle caught. (iv) Tooling: without Pixi, `pip install --index-url https://whl.modular.com/nightly/simple/ --extra-index-url https://pypi.org/simple mojo==1.1.0.dev2026090805 max==26.6.0.dev2026090805` into a venv reproduces the lock pin and runs all 126 kernel test files; parallel_fold needs `max`. (v) A conflicted PR runs no pull_request workflow, so new path-filtered gates are silently absent until the conflict is resolved. Locator: closed PR #369 (head 67c4b6d; its packet is evidence/class-b-rank-certificate-2026-10-27/ on that head).

2026-10-29 — **Class-C lower strip: exact PIP domain, a middle cone and four top layers.** For every d>=6 the exact domain starts are n>=2d-5 (plus) and n>=2d+1 (minus): chi(1)=-2d, chi(-1)=-2(n-2d+3eps+3), chi(2)=-2(n+d), and chi(-2)<0 exclude rational roots; quadratic Schur/Jury at beta>2 proves the domain, with chi(-1)=0 one below. Both signs certify BH on 3d+16<=n<=4d-16 (280/250 constant labels, direct coefficient signs). Eight diagonal certificates at d>=12 plus 48 exact end members certify all four layers below T_C for every d>=6 (plus c=-4..-1, minus c=0..3). All 32 residual members at d=6 certify; its plus domain start has 2,432 labels, so frozen-tail extrapolation fails sharply. The independent literal-prefix/Fraction oracle checks 122 complete graphs; the exact Routh oracle has 13,432 decisions agreeing with the domain and 20 explicit refusals below it. The unchanged cone engine is source-audited, not independently human reviewed. Remaining d>=7 strips and the realization/non-unit spectral firewalls stay open. Locator: docs/class-c-lower-strip-2026-10-29.md; kernel/psc/class_c_lower_strip.mojo; evidence/class-c-lower-strip-2026-10-29/.

2026-10-29 — **Bi-injective spike ownership repair, independent of Theorem T_C.** On main 91db5726, the pinned Mojo 1.1.0.dev2026090805 rejects the implicit `bounded.graph` copy at driver line 93; the regression importing and calling the real driver fails there too. Explicit `.copy()` preserves states, adjacency and metadata, admits independent nested mutation, and retains both state/length cap refusals. The repaired finite scan reports 2,958 eligible / 2,064 primitive / 330 complete / 1,734 length-capped specimens; 360 closed components split A=288, B=48, C=24, with all 48 B witnesses reducible. Capped specimens remain inconclusive. Replay from kernel/: `pixi run mojo run -I . tests/test_endpoint_sign_spike.mojo`; its existing workflow step runs the regression, and the workflow additionally watches the driver path. Historical class-D acceptance permits added trigger paths, but freezes workflow steps, so the regression uses the existing endpoint-test entry point without changing accepted steps or evidence. No theorem, archived evidence or claim status changes. Locators: kernel/biinjective_sign_spike.mojo; kernel/tests/test_biinjective_sign_spike.mojo; PR #384 comment 6488000650.

2026-10-29 — **Class-C slope-three cover: upper gap closed, remaining strip has one upper edge per sign.** Unchanged cone certifiers prove plus 3d+4<=n<=4d-16 (280 labels) and minus 3d+8<=n<=4d-16 (250). Separate minus lines n=3d+6,7 certify at d>=24. Twenty-six n-4d diagonals and 414 exact end members d=6..23 join these to #390's top layers and T_C, yielding BH for every d>=6 above n=3d+4 plus / 3d+6 minus. Five of eight corner proposals refuse: ten native Sturm–Tarski reads and an independent Fraction oracle prove actual sign changes of their intermediate clipping comparisons, including minus (6,16), despite 250-label endpoint graphs. Equal counts also fail as a proxy: plus c=-8 and -9 both have 282 labels with different sets. Independent replay checks 547 complete graphs, all finite label rows/depths and ten refusal signs. Remaining d>=7 is plus 2d-5<=n<=3d+3, minus 2d+1<=n<=3d+5. No PSC/PDS, governed-status or human-review promotion; inherited hosted checks were still queued on inspection. Locators: docs/class-c-slope-three-2026-10-29.md; kernel/psc/class_c_slope_three.mojo; evidence/class-c-slope-three-2026-10-29/.
