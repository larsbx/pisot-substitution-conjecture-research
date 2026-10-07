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
