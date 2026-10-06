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

## 2. Redirected routes (no lever there; see the decision)

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
