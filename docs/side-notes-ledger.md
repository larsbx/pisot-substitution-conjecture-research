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

## 7. Review outcomes

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

