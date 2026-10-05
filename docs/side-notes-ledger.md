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

