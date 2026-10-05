# Documentation index

This directory separates live proof status, source provenance, mathematical
exposition, exact finite certificates, and historical snapshots. Start with
the section matching the question you are asking.

For definitions and implementation authority, use the generated
[`mathematical-object-catalogue.md`](mathematical-object-catalogue.md). Its
single structured source is `catalogues/mathematical_objects.toml`; edit the
TOML and regenerate rather than hand-editing the Markdown.

## What the 2026-10-05 results establish

Five theorems were proved on 2026-10-05, each with an exact certificate. They
are stated here positively, because each note's own limits section is
deliberately long and should not be mistaken for the result.

| Result | What it establishes | Where |
| --- | --- | --- |
| **Proposition LC** | The leftmost child is a *function*, so the obstructions to `CU` are exactly the terminal cycles of that function — and every one of them is a **prefix-vs-interior periodic pair**: a prefix occurrence `sigma^r(i) = i U` on one side, an interior occurrence `sigma^r(j) = Q j V` on the other, offset `w_0 = (I − M^r)^{-1} ab(Q)`. The half-degenerate companion of Theorem B. Verified on **10,584 / 10,584** terminal cycles of all 4,554 corpus specimens, none capped, none failing | [`p1b-leftmost-chain-periodic-pair-2026-10-05.md`](p1b-leftmost-chain-periodic-pair-2026-10-05.md) |
| **Corollary LC4** | Those cycles come in **mirror pairs** of opposite offset sign, so their number is always even. Confirmed on all 210 catch-up-free specimens (counts 2, 4, 6, 8, 10 — never odd) | same, §8a |
| **Corollary LC5** | A box graph with **no** terminal leftmost cycle has `Z(s) = ∅` for every seed, so finiteness holds for that substitution. **Covers 1,794 of the 4,554 corpus specimens** by a certificate needing only the leftmost function — one walk per vertex, no closure analysis, no depth bound | same, §8a |
| **Theorem C** | #138's aligned branch has **one** surviving obligation, not two: passing to `sigma^2` collapses the fixed-edge cases (i) and (ii) and the alternating-E template onto the single case where the first-letter map fixes both letters of a bad edge. Every hypothesis transfers. Certified on **36 / 36** viable endpoint/good-edge placements | [`p1a-template-collapse-2026-10-05.md`](p1a-template-collapse-2026-10-05.md) |
| **Proposition A + Corollary C3** | The surviving obligation A1′ is the **residual** half of all-pairs strong coincidence, so it holds with zero failures on all **408,798** PIP specimens already censused; and on the catch-up-free class — all 210 corpus members — **A1′ and T2 are the same boundary-hitting statement**, so #138's aligned branch and #139's strict-zipper branch converge there | [`p1a-a1-prime-2026-10-05.md`](p1a-a1-prime-2026-10-05.md) |
| **Lemma D0 + Proposition D** | On that class the surviving template is an **explicit three-parameter normal form**: the odd letter set is exactly the bad edge, forcing `sigma(x) = x y^p s_x`, `sigma(c) = c y^q s_c`, `sigma(y) = t y^r s_y`. The 18 catch-up-free corpus specimens with one odd letter cannot carry the template at all; the other two templates force a length-one image. `|O| <= 2` because all-odd would make every image length two, hence the Perron root the rational number 2 | same, §3a |

Two redirects came with them, and are worth as much as the theorems. The
`CU` / one-tile route **cannot** reach #139: by Proposition LC its obstructions
are pairs whose centre is a vertex of one tiling and interior to the other,
hence never a common vertex, so they are forced, abundant and harmless — 10,584
of them sit on a corpus where finiteness holds throughout. #139 effort belongs
on the interior-vs-interior pairs of Theorem B. And A1′ is **not** a corollary
of the Barge–Diamond import: that theorem produces one of `d(d-1)/2` pairs,
which is the only pair when `d = 2` and is why the two-letter case is settled.

None of this proves #84, #138, #139, G1b-2, G1 for the family, or PSC. Each
note's final section states its own limits.

## Current status

0. `side-notes-ledger.md` — live, append-only record of side findings:
   refuted mechanisms, redirected routes, specimens settled by the literature,
   withdrawn figures, finite observations and tooling pitfalls. Read it
   before starting a new mechanism, census or route (`AGENTS.md`).

1. `audit-2026-10-04.md` — latest status audit, after the overlap-depth routes
   and the `PDS ⇒ G1` promotion. It re-derives Propositions 5.46/5.47 and
   Theorem B, confirms the realization firewall holds, and reproduces the
   cube-image bounds exactly. **Its findings describe the audited baseline
   `b661f50` and most were applied in the same change; §A.1 is the resolved
   list.** Resolved there: the strict-zipper note's header now records what
   depends on it, the four 2026-10-04 claims now have prose surfaces that
   governance checks, and `PDS ⇒ G1` with the seedwise bridge is stated on
   `README.md`, the conjecture ledger, the proof ladder, the architecture note
   and the claim/source map — and, since 2026-10-05, on the live research
   roadmap, which that change had missed. The 2026-10-05 follow-up also fixed
   the two inherited documentation defects of §D.6: the three manuscript
   statements tagged `\Status{Theorem}, conditional only on its hypothesis`
   now carry `\Status{Conditional}` with their open hypothesis named, as the
   vocabulary and every repository surface already said, and
   `verification-architecture.md` §7 now gives the overlap-productivity
   frontier instead of calling factorization the deepest gap. Two findings were
   retracted as wrong on inspection (§§D.2, D.4); the independent 2026-10-04
   review that §D.2 looked for is recorded in `side-notes-ledger.md` §7, and
   the closure gap §D.4 described is closed — Theorem R, Proposition F and
   Theorem B are ledger nodes since 2026-10-05, so `PDSImpliesRepoG1` requires
   its repository inputs and not only the import. What still stands is the rest
   of §D.6 — `main` unprotected with no enforced status check, and the 24,486-
   and 135,990-specimen PPVC runs outside CI — plus one deliberate deferral:
   the eleven generated claim bindings still target the frozen 2026-09-14
   weekly snapshot.
2. `audit-2026-09-27.md` — status/provenance audit, now carrying a 2026-10-01
   resolution note: the PSC-closed premise was withdrawn, PSC remains open,
   #84/#138 are live theorem issues again, and #153 is resolved conservatively.
   The audit also records the adelic/trim frontier and the Markdown source
   corruption repaired by the current maintenance work.
2. `research-roadmap-2026-09-21.md` — live completion roadmap. Its
   2026-10-02 synchronization includes the fixed-edge/alternating-E aligned
   normal form, strict-zipper M-adic carry stop result, conditional G1 routes,
   and complete finite separation evidence; the open gates remain open.
3. `p1-two-route-map-2026-10-01.md` — current attack map joining the aligned
   and strict-zipper routes at offset zero and identifying the next reviewable
   theorem targets.
4. `p1b-strict-zipper-literature-gate-2026-09-21.md` — completed #139
   literature transfer audit, non-unit hypothesis firewall, and exact open
   adelic periodic-offset hitting obligation.
5. `completion-ledger-2026-10-02.md` — latest merged weekly completion
   snapshot, refreshed to `main@ff9e5d3`; mathematical/evidence additions
   through PR #188 and the complete 24,486-specimen separation record.
6. `claim-status-and-source-map-2026-09-13.md` — concise authoritative
   classification of every load-bearing claim and its exact source.
7. `conjecture-ledger.md` — live prose dependency ledger.
   `ledger-index.md` is its generated machine-derived counterpart: one row per
   TLA+ ledger node with kind, source, dependencies, and closure.
8. `proof-ladder.md` — shortest honest path from established results to the
   remaining theorem, plus the stronger parallel structural routes.
9. `current-proof-architecture-2026-09-14.md` — canonical detailed architecture,
   explicitly distinguishing the primary overlap route from the finite-BPA and
   realization programmes. The 2026-09-11 file is retained only as a superseded
   historical pointer.
10. `../manuscripts/PSC_balanced_pair_state_2026-09-13.tex` — publication-form
   state-of-program exposition.

When these disagree, do not choose the strongest wording. Check the latest
merged commit, the claim/source map, the proof note, and `proof/tla/Ledger.tla`,
then repair all status surfaces together. `proof/tla/Ledger.tla`, the `proof/tla/MCLedger*`
models, `ledger-index.md`, `claim-relationship-graph.json`, and the claim
entries of every ledger node are
generated by `tools/make_ledger.py` from the proof-record table it holds
(`proof/tla/ledger.json` is the table's serialized, likewise generated, form); change
the table and regenerate, never the outputs. The claim ledger in
`claim_governance.toml` names every load-bearing claim, its status class, and
the surfaces on which that status is spelled out; CI, `pytest`, and
`tools/verify_all.sh` run the vendored `tools/claim_governance` audit
against it, so a surface that disagrees with the ledger fails the build.
Change the ledger entry and every surface in the same commit.

## Cross-program engineering

- `library-extraction-candidates-2026-09-14.md` — ranked audit of code that
  could move into shared libraries with NLAP-JT (exact arithmetic,
  substitution kernel, intervals, linear algebra, proof records, audits);
  engineering only, no claim status changes. Its "Execution status" section
  records which steps have landed.
- `exact-arithmetic-binding.md` — this repository's binding rows for the
  arithmetic specification kept in `larsbx/finite-math-kernels`, and the vendoring
  rule enforced by `vendored.toml`.
- `../claim_governance.toml` — the claim-governance policy read by the
  vendored `larsbx/claim_governance_tools` package: status vocabulary, claim
  ledger with its status surfaces, promotion guard, and the floating-point
  ban on the exact kernel.
- `claim-relationship-graph.json` — the same ledger read as a typed
  relationship graph (`docs/typed-relationship-graph-spec.md` in
  `larsbx/finite-math-kernels`): dependencies as `implicative` edges, aliases
  as `synonymous`, assumption-set membership as `part-whole`, and a live
  result standing on a withdrawn one as `contradictory`. Each node carries the
  provenance its record determines and the premises it leaves unestablished,
  so a conditional claim states its leak in the graph rather than only in
  prose. Generated; it asserts nothing the ledger does not already record.
- `test-claim-coverage.md` — which Mojo test guards which claim, and what the
  `coverage` check does and does not conclude from that.
- `cross-program-bridge-psc-nlapjt-2026-09-12.md` — structural comparison
  with the NLAP-JT finite Mandelbrot program.
- `cross-pollination-round-two-2026-09-16.md` — the comparative audit across
  both research programs, `finite-math-kernels`, and four adjacent
  repositories, with the running delivery record of its ranked items.
- `cross-pollination-round-three-2026-09-17.md` — the rest of the estate:
  twelve repositories round two never opened, and the six rulings they state
  independently of each other and of this program.

## Research references

- [`bridges/penrose-2d-to-psc-interface-program.md`](bridges/penrose-2d-to-psc-interface-program.md)
  — PR #154's non-load-bearing Penrose interface comparison. Its strongest
  analogies concern P2/G1b-2 and P4 realization; the narrower P1b/#139 analogy
  supplies no adelic hitting theorem. Penrose derivations remain in
  `larsbx/tiling-theory-research`.
- [`post-proof-padovan-plastic-a-conjectures-2026-09-23.md`](post-proof-padovan-plastic-a-conjectures-2026-09-23.md)
  and its [JSON catalogue](post-proof-padovan-plastic-a-conjectures-2026-09-23.json)
  — PR #157's research-only benchmark conjectures. The historical
  "post-proof" filename does not assert a completed PSC proof.

These are reference/index additions only. They do not establish #84, #138,
#139, G1, or general PSC, or change their ledger status or closure priorities.

## Source provenance

- `archive-tarball-audit-2026-09-13.md` — uploaded archive digest, identity check, and warning about contradictory v34 closing status language.
- `source-provenance-v16-later-audit-2026-09-12.md` — exhaustive reachable
  Git-history audit and imported-source checksums.
- `v9-extraction-audit-2026-09-23.md` — extracts the reusable UD / UD-for-powers / local-hierarchy material from the externally supplied PSC v9 manuscript and explicitly rejects its withdrawn finite-BPA and cycle-exclusion claims.
- `galois-aux-b-source-resolution-2026-09-13.md` — separates the historical
  degree-three seed theorem, the reconstructed degree-two carrier theorem, and
  open concentration.
- `../sources/issue-45/g1b1-bounded-discrepancy-reconstruction.md` —
  self-contained proof replacing dependence on the unrecovered contraction
  estimate.
- `../sources/issue-45/realization-coincidence-rank-audit.md` — G0–G6
  decomposition of the open realization bridge.
- `../sources/issue-45/p1a-concentration-aux-b-program.md` and
  `p1a-v34-concentration-audit.md` — preserved formulation and inheritance
  audits, not proofs of concentration.

- `lost-depth-indexed-formulation-2026-10-01.md` — records the lost files of a
  parallel depth-indexed ladder (`PROOF_LADDER.md`, `SWEEP_RESULTS.md`, ...),
  marks every claim attributed to them unverified and uncited, and identifies
  the lost 24,486-specimen sweep domain as total image length at most 8.
- `bpa-termination-by-overlap-depth-2026-10-02.md` — conditional bounded-gap
  argument: a productive seed-patch overlap graph of depth `D` bounds every
  balanced-pair state by `2 beta^D ell_max`; finite-domain consequences for
  `0 -> 1, 1 -> 222, 2 -> 0222` and the total-length class. Recorded in the
  ledger as the conditional theorem `G1OverlapRoute` (manuscript Proposition
  5.46).
- `bpa-overlap-depth-literature-gate-2026-10-02.md` — stop/go literature gate
  for that argument: the mechanism is Sirvent–Solomyak (2002), Theorem 5.6;
  novelty is narrowed to the swap-seed transfer and the explicit bound.
- `p1a-template-collapse-2026-10-05.md` — #138 research note (unreviewed),
  with its own stop/go gate: **Theorem C** collapses the three surviving
  aligned sub-templates of `p1a-aligned-cycle-normal-form-2026-10-01.md` onto
  one by passing to `sigma^2` — a fixed bad edge is permuted by the
  first-letter map, so its square fixes it pointwise, and in the alternating
  template the square is the identity; primitivity, irreducibility, the Pisot
  property, the good pair, the badness of the edge and the closed
  nonproductive component all transfer. So **A2 follows from A1**, and #138's
  aligned branch has one obligation instead of two: *two distinct one-sided
  fixed points of a PIP substitution on three letters, anchored at a common
  point, share a tile*. Exact certificate over all 81 endpoint/good-edge
  placements in `kernel/psc/hub_selector.mojo`, 36/36 viable ones collapsing,
  reproducing the 45/33/3 table. The gate records from Barge–Diamond (2002)
  itself why the surviving obligation is a special case of the **open** ternary
  strong coincidence problem and not a corollary of the import, and that a
  proof routed through transitivity of eventual coincidence would be wrong.
- `p1a-a1-prime-2026-10-05.md` — #138 research note (unreviewed) on the single
  obligation Theorem C leaves. **Proposition A**: A1′ is the *residual* half of
  all-pairs strong coincidence — the endpoints never synchronize in this
  configuration, so the whole content is interior — hence A1′ holds with zero
  failures on all 408,798 PIP specimens of the strong-coincidence census,
  residual level at most 15, and no sharper finite test exists because the
  hypothesis presupposes a bad edge no verified specimen has. **Corollary C3**:
  on the catch-up-free `|det M| = 2` class, Theorem C's template makes the
  aligned vertex a self-loop with no other offset-zero child (Lemma A's
  contrapositive), so a coincidence can only arrive as a simultaneous birth —
  **A1′ and T2 are the same statement there**, and #138's aligned branch meets
  #139's strict-zipper branch. Covers all 210 catch-up-free corpus members.
  All three are repository-proved. **Proposition B**: why A1′ is not a
  corollary of the Barge–Diamond import, by the count `d(d-1)/2` of pairs
  against the one the theorem produces, which also explains in one line why
  `d = 2` is settled.
- `p1b-strict-zipper-periodic-pair-2026-10-02.md` — #139 research note
  (unreviewed): two-sided alignment weakening of Proposition 5.47, and the
  reformulation of a strict zipper as two `Phi^r`-fixed legal tilings with a
  common centre and no common vertex; isolates the open target
  PeriodicPairVertexCoincidence; exact certificate `kernel/psc/periodic_pair.mojo`.
  Excludes no strict zipper.
- `p1b-periodic-pair-fibre-literature-gate-2026-10-02.md` — stop/go gate for
  the fibre identification: Proposition F (the Theorem B pair lies in one
  fibre of the maximal equicontinuous factor), with Theorem R proving its
  hypothesis (R), return module equal to `Z^3`, for every PIP substitution;
  exact index `kernel/psc/return_module.mojo`. Decision "proceed".
- `p1b-barge-diamond-configuration-gate-2026-10-02.md` — Barge–Diamond 2002
  and Barge 2018 Lemma 2 read in full: the configuration argument does not
  force a common vertex (its maximality step yields only an aligned pair).
  Decision "stop".
- `p1b-vertex-coincidence-box-2026-10-02.md` — #139 research note
  (unreviewed): Proposition V decides PeriodicPairVertexCoincidence per
  substitution for every `r` on one finite box graph; exact certificate
  `kernel/psc/vertex_coincidence.mojo` and census
  `kernel/vertex_coincidence_census.mojo`. Not proved for all PIP
  substitutions (it implies G1). Depth laws `K_V <= a + c/log(1/mu)` are checked
  exactly against the census records by `kernel/vertex_depth_law.mojo`
  (`psc.depth_law`). §5.6b: catch-up reachability (`kernel/psc/one_tile.mojo`,
  `kernel/one_tile_census.mojo`) fails on 360 of 4554 specimens at both
  endpoints, so the cross-letter rigidity is not a one-tile question;
  Lemma P (no proper prefix in `M Z^3`) accounts for all 210 total failures.
  Proposition P′: there, vertex levels are the M-adic valuations of their
  positions; Proposition C gives the class by image shape; Proposition P″
  (M-adic centres coincide in a periodic pair) closes the purely M-adic route;
  route check against Baker–Barge–Kwapisz 2006 recorded.
  §5.6h: exact anatomy (`kernel/one_tile_anatomy.mojo`); §5.6i: every scratch
  probe of the session archived with outputs in `archive/2026-10-04/session-probes/`.
  §5.6c states the closing trichotomy and its two unproved statements T1 and
  T2; the structure of T1's object is in the next entry.
- `p1b-leftmost-chain-periodic-pair-2026-10-05.md` — #139 research note
  (unreviewed), with its own stop/go gate: the leftmost child is a *function*
  on nonzero-offset vertices, so `CU` is the complement of the basins of that
  function's terminal cycles, and **Proposition LC** proves every such cycle
  keeps one offset sign and is a **prefix-vs-interior** periodic pair — a
  prefix occurrence `sigma^r(i) = i U` on the side whose tile starts later, an
  interior occurrence `sigma^r(j) = Q j V` on the other, and
  `w_0 = (I − M^r)^{-1} ab(Q) ∈ Z^A`. It is the half-degenerate companion of
  Theorem B, which excludes the prefix case. Canonical
  `kernel/psc/leftmost_chain.mojo`, census `kernel/leftmost_chain_census.mojo`,
  regression `kernel/tests/test_leftmost_chain.mojo`. It restructures T1 —
  "reaches `CU`" is an invariant of the box graph's strongly connected
  components (Corollary LC2) — but **does not prove T1**: the reachability half
  is still a pointwise hitting problem, and T2 is untouched. The gate records
  that the cycle principle itself is Siegel–Thuswaldner's zero-expansion graph,
  whose proposition assumes unimodularity at exactly the step this one carries
  as an explicit integrality condition.
- `formal-overlap-carriers-2026-10-04.md` — exact census of formal
  (potential) versus realized overlap carriers; supersedes the unreproducible
  "1,764 formal producer-free cycles / death radius 7" line of the
  2026-09-11 ledger. No closed carrier and no nonproductive potential overlap
  on the corpus; realized carriers are mostly aligned and die fast, unrealized
  ones are 99.3% strict zippers and die later (depth up to 14). Canonical
  `kernel/psc/formal_overlap.mojo`, census `kernel/formal_overlap_census.mojo`.
- `formal-productivity-reduction-2026-10-04.md` — research note
  (unreviewed): every potential overlap is productive iff the six aligned
  pairs `(i, j, 0)` are productive and every cycle overlap has an offset-zero
  descendant (Proposition FP), with the remainder after offset zero bounded by
  `S(sigma)`; with Proposition V and Theorem S this is PDS plus all-pairs
  aligned strong coincidence (Corollary FP′). Changes no status.
- `pds-strong-coincidence-literature-gate-2026-10-04.md` — stop/go: Akiyama–Lee
  2014 Corollary 4.5 gives PDS ⇒ all-pairs prefix strong coincidence for
  irreducible Pisot substitutions (non-unit height step via Theorem R);
  hence formal productivity ⟺ PDS. Decision "proceed, caveat recorded".
- `coincidence-rank-imports-literature-gate-2026-10-04.md` — stop/go: the
  imports behind Theorem S (Barge 2013 Thm 4, Barge 2015 §1 (2)–(3)) assume
  only a primitive, non-periodic substitution with Pisot inflation, so they
  cover every PIP substitution, non-unit included. Decision "proceed".
- `strong-coincidence-census-2026-10-04.md` — exact SC_all census on the
  corpus, total length ≤ 8, images ≤ 4 and total length ≤ 10 (408,798
  specimens): no failure. Lemma A: on the catch-up-free `|det M| = 2` class the
  aligned route is a hitting statement through nonzero offsets. With the
  recorded PPVC runs, pure discrete spectrum on the 145,806 specimens with
  images ≤ 4 or total length ≤ 8 (finite evidence; Proposition V unreviewed).
  Driver `kernel/strong_coincidence_census.mojo`.
- `catch-up-hit-witness-enumeration-2026-10-04.md` — occurrence-level
  all-path decision (`psc.hit_witness`): committed stable labels for all
  97,224 simultaneous-only standing vertices, replayable closed certificates,
  alternative-shortest and later-hit controls; recorded 1,000-specimen slices
  of the total-length-8 and image-length-4 domains. Standing export rerun in
  CI. [Stop/go check](catch-up-hit-witness-gate-2026-10-04.md); no closure of
  #139, UH, G1, general PPVC or PSC.
- `return-lattice-literature-gate-2026-10-02.md` — return vectors of tiles
  span `Z<ell>` on the whole corpus; return vectors of length-`n` patches span
  it for every `n` on the unimodular classes and fail to by `n = 13` on every
  `|det M| = 2` specimen, where the equicontinuous factor is a solenoid
  (Barge–Kellendonk Corollary 5.11). Exact census:
  `kernel/return_lattice_census.mojo`.
- Manuscript Proposition 5.47 and the same proof note's Proposition 4 /
  Corollary 5 sharpen this to the half-coincidence route: excluding reachable
  strict zippers from every swap seed is sufficient for G1. The exclusion is
  still open, so this conditional theorem does not promote G1 or PSC.

The missing `PSC_PROOF_v16` file is a historical provenance fact. It is not a
current dependency for G1b-1 or degree-two carrier-span propagation.

## Exact finite-domain results

- `p1a-degree3-partial-theorem.md` — no strict `K2=0`, first-`K3`
  component in the exact 4,554-member short-image corpus.
- `p1a-degree2-wedge-productivity.md` — no closed nonproductive recurrent
  nonzero-`K2` component in the same corpus.
- Canonical executable certificates live in `../kernel/` and are enforced by
  GitHub Actions.

These are theorems over their enumerated finite domain. They are evidence, not
general concentration or wedge-productivity theorems. Certificates must fail
closed on caps and retain a replayable record for every survivor.

## Primary completion route: finite seed-patch overlaps

- G1b-1 bounded discrepancy: repository-proved.
- Seed-patch overlap-graph finiteness: repository-proved from bounded discrepancy.
- Coincidence-density / dense-good-set equivalence: repository-proved.
- Density-to-PDS: imported Barge–Štimac–Williams theorem, audited in the manuscript.
- **Overlap productivity remains the only open premise on this shortest route.**
  Productivity of the overlaps reachable from one periodic swap seed built from
  distinct tile types already implies PDS (manuscript Theorem 5.38); no
  substitution-language legality assumption is used; proving every seed or every vertex in the union
  graph is stronger than necessary. Proposition 5.39(iii), the all-pairs
  strong-coincidence consequence, and the unimodular equivalence with PDS apply
  only to the stronger all-vertex hypothesis; no one-seed-to-all-vertices
  implication is claimed. See `audit-2026-09-20.md` §C.
- Endpoint-aligned overlaps are the two-sided strong coincidence condition, and
  under strong coincidence productivity is the prefix-Parikh boundary-hitting
  statement of Propositions 5.39–5.40 / Corollary 5.41.
- The contracting lower bound on the hitting level (Proposition 5.42, PR #87)
  accounts for at most 8 of the up to 17 inflations observed, leaving a gap this
  magnitude bound does not explain (note Section 10).
- Exact finite evidence: all 1,118,850 overlap vertices in the 4,554-member corpus
  are productive; maximum first-coincidence depth 18, maximum first left-aligned
  depth 17, maximum prefix/suffix strong-coincidence depth 15.
- Contracting lower bound on the hitting level: at most 8; excess of the
  hitting depth over it at most 14.

## Stronger Level 2 programme: BPA finiteness

- G1b-2 renewal finiteness remains open and is now equivalent to G1 after G1b-1.
- It is **not required by manuscript Theorem 5.38**, but remains the exact theorem
  needed to establish finite BPA in general.
- `bpa-literature-bridge.md`: interface audit between literature algorithms
  and the normalized all-seed repository graph.
- Renewal, address, and countermodel notes should preserve non-unimodularity
  and must not treat the projected integer module as a lattice.

## Alternative finite-BPA Level 3 programme

- `sink-scc-reduction.md`: finite obstruction extraction under G1.
- Endpoint, signing, first-defect, ordered-area, recognizability, and hierarchy
  notes provide supporting structure.
- General concentration (`K2=0` branch) remains open.
- General wedge productivity (`K2!=0` branch) remains open.
- Full rational wedge span does not imply productivity.
- These remain valuable structural theorems to pursue, but they are not
  prerequisites of the current one-gate overlap route to PDS.

## Realization and collar experiments

The realization/MEF track is an open bridge and parallel certification route.
A formal recurrent BPA component, a globally realized tiling component, and a
component surviving a finite collar radius are not interchangeable. Use the
G0–G6 audit before citing an equivalence.

## Historical material

- `../archive/2026-09-08/README_READ_FIRST_2026_09_08.md` explains the
  preserved archive.
- `../archive/2026-09-08/manuscripts/PSC_PROOF_v15.tex` is the last imported
  canonical predecessor manuscript.
- `../archive/2026-09-08/certificates_patched/PROOF_CERTIFICATE.md` contains
  the restricted degree-three seed theorem.
- Dated completion ledgers are snapshots, not automatically current.

Historical files are immutable evidence. Correct their live interpretation in
the current ledgers rather than rewriting the archive.

## Verification and implementation

- [`audit-pr197-2026-10-03.md`](audit-pr197-2026-10-03.md) records the
  independent audit of PR #197 at `347c0d9`: Theorem R, Proposition V's finite
  box completeness and the PDS ⇒ PPVC ⇒ G1 interface. It distinguishes the
  CI-guarded standing census and regression slices from the larger recorded
  PPVC runs, leaves general G1 and PSC open, and changes no claim-ledger status.
  Its checks are historical results on that head, not on later `main`.
- `verification-architecture.md` describes the responsibilities and limits of
  Mojo, TLA+, Lean, and Python.
- `mojo-census-library-2026-09-16.md` describes the shared census/catalogue
  library every driver is built on, and the retirement of the Python-only
  computation scripts it replaced.
- `automatic-sequence-route-literature-gate-2026-09-17.md` gates the step from
  a census to a decision procedure, and now records the three automata that
  exist for a specimen that builds -- admissibility, the letter map, and
  addition -- against what is still missing: what the automata kernel and the
  Dumont-Thomas numeration now establish, and the three things that would have
  to be imported before any family could be decided.
- `frontier-intersections-2026-09-17.md` looks outward from the two programs:
  which fields of mathematics the separation calculus, the certificate calculus
  and the governance layer could touch, what each would return, and a first
  experiment for each. It proves nothing and changes no ledger.
- `mojo-lookup-caches-2026-09-17.md` records which repeated computations were
  worth replacing with a lookup and which measurement said to leave alone, and
  what keys make the three caches exact.
- `bsw-import-literature-gate-2026-09-21.md` checks Imported Theorem 5.37
  against the Barge–Štimac–Williams source text: patches need not be allowed,
  "densely" means a dense set of points, and the one-dimensional
  specialization is their own proof of Theorem 3.2. Decision: proceed.
- `audit-2026-09-10.md`, `audit-2026-09-15.md`, `audit-2026-09-20.md` and
  `audit-2026-10-04.md` are the status audits: the C1–C4 reduction chain, the
  engineering state, the overlap-productivity route against that chain, and
  the overlap-depth routes with the `PDS ⇒ G1` promotion.
- `../AGENTS.md` is the implementation policy.
- Mojo is canonical for executable research.
- TLA+ records dependency/state-machine claims.
- Lean checks deductive finite algebra.
- Python is an independent oracle or prototype, not the executable source of
  truth once Mojo exists.

Run all available verification layers with:

```bash
./tools/verify_all.sh
```

A skipped unavailable toolchain must be reported; it is not a passing proof.

## Status-change checklist

When a theorem status changes:

1. identify the exact statement and hypotheses;
2. classify it using the claim/source vocabulary;
3. attach the proof, import, finite certificate, or named open obligations;
4. update the claim/source map, conjecture ledger, proof ladder, detailed
   architecture, README, manuscript status table, and TLA ledger as applicable;
5. update citations and distinguish mathematical sources from Git provenance;
6. retain finite-domain parameters and countermodel behavior;
7. run verification and obtain review before merge.
