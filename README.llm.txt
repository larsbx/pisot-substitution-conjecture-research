PSC RESEARCH PROGRAM — AGENT ENTRYPOINT
File: README.llm.txt
Audience: LLM research agents, coding agents, proof auditors, CI/review agents.
Companion for humans: README.md
Implementation policy: AGENTS.md
Scope: state of research and operating constraints, NOT a claim-status authority.
Baseline inspected: main@012d563522fbe96c8b663fbe2d4fc926ecda45a4.
When a PR or the claim ledger moves, recheck instead of treating this snapshot as live.
Organization: mathematical dependency / evidentiary strength, NOT chronology.

=======================================================================
0. GOAL, PRECONDITIONS, AND SUCCESS CONDITION
=======================================================================

Goal: prove pure discrete spectrum (PDS) for primitive irreducible Pisot
substitutions in the repository's standing generality. In particular:
  - substitution alphabet finite, primitive;
  - det(incidence matrix) != 0;
  - characteristic polynomial irreducible over Q;
  - Perron eigenvalue beta is Pisot;
  - NON-unimodular examples are included, |det M|=1 is not assumed.

Do not claim general PSC is proved. It is OPEN.

The direct sufficient implication chain is:
  primitive irreducible Pisot
    => bounded discrepancy                         REPOSITORY-PROVED
    => finite seed-patch overlap graph             REPOSITORY-PROVED
    => one appropriate swap seed is productive     OPEN, issue #84
    => coincidence density one                     REPOSITORY-PROVED
    => PDS                                         IMPORTED with audited hypotheses

The two-obstruction completion theorem supplies a sufficient strategy
for the one-seed productivity premise:
  A1-prime (#138) AND BH (#139)
    => one-seed productivity (#84)
    => PDS.
The implication is established at its stated hypotheses. Its two
universal antecedents are NOT proved.

A1-prime: one-sided eventual coincidence of the residual fixed-hub
aligned pair. Do NOT reintroduce a two-sided reversed premise.
BH: every relevant CYCLIC, SEED-REACHABLE, STRICT-ZIPPER overlap has
an ACTUAL OCCURRENCE-COMPATIBLE descendant of OFFSET ZERO.
BH needs a boundary hit, not necessarily equal-letter coincidence.

One suitable seed is enough for the shortest sufficiency route.
All-seed/all-vertex productivity is a stronger proof target; it is
not a license to assume the one-seed-to-all-vertices implication.

Canonical live references:
  claim_governance.toml
  docs/proof-ladder.md
  docs/claim-status-and-source-map-2026-09-13.md
  docs/research-roadmap-2026-09-21.md
  docs/direct-attack-frontier-2026-10-23.md
  manuscripts/PSC_balanced_pair_state_2026-09-13.tex
  tools/make_ledger.py (for generated proof-record nodes)

=======================================================================
1. STATUS PRECEDENCE AND PROOF STRENGTH
=======================================================================

If there is a conflict, inspect the actual claim source, its hypothesis
and acceptance receipts. Governance/authoritative proof records and
current reviewed artifacts control; this entrypoint is orientation only.
Never silently update claim status from a narrative README or GitHub
issue state.

Use exactly scoped language:
  PROVED: proof and quantified hypotheses established in repository.
  IMPORTED: cited external result with applicability verified.
  CONDITIONAL: implication proved; premise may still be open.
  FINITE-DOMAIN: exhaustive, independently accepted certificate on a
    declared finite universe; NOT an unrestricted theorem.
  FAMILY: uniformly proved for a precisely parameterized infinite family;
    NOT a cover of the standing regime unless the cover is proved.
  FINITE REPLAY / EVIDENCE: specimens, oracle tests and counts, NOT proof
    of an unbounded parameter quantifier.
  PROPOSAL / PR-OPEN: unmerged research statement, not mainline theorem.
  HISTORICAL / WITHDRAWN: source material or rejected inference only.

Machine-generated evidence, hand symbolic algebra, Lean formalization,
independent human review, and current-hosted CI are different fields.
"Project-accepted for progression" permits provisional downstream work
under preserved hypotheses, NOT a fictional independent review.

Required checks:
  - Verify PR merged/head status and actual files on main.
  - Inspect EXACT HEAD evidence and whether CI is queued/failed/succeeded.
  - Read scoped theorem statement, parameter guards and receipt provenance.
  - Keep finite member agreement distinct from Z[k,t] identity proofs.
  - A failed or SKIPPED verifier confers no proof credit.
  - Do not infer "issue closed" => theorem proved.

Claim-governance mechanism:
  claim_governance.toml and generated proof/TLA ledger surfaces must agree;
  generated blocks must NOT be edited by hand. Modify the proof-record
  source (tools/make_ledger.py) and regenerate only when justified.
  The authoritative status convention is more specific than PR labels.

=======================================================================
2. EVIDENCE IN DESCENDING ORDER OF RELEVANCE TO PSC
=======================================================================

TIER A — DIRECT GENERAL SUFFICIENCY INPUTS
  Proved: bounded discrepancy, finite exact seed-patch overlap graph,
  obstruction normal form, productivity=>coincidence-density.
  Imported: density-to-PDS with explicitly checked hypotheses.
  Open: universal one-seed productivity (issue #84).
  Universal target interfaces: A1-prime (#138) + BH (#139).

TIER B — UNIVERSAL ALGEBRA INSIDE STRICT SUBFAMILIES
  - Class-D determinant-two PIP boundary hitting is assembled at its
    declared scope. Its finite-BPA corollary is ALSO scoped.
  - Catch-up-free determinant-two A1-prime has large proved sectors;
    residual non-crossing family-F cells remain.
  - Classes A, B, C have line/wedge/cone/boundary certifications; the
    uniform A/C regions and B top layer remain unfinished globally.
  - Any family closure must supply an INDEPENDENT COVERING THEOREM
    before it can discharge universal BH or A1-prime.

TIER C — RECOVERED CLASS-A GRAPH/SELECTED-EXIT PACKETS
  Minus class-A only:
    k,t >= 0; n=k+t+3; d=2*n-1-k; A=n+d
    x -> x y^A x
    c -> c y^n x
    y -> x y^(n-1) c

  Merged #372: canonical P3-star family.
  Merged #412: T/X/Y0 exact stars, 42-label outgoing image and endpoints;
    source #371 had been merged only to an obsolete branch.
  Merged #413: P3 (37) and T/X/Y0 (42) images have intersection 20,
    union 59 oriented labels. NOT closed; NOT all seed-reachable states.
    Its 34-label review queue is scoped to a CURATED registry, not the
    globally unresolved label count.
  Merged #414: CY=(c,y,0,-2,2) six typed labels, 2n+1 actual indexed
    children per orientation, Y0<->CY cycle, selected typed exit.
  Merged #419: for Y0=(y,y,1,-1,-1), every actual FIRST choice has
    SOME selected continuation to coincidence (<=6 edges from Y0).
  Open #411: #354's four-edge aligned seed->internal coincidence witness,
    including selected U->...->C two-edge suffix.
  Open #415: every CY first choice has a selected coincidence
    continuation (<=7 total edges); extra proofs/CI NOT on main.
  Open #416: CC=(c,c,0,-2,3) four-child star and three-edge selected exit.
  Open #417: every CC first choice has a selected continuation
    (<=5 total edges), stacked on #416.
  NOTE: Y0 LAST/LAST reaches EXACT CC=(c,c,0,-2,3) STRICTLY only for t=0.
    Do not silently turn that endpoint into a uniform Y0 edge.

  These labels and edge counts concern actual ORIENTED five-tuples,
  with parameter-dependent word occurrences. Do not treat a union of
  outgoing-image labels as a forward-closed carrier.

TIER D — FINITE-DOMAIN RESULTS
  Theorem Omega: PDS on exactly 145,806 specified ternary PIP
  substitutions in the stated bounded image/total-length union;
  relies on audited overlap/Meyer and flow-to-symbolic imports.
  This is an exhaustive finite-domain theorem, NOT an infinite-family
  theorem and NOT a PSC closure.

TIER E — FINITE CORPORA / REGRESSIONS
  Standing short-image corpus: 4,554 exact ternary PIP specimens;
  all seed-patch overlap graphs constructed in the reported census;
  largest graph 2,640 vertices; no nonproductive state observed;
  max first coincidence depth 18.
  Strong coincidence: reported two-sided finite check for 408,798
  specimens in total-length <= 10 domain.
  Native Mojo, independent Python, exact Fraction, rational-Perron and
  proof-policy checks are regressions at their stated scope.
  No finite sample, however large, proves universal PIP PSC.

TIER F — NEGATIVE CONTROLS / HISTORICAL SOURCES
  Productive affine cycles exist: all-edge-decreasing rank is false.
  Abstract affine equality cannot substitute for actual occurrence data.
  Finite-radius collar, magnitude-only contracting lower bound,
  rank-deficiency shortcut and unverified Nakaishi first-entry routes
  have documented limitations.
  Historical v6/v9 arguments are mined only through their source audit;
  withdrawn closure inferences never become live premises.
  Plastic-A/Padovan and Penrose are benchmark/bridge programmes, not
  additional load-bearing premises.

=======================================================================
3. EXACT OVERLAP STATE AND EDGE CONTRACT
=======================================================================

State ID:
  (top_letter, bottom_letter, dx, dc, dy).
  These three integers are bottom-minus-top Parikh offset coordinates.
  Never canonicalize by nickname (T, Q, V, U, etc.) alone.
  Actual reversal:
    R(a,b,p,q,r) = (b,a,-p,-q,-r).

For a selected actual ordered child (i,j), zero-based in the
literal substituted top and bottom words respectively:
  child_state =
    (top_image[i], bottom_image[j],
     M * offset
       + Parikh(bottom_image proper prefix to j)
       - Parikh(top_image proper prefix to i)).

A VALID EDGE requires, independently:
  (i)   parent belongs to the declared family and parameter chamber;
  (ii)  both indices exist as actual FIRST/RUN/LAST letter occurrences;
  (iii) the child types and full three-coordinate Parikh update agree;
  (iv)  both parent and child have STRICT interior physical overlap,
        not mere endpoint contact;
  (v)   reversal uses swapped REAL occurrence indices;
  (vi)  all symbolic guard inequalities hold for every parameter in
        the quantifier domain, including n=3, k=0, t=0 exceptions.

The endpoint/strictness rule is especially easy to violate: two states
may have plausible physical offsets but DIFFERENT typed LAST/RUN children.
An affine quotient graph is not proof of a symbolic child.

When checking a proposed all-parameter result:
  1. Derive explicit image words and occurrence prefix vectors.
  2. Partition integer parameter space into exhaustive disjoint chambers.
  3. Verify identities coefficientwise in Z[k,t] (or exact field/ring).
  4. Prove each address is valid in its chamber; test unbounded directions.
  5. Prove all geometric overlap margins STRICT using exact root bounds.
  6. Recheck actual orientations and endpoint cases.
  7. Run independent literal-word and exact-arithmetic finite regressions.
  8. Distinguish the symbolic universal argument from its finite replay.
  9. Record source/receipt, status, hypotheses and known nonclaims.

For the CY/Y0/CC selected paths, existing root inequalities allow
affine strict-overlap checks over a rational polygon in h=1/beta and
rho=alpha-h; that technique is valid at ITS scoped assumptions only.
Do not imply it handles arbitrary PIP families or replaces the needed
non-unit finite-place representation-space arguments.

=======================================================================
4. CURRENT HIGH-LEVERAGE PROOF WORK (NOT A CALENDAR)
=======================================================================

PRIMARY: Universal BH (#139).
  Define the seed-reachable cyclic strict-zipper universe precisely;
  verify the actual graph closure on each proposed carrier; classify
  or control all outgoing child types; prove coincidence/boundary-hit
  reachability for every relevant obstruction state.
  Near-term class-A work: reconcile all outgoing labels of P3/TX/Y0/CY/CC
  against the COMPLETE existing proof bank. Separate unclassified sources
  from classified sources with missing exits. Avoid naming duplicates.
  A productive cycle does NOT refute existential BH; it refutes an
  all-edge strict-descent requirement.
  Then extend to A/C uniform chambers, B top layer and non-unit/M-adic
  representation with no extra hidden premises.

SECONDARY: One-sided A1-prime (#138).
  Finish the non-crossing residual hub family and prove full standing
  generality. Do not conflate two-sided SC corpus checks with A1-prime.

ASSEMBLY: Apply the scoped two-obstruction completion theorem once both
  universal premises are verified. Then check #84 one-seed productivity,
  density, PDS import and all proof hypotheses end-to-end.
  Do not close an issue or promote a claim in advance of proof.

PARALLEL STRUCTURE (NOT REQUIRED BY DIRECT SUFFICIENCY):
  G1b-2 renewal finiteness and finite BPA;
  SCC Producer, concentration and wedge productivity;
  realization/MEF/coincidence-rank bridges;
  exact number-theory and finite-interface benchmark programmes.

=======================================================================
5. REPOSITORY SOURCES, TOOL POLICY, AND ACCEPTANCE
=======================================================================

Proof/status authority:
  claim_governance.toml
  tools/make_ledger.py
  docs/proof-ladder.md
  docs/claim-status-and-source-map-2026-09-13.md
  docs/proof-bank.md
  manuscripts/PSC_balanced_pair_state_2026-09-13.tex

Direct strategic references:
  docs/direct-attack-frontier-2026-10-23.md
  docs/project-onboarding-2026-10-23.md
  docs/class-d-assembly-audit-2026-10-21.md
  docs/class-a-boundary-consolidated-frontier-2026-10-31.md
  docs/class-a-boundary-cy-carrier-2026-10-31.md
  docs/class-a-boundary-y0-every-child-2026-10-31.md

Implementation and validation:
  AGENTS.md                  Binding implementation/review policy.
  kernel/                    Canonical Mojo executable research.
  kernel/psc/                Shared corpus/histogram/carrier/symmetry.
  kernel/tests/              Mojo tests with claim/contract declarations.
  reference/psc_research/    Secondary reference logic.
  oracles/python/            Independent exact differential oracles.
  tests/                     Python regression tests.
  proof/PscVerif/            Lean exact finite-algebra proofs.
  proof/tla/                 TLA+/TLC models and generated ledger.
  evidence/                  Immutable SHA256-pinned evidence.
  vendored.toml              Pinned dependency identity and digests.
  ESTATE.toml                Repository authority/layout manifest.

Normal verification entrypoints:
  ./tools/verify_all.sh
  (from kernel/) pixi run test
  (from kernel/) pixi run verify
  ./tools/setup_lean.sh
  ./tools/check_lean.sh
  PYTHONPATH=tools python -m claim_governance.cli --root .

Report which commands actually ran and whether each passed, failed or
SKIPPED; do not claim verification for an unavailable toolchain.
For a proof-by-computation claim, record exact corpus bounds, schemas,
caps, all hash/CI receipts, and independent checks. Never invent a
Green CI result from 'queued' workflow runs.

Implementation DEFAULT is Mojo-first. New executable algorithms,
finite-state engines and census machinery belong in kernel/ before
Python can be treated as an independent oracle. Follow AGENTS.md;
do not rewrite vendored packages locally or hand-edit generated ledgers.

PR discipline:
  - Compare against current main and the canonical oriented state ledger.
  - Import only missing statements/artifacts; retain historical evidence.
  - Avoid a second kernel for a proof already subsumed by main.
  - Use focused changes and explicit preconditions/nonclaims.
  - Verify the exact head, diff, test receipts, and merge prerequisites.
  - Updating a README, merging a PR, or passing a specimen replay cannot
    independently change any global claim's mathematical truth/status.

=======================================================================
6. MANDATORY GENERALITY FIREWALL
=======================================================================

Never silently add:
  - |det M|=1 (unimodularity).
  - independent tile lengths in Z/Q (derive consequences as appropriate).
  - UD as an independent hypothesis (derive it from full rank/defect
    theorem when used).
  - prefix/suffix permutation, boundary injectivity or finite injectivity.
  - legality of chosen swap seeds as an unproved extra prerequisite.
  - Euclidean-only realization when M-adic/finite-place factors matter.
  - discrete projected Z^A lattice assumption.
  - realization of a formal recurrent object without a separate proof.
  - an arbitrary fixed-radius or finite corpus bound as universal.
  - a strongly decreasing rank on every edge of a productive cycle.
  - arbitrary later-choice termination from a first-choice exit theorem.

Never promote a selected path to a full child-closed carrier;
never replace an occurrence edge with an affine quotient edge;
never equate a proven implication with proof of its open antecedent.

=======================================================================
7. RESEARCH HISTORY IS SEPARATE FROM THIS INFERENCE MAP
=======================================================================

This file intentionally contains no chronological milestone narrative.
For dated decisions, experiments, withdrawn paths and recovered branches:
  docs/completion-ledger-2026-10-26.md
  docs/side-notes-ledger.md
  docs/branch-conjugate-audit-2026-10-30.md
  archive/
  GitHub PR and issue histories.

Historical notes and benchmark programmes may inspire proof strategies;
they do not override authoritative current hypotheses or claim status.

=======================================================================
8. STANDARD DELIVERABLE FROM AN AGENT
=======================================================================

For every mathematical change, report in this order:

  TARGET: exact claim, issue, standing assumptions, quantifier scope.
  DELTA: what the new work proves relative to already accepted mainline.
  STATEMENT: precise theorem/proposition and conclusion type.
  DERIVATION: universal proof or explicit conditional obligations.
  ACTUAL EDGES: oriented tuples, literal occurrences and guard checks.
  EVIDENCE: exact tests, independent oracle, hashes, CI receipts.
  NEGATIVE CONTROLS: endpoints, wrong-type, wrong-index, false closure.
  DEPENDENCIES: imported theorems, earlier proof records, open PRs.
  STATUS: proved/conditional/family/finite/experimental/proposed as warranted.
  NONCLAIMS: stronger statements NOT supported.
  NEXT GAP: smallest reproducible mathematical or implementation obligation.

This is the agent-facing evidence and inference contract. For a
pedagogical explanation and navigation, see README.md.
