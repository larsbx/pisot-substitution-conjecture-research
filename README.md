# Pisot Substitution Conjecture Research Program

Automated research workspace for the Pisot Substitution Conjecture (PSC), with emphasis on reproducible experiments, conjecture tracking, manuscript hygiene, theorem-audit automation, and exact finite certificates.

## Implementation default

**Mojo is the canonical implementation language for executable research code in this repository.** New algorithms, exact finite-state machinery, census code, and performance-sensitive proof instrumentation should land in `mojo/` first and use Mojo-native data/layout optimizations.

Python under `src/psc_research/` is a secondary reference/oracle and prototyping layer. Once a Mojo implementation exists, the Mojo module is the executable source of truth. See `AGENTS.md` for the detailed policy.

The generated [mathematical-object catalogue](docs/mathematical-object-catalogue.md)
provides a browsable taxonomy with explicit canonical-Mojo and independent-oracle
links. Its single machine-readable source is `catalogues/mathematical_objects.toml`.

Censuses, catalogues and the taxonomies of the objects they classify are built
on one shared library (`mojo/psc/corpus.mojo`, `histogram.mojo`, `carrier.mojo`,
`symmetry.mojo` and the defect kernels), so a driver is a survey over the corpus
rather than a private copy of it. `mojo/pixi.toml` has one task per driver and
`pixi run test` loops over every `mojo/tests/test_*.mojo`. See
`docs/mojo-census-library-2026-09-16.md`, and
`docs/mojo-lookup-caches-2026-09-17.md` for the exact-arithmetic results the
drivers now look up instead of recomputing.

## Current mathematical state

Start here:

1. `docs/current-proof-architecture-2026-09-14.md` — canonical current architecture.
2. `docs/completion-ledger-2026-09-14.md` — latest weekly completion ledger and priority ordering.
3. `docs/claim-status-and-source-map-2026-09-13.md` — authoritative status/source taxonomy, updated through the 2026-09-14 architecture reconciliation.
4. `docs/conjecture-ledger.md` and `docs/proof-ladder.md` — live prose dependency views.
5. `manuscripts/PSC_balanced_pair_state_2026-09-13.tex` — publication-form state-of-program exposition.

### Headline: one open premise on the shortest PDS route

The shortest current sufficiency chain is

```text
primitive irreducible Pisot
=> bounded discrepancy                                  [PROVED]
=> finite seed-patch overlap graph                      [PROVED]
=> one swap seed has only productive reachable overlaps [OPEN]
=> coincidence density one / dense good set             [PROVED]
=> pure discrete spectrum                               [IMPORTED theorem]
```

The only open premise on this route is **seedwise overlap productivity (Open Problem 5.35, issue #84)**. Manuscript Theorem 5.38 therefore no longer requires finite BPA / G1.

What that premise is, so the headline is not misread as a reduction: it contains the two-sided strong coincidence condition of Arnoux–Ito as its endpoint-aligned case (manuscript Proposition 5.39), open for three letters since 2001; under strong coincidence its remaining content is the prefix-Parikh hitting problem of Corollary 5.41, the geometric (super-)coincidence problem of Ito–Rao and Barge–Kwapisz; and for unimodular `sigma` a converse (PDS implies productivity of every overlap vertex) can be read off Barge–Kwapisz Cor. 9.4 / Prop. 17.2, cited but not imported, so there the premise is equivalent to PDS. Theorem 5.38 removes the finiteness hypothesis from the route; it does not reduce the conjecture. Manuscript Open Problem 5.35 is stated for every vertex of the overlap graph; the one-seed form that Theorem 5.38 needs is weaker and is the form meant on the status surfaces. See `docs/audit-2026-09-20.md` §C.

The current strict-zipper attack retains actual ordered child occurrences and
certifies their exact affine recurrence `w'=Mw+q-p`. A productive
determinant-two regression has a six-edge zero-shift-free affine cycle, so the
next universal step is explicitly a child-closure plus
recognizability/full-internal-space theorem, not a bare cycle exclusion.

This does **not** mean the stronger structural problems are solved:

- **G1b-2 renewal finiteness / finite BPA (G1)** remains open (issue #44), but is now a parallel stronger theorem rather than a prerequisite of Theorem 5.38.
- **Concentration (`K2=0`)** and **general wedge productivity (`K2!=0`)** remain open on the finite-BPA/SCC route (issue #43 covers the concentration branch).
- **SCC Producer** remains open generally.
- **Realization / coincidence-rank** remains an audited open bridge with G0–G6 obligations.
- **PSC remains open.**

### Established primary-route inputs

- **Unique decodability:** repository-proved from full incidence rank / the defect theorem. UD is derived, not assumed.
- **G1b-1 bounded discrepancy:** independently reconstructed and proved in PR #69; uses primitivity + Pisot spectrum, not unimodularity or UD.
- **Finite seed-patch overlap graph:** repository-proved in PR #72 from bounded discrepancy, with an explicit finite coordinate bound and no G1 assumption.
- **Full-rank bad-set constraint:** PR #76 proves that a nonempty child-closed noncoincidence overlap set has full rational intersection-vector rank and that its child-count matrix inherits the Galois spectrum of `M`. A bad set is algebraically rich, not rank-deficient.
- **Coincidence density:** repository Lemma 5.36 identifies overlap productivity with coincidence density one / density of the eventual-coincidence good set.
- **Density to PDS:** Barge–Štimac–Williams is imported with exact hypotheses audited in PR #77 / manuscript Imported Theorem 5.37.
- **Endpoint-aligned structure:** PR #82 identifies offset-zero/right-aligned overlaps with prefix/suffix strong coincidence and proves the exact prefix-Parikh boundary-hitting criterion.
- **Obstruction normal form in the manuscript:** Propositions 5.43–5.44 and Lemma 5.45 state and prove the closed irreducible obstruction, the aligned-versus-strict-zipper dichotomy (with first-/last-letter closure of the aligned pairs), and the ordered cycle equation with its purely periodic offset expansion.
- **Contracting lower bound:** PR #87 proves that a boundary hit at level `m` forces `|ς(t)| ≤ C_ς Σ_{s≤m} |ς(β)|^{-s}` for every contracting embedding (Proposition 5.42, decided exactly in `Q(β)`); on the corpus this lower bound is at most 8 while the hitting depth reaches 17, a gap of up to 14 inflations that this magnitude bound does not explain (the gap includes the slack of the bound; no further attribution is drawn).
- **Ordered affine/context boundary:** ordered occurrences satisfy the exact affine recurrence, but the determinant-two calibration reaches one affine child state through unequal one-step paired prefix-suffix addresses. Affine equality is therefore not a symbolic pump-deletion criterion. The radius-`m` collar (`docs/p1-overlap-collar-2026-09-16.md`) is exact: on the determinant-two graph one letter of context on each side resolves one-step ancestry, while 120 corpus specimens exhibit the precisely classified proper-power collapse. The seed-relative multiple-edge accounting is now proved (`docs/p1-overlap-seed-growth-bridge-2026-09-17.md`): occurrence-labelled paths count realized residual overlaps per inherited seed period, including repeated child types, and periodic collapse does not invalidate the forward update. The remaining bridge is the rigidity step excluding full-growth, child-closed, nonproductive realized occurrences; generic Perron growth and bounded-context equality do not do this.

### Current theorem target

Issue #84 is the primary completion issue. The preferred attack is to assume a **minimal finite reachable child-closed nonproductive overlap set** and combine:

- full rational rank;
- inherited child-count spectrum;
- ordered exact descendant offsets;
- prefix-Parikh boundary avoidance;
- Pisot contraction;

until a boundary hit / coincidence or an impossible finite configuration is forced.

Proving all seeds or every overlap vertex is stronger than necessary; one swap seed on distinct tile types per substitution suffices for Theorem 5.38, and `ab` need not be a legal factor.

### Exact finite evidence

On the exact 4,554-member ternary PIP short-image corpus:

- maximum reachable discrepancy: `14`;
- a reachable balanced-pair state has length `48,020`;
- seed-patch overlap graphs built / capped / failed: `4,554 / 0 / 0`;
- total overlap vertices: `1,118,850`;
- largest overlap graph: `2,640` vertices;
- specimens with a nonproductive overlap: `0`;
- maximum first-coincidence depth: `18`;
- maximum first left-aligned depth: `17`;
- maximum prefix/suffix strong-coincidence depth: `15`;
- contracting lower bound on the hitting level (Proposition 5.42): at most `8`, excess of the hitting depth over it at most `14`;
- every specimen satisfies the tested two-sided strong-coincidence condition.

The degree-two and degree-three fail-closed carrier certificates also have zero survivors in their exact stated domains. These are finite-domain theorems/evidence according to their individual completeness contracts; none proves the general PSC.

## Generality firewall

The project deliberately targets the non-unimodular primitive irreducible Pisot setting. A general theorem must not silently add:

1. tile-length `Q`/`Z` independence as an independent hypothesis — derive it from irreducibility where used;
2. unique decodability as an independent hypothesis;
3. finite injectivity, prefix/suffix permutation, or boundary-injectivity assumptions;
4. unimodularity `|det M|=1`;
5. a purely Euclidean internal-space model where a non-unimodular argument requires more structure;
6. discreteness of `pi_s(Z^A)`;
7. global realization of a merely formal recurrent object;
8. completeness of a finite corpus/collar bound without an independent theorem.

## Stronger parallel programmes

### G1 / renewal finiteness

G1b-1 is proved; G1b-2 remains the exact missing theorem for finite BPA:

```text
realizable labelled first-return words
=> level-scaled contracting/Rauzy address
=> finite local return types / uniform discreteness
=> G1b-2
=> G1.
```

This route must preserve non-unimodular geometry and label/order data.

### Finite-BPA SCC route

Under G1, nonproductivity reduces to a finite closed/sink carrier and splits by first defect:

```text
K2 == 0  => concentration problem [OPEN]
K2 != 0  => wedge productivity    [OPEN].
```

The carrier-span theorem is proved; full span alone does not imply productivity. The exact 4,554-corpus degree-two and degree-three exclusions remain finite-domain theorems only.

### Realization / MEF route

The realization/coincidence-rank chain is an open bridge / certificate programme. Formal recurrence, global realization, and finite collar survival must remain distinct.

## Source/provenance status

The live project no longer depends on recovery of a historical `PSC_PROOF_v16` file:

- G1b-1 is independently repository-proved;
- degree-two carrier propagation is independently repository-proved;
- concentration is an open mathematical gate, not source-pending;
- the realization chain is an open bridge, not source-pending;
- the P0 manuscript hypothesis/attribution corrections are implemented.

Issue #45 is therefore closed as a completed status/source reconciliation task. The missing v16 artifact remains useful archival metadata only.

## Verification layers

| Priority | Layer | Tool | Scope |
|---|---|---|---|
| **Canonical executable** | `mojo/` | Mojo | Source-of-truth exact implementation: PIP decision, BPA construction, structural C4 machinery, endpoint/C3/C4/defect finite censuses, and optimized corpus instrumentation. The reusable kernels under `mojo/finite_exact/`, `mojo/substitution_dynamics/`, and `mojo/finite_linear_algebra/` are vendored from one pinned `larsbx/finite-math-kernels` commit. |
| Formal state/dependency | `tla/` | TLA+ / TLC | BPA state-machine models and the machine-checked proof-dependency ledger, generated from the proof-record table in `scripts/make_ledger.py` (`tla/ledger.json` is its serialized output). |
| Deductive finite algebra | `PscVerif/` | Lean 4 + Mathlib | Machine-checked finite algebra from the spectral module, with an axiom audit. |
| Secondary oracle | `src/psc_research/` + `tests/` | Python | Independent reference implementations, counterexample generation, and regression/oracle comparisons during migration to canonical Mojo modules. |

The five logical packages vendored from `larsbx/finite-math-kernels` are checked against one commit and per-file digests in `vendored.toml` by `scripts/check_vendored_sync.py` in CI. Status surfaces are checked against the claim ledger in `claim_governance.toml` by the vendored audit package under `tools/claim_governance`. The TLA+ ledger, its TLC models, `tla/ledger.json`, the claim entries of every ledger node, `docs/ledger-index.md`, and the typed relationship graph `docs/claim-relationship-graph.json` are generated from the one table of proof records in `scripts/make_ledger.py` through the vendored `tools/proof_records` package; edit that table and regenerate, since CI fails if any output is stale or hand-edited. Every Mojo test names the ledger claim or the contract it guards (`mojo/psc/claim_tests.mojo`), and the `coverage` check reads the receipts of the run, so a claim whose warrant is a finite computation cannot lose its regression unnoticed.

Run everything:

```bash
./scripts/verify_all.sh
```

Unavailable toolchains are reported as skipped; a skip is not a passing proof.

## Repository layout

```text
.
├── AGENTS.md                   # Mojo-first implementation and optimization policy
├── archive/2026-09-08/        # preserved source corpus: manuscripts, notes, instruments
├── docs/                       # live proof architecture, audits, conjecture ledger
├── manuscripts/                # publication drafts and referee records
├── mojo/                       # canonical exact implementation + finite censuses
│   ├── finite_exact/           # BigZ, Q, and closed intervals from finite-math-kernels
│   ├── substitution_dynamics/  # words, balanced pairs, automaton, vendored (alphabet-generic)
│   ├── finite_linear_algebra/  # Mat3, RREF, rank-three tensors, W_3, vendored
│   ├── psc/                    # reusable Mojo research kernel
│   └── tests/                  # canonical executable regressions
├── tla/                        # TLA+ BPA models; Ledger.tla, MCLedger*, and ledger.json are generated from scripts/make_ledger.py
├── PscVerif/                   # Lean 4 + Mathlib finite-algebra proofs
├── src/psc_research/           # secondary Python reference/oracle layer
├── tests/                      # Python oracle/regression tests
├── scripts/verify_all.sh       # run every verification layer
├── vendored.toml               # commit and digest pins of the five vendored packages
├── .github/workflows/          # automated checks and exact censuses
└── pyproject.toml              # secondary Python oracle metadata
```

## Quick start — Mojo

```bash
cd mojo
pixi run test
pixi run verify
```

Python remains available as an independent oracle:

```bash
python -m venv .venv
. .venv/bin/activate
pip install -e .[dev]
pytest
```

but new executable research logic should not default to Python.

## Standing regime

Unless a note says otherwise:

- `sigma: A -> A+` is primitive;
- `det M_sigma != 0`; **unimodularity is not assumed**;
- `char(M_sigma)` is irreducible over `Q`;
- `beta` is the Perron eigenvalue and Pisot.

## Research discipline

1. Do not promote empirical patterns to theorems.
2. Every load-bearing theorem must be proved in-repo or cited precisely with hypotheses checked.
3. Record failed routes so agents do not repeat them.
4. Keep G1 separate from statements conditional only on a given finite closed carrier.
5. Keep the one-seed overlap theorem distinct from stronger all-seed/all-vertex claims.
6. Do not stack fixed-size sieves without a credible uniform completeness theorem.
7. Default executable work to Mojo; Python is an oracle/prototype.
8. Fail closed on caps/incomplete exact computations and retain replayable countermodels.
