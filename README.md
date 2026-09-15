# Pisot Substitution Conjecture Research Program

Automated research workspace for the Pisot Substitution Conjecture (PSC), with emphasis on reproducible experiments, conjecture tracking, manuscript hygiene, theorem-audit automation, and exact finite certificates.

## Implementation default

**Mojo is the canonical implementation language for executable research code in this repository.** New algorithms, exact finite-state machinery, census code, and performance-sensitive proof instrumentation should land in `mojo/` first and use Mojo-native data/layout optimizations.

Python under `src/psc_research/` is a secondary reference/oracle and prototyping layer. Once a Mojo implementation exists, the Mojo module is the executable source of truth. See `AGENTS.md` for the detailed policy.

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

### Current theorem target

Issue #84 is the primary completion issue. The preferred attack is to assume a **minimal finite reachable child-closed nonproductive overlap set** and combine:

- full rational rank;
- inherited child-count spectrum;
- ordered exact descendant offsets;
- prefix-Parikh boundary avoidance;
- Pisot contraction;

until a boundary hit / coincidence or an impossible finite configuration is forced.

Proving all seeds or every overlap vertex is stronger than necessary; one legal swap seed per substitution suffices for Theorem 5.38.

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
| **Canonical executable** | `mojo/` | Mojo | Source-of-truth exact implementation: PIP decision, BPA/overlap construction, structural machinery, exact arithmetic, and finite censuses. |
| Formal state/dependency | `tla/` | TLA+ / TLC | State-machine models and machine-checked proof-dependency ledger. |
| Deductive finite algebra | `PscVerif/` | Lean 4 + Mathlib | Machine-checked finite algebra with an axiom audit. |
| Secondary oracle | `src/psc_research/` + `tests/` | Python | Independent reference implementations and regressions. |

Exact arithmetic lives in `mojo/finite_exact/`, vendored from `larsbx/NLAP-JT` with a pinned sync check.

Run everything:

```bash
./scripts/verify_all.sh
```

Unavailable toolchains are reported as skipped; a skip is not a passing proof.

## Repository layout

```text
.
├── AGENTS.md
├── archive/2026-09-08/
├── docs/
├── manuscripts/
├── mojo/
│   ├── finite_exact/
│   ├── psc/
│   └── tests/
├── tla/
├── PscVerif/
├── src/psc_research/
├── tests/
├── scripts/verify_all.sh
└── .github/workflows/
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
