# Pisot Substitution Conjecture Research Program

Automated research workspace for the balanced-pair route to the Pisot Substitution Conjecture (PSC), with emphasis on reproducible experiments, conjecture tracking, manuscript hygiene, and theorem-audit automation.

## Implementation default

**Mojo is the canonical implementation language for executable research code in this repository.** New algorithms, exact finite-state machinery, census code, and performance-sensitive proof instrumentation should land in `mojo/` first and should use Mojo-native algorithm/data-layout optimizations rather than Python-shaped implementations translated mechanically.

Python under `src/psc_research/` is a secondary reference/oracle and prototyping layer. It may independently cross-check Mojo, preserve legacy regressions, or explore a contract before it stabilizes, but once a Mojo implementation exists the Mojo module is the executable source of truth. See `AGENTS.md` for the detailed optimization and review policy.

## Current mathematical state

Canonical archived manuscript: `archive/2026-09-08/manuscripts/PSC_PROOF_v15.tex`. Read `archive/2026-09-08/README_READ_FIRST_2026_09_08.md` first. The corrected working source is `manuscripts/PSC_PROOF_next_source_audit.tex`; it is explicitly not represented as the missing v16 manuscript. The reachable-history audit and per-claim source boundary are in `docs/source-provenance-v16-later-audit-2026-09-12.md`. The live proof state is recorded in `docs/conjecture-ledger.md`, `docs/proof-ladder.md`, the dated weekly ledger `docs/completion-ledger-2026-09-11.md`, and the C4 notes.

- **Level 2:** unique decodability is proved. The withdrawn predecessor-contraction argument does **not** prove finiteness of the balanced-pair automaton `B_sigma`; global finiteness remains hypothesis **G1** in the repository proof architecture.
- **Finite-obstruction reduction:** if `B_sigma` is finite and a nonproductive state exists, the nonproductive subgraph contains a closed/sink recurrent noncoincident SCC. G1 is used at this extraction step. Once a finite closed SCC is given, most subsequent C4 structural lemmas do not separately require global BPA finiteness.
- **Boundary route:** the proved sufficiency chain is

  ```text
  C4  =>  C3-local  =>  C2  =>  C1 (SCC Producer),
  ```

  and, with G1, `C1 => PDS` in the standing alphabet-3 PIP regime. These are one-way proof-dependency arrows, not equivalences.
- **C4 structural stack now proved:** endpoint-map synchronization quotients; the unconditional globally-synchronizing-endpoint eliminator; the 1/3/9 endpoint-signature bound; the Parikh intertwiner `P_C N_C = M_sigma P_C` with `rank P_C=3`, `|C|>=3`, and `rho(N_C)=beta` for a strict closed nonproductive component; the `Z/2` orientation cocycle and even/odd matrices `N=A+B`, `S=A-B`; signed first-defect intertwiners; degree-3 low-growth/centralizer restriction; degree-4 and arbitrary-degree spectral sieves; the degree-2 parity size sieve; and the ordered mid-area factorization identity.
- **Three-state calibration is intentionally capped:** the trace, mean-area, and integral-lattice layers for `|C|=3` are useful negative-template diagnostics, but they are not a plausible complete proof spine. No further three-state sieve should be stacked without a uniform completeness theorem.
- **Exact finite evidence:** in the established 4,554 alphabet-3 PIP substitutions with image lengths `<=3`, all BPA builds terminate below the cap and every observed sink is productive. Among 385,926 reachable noncoincident states, 385,902 have first defect degree 2, 24 have degree 3, and none has degree `>=4`. The 24 degree-3 occurrences all leak to coincidence within two inflations.
- **Active theorem target:** a uniform-in-`|C|` C4 argument using the actual prefix-difference return structure and recognizability/supertile alignment. The synthetic G/F calibration shows that incidence, spectra, endpoint phases, and even actual balanced-state columns can all be correct while the prescribed zero-return child factorization is wrong.

### G1 and the literature

The balanced-pair literature states, for irreducible Pisot substitutions, an equivalence between pure discrete spectrum and termination with coincidence of the standard balanced-pair algorithm, and notes that a seed `(ij,ji)` suffices for the criterion. The repository does **not yet** identify this automatically with its normalized all-seed graph `B_sigma`: `docs/bpa-literature-bridge.md` tracks the exact definition/reachability bridge required before the ledger promotes a bare `PDS => G1` theorem.

This repository is for automated research support, not for hiding conjectural steps. Anything unproved belongs in `docs/conjecture-ledger.md` or an issue.

## Verification layers

| Priority | Layer | Tool | Scope |
|---|---|---|---|
| **Canonical executable** | `mojo/` | Mojo | Source-of-truth exact implementation: integer/rational kernel, PIP decision, BPA construction, structural C4 machinery, endpoint/C3/C4/defect finite censuses, and optimized corpus instrumentation. |
| Formal state/dependency | `tla/` | TLA+ / TLC | BPA state-machine models and the machine-checked proof-dependency ledger. |
| Deductive finite algebra | `PscVerif/` | Lean 4 + Mathlib | Machine-checked finite algebra from the spectral module, with an axiom audit. |
| Secondary oracle | `src/psc_research/` + `tests/` | Python | Independent reference implementations, counterexample generation, and regression/oracle comparisons during migration to canonical Mojo modules. |

`docs/verification-architecture.md` states what each layer does and does not establish and records known source/interface discrepancies, including the signed-vs-unsigned SCC transfer correction.

Run everything:

```bash
./scripts/verify_all.sh
```

Each layer is skipped with a notice if its toolchain is absent, so a partial environment reports honestly instead of passing vacuously.

## Repository layout

```text
.
├── AGENTS.md                   # Mojo-first implementation and optimization policy
├── archive/2026-09-08/        # preserved source corpus: manuscripts, notes, instruments
├── docs/                       # live proof architecture, audits, conjecture ledger
├── mojo/                       # canonical exact implementation + finite censuses
│   ├── psc/                    # reusable Mojo research kernel
│   └── tests/                  # canonical executable regressions
├── tla/                        # TLA+ BPA models and proof-dependency ledger
├── PscVerif/                   # Lean 4 + Mathlib finite-algebra proofs
├── src/psc_research/           # secondary Python reference/oracle layer
├── tests/                      # Python oracle/regression tests
├── scripts/verify_all.sh       # run every verification layer
├── .github/workflows/          # automated checks and exact censuses
└── pyproject.toml              # secondary Python oracle metadata
```

## Quick start — Mojo

```bash
cd mojo
pixi run test
pixi run verify
```

Run the exact census drivers from `mojo/` as needed; they share the canonical `psc` kernel. Issue #2 tracks the remaining work to make the exact PIP screen the single documented reproducible corpus-export interface with deterministic JSONL output.

Python remains available as an independent oracle when a cross-check is useful:

```bash
python -m venv .venv
. .venv/bin/activate
pip install -e .[dev]
pytest
```

but new executable research logic should not default to Python.

## Standing regime

Unless a note says otherwise:

- `sigma: A -> A+` is primitive.
- `det M_sigma != 0`; **unimodularity is not assumed**.
- `char(M_sigma)` is irreducible over `Q`.
- `beta` is the Perron eigenvalue and Pisot.

## Research discipline

1. Do not promote empirical patterns to theorems.
2. Any theorem used in a proof must be either proved in-repo or cited precisely.
3. Any failed attack route gets recorded so agents do not repeat it.
4. Keep G1 separate from statements conditional only on a given finite closed SCC.
5. Treat `C4 => C3-local => C2 => C1` as a one-way sufficiency chain unless a converse is separately proved.
6. Do not stack additional fixed-size sieves without a credible uniform completeness statement.
7. **Default executable work to Mojo.** Python-only theorem-support implementations require an explicit temporary rationale and a planned Mojo port.
8. **Optimize for Mojo.** Prefer fixed-dimension exact arithmetic, streaming accumulators, precomputed substitution-local data, compact index-based graph kernels, reused storage, and fail-closed invariants over Python-style dynamic/object-heavy hot loops.
