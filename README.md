# Pisot Substitution Conjecture Research Program

Automated research workspace for the balanced-pair route to the Pisot Substitution Conjecture (PSC), with emphasis on reproducible experiments, conjecture tracking, manuscript hygiene, and theorem-audit automation.

## Current mathematical state

Canonical manuscript: `archive/2026-09-08/manuscripts/PSC_PROOF_v15.tex`. Read
`archive/2026-09-08/README_READ_FIRST_2026_09_08.md` first.

- **Level 2:** unique decodability is proved. Finiteness of the balanced-pair
  automaton `B_sigma` is **not**: it is hypothesis **G1**. The
  predecessor-contraction proof of PSC_PROOF_v5 Theorem 5.1 is withdrawn
  (`beta * L(s') <= L(s) + D` is false; worst ratio 8.0, excess unbounded).
  Finiteness is unconditional only for `|A| = 2` and verified families.
- **Level 3:** the open gap is the **SCC Producer Theorem** — every recurrent
  noncoincident SCC of `B_sigma` produces a coincidence sibling at some
  inflation step.
- The main result is a **boxed conditional**: `B_sigma` finite (G1) + SCC
  Producer implies PDS. `tla/Ledger.tla` encodes that dependency structure and
  `tla/check.sh` verifies mechanically that neither hypothesis can be dropped.
- The old cycle-exclusion route is retired: recurrent noncoincident cycles may
  exist, and displacement nonvanishing is not the right invariant.
- The active next target is the **Boundary Synchronization / Nonsynchronizing
  Trap** layer.

This repository is for automated research support, not for hiding conjectural
steps. Anything unproved belongs in `docs/conjecture-ledger.md` or an issue.

## Verification layers

| Layer | Tool | Scope |
|---|---|---|
| `mojo/` | Mojo | Exact integer/rational kernel: seeds, `W_3`, `Theta`, `Phi_3`, the PIP decision procedure, `B_sigma`. Ten certificate checks and the exhaustive alphabet-3 census. |
| `tla/` | TLA+ / TLC | `B_sigma` as a state machine (G1 and SCC Producer, in scope), plus a machine-checked proof-dependency ledger. |
| `PscVerif/` | Lean 4 + Mathlib | Machine-checked proofs of the Spectral module's finite algebra, with an axiom audit. |

`docs/verification-architecture.md` says what each layer does and does not
establish, and records three discrepancies found while mechanising
`PROOF_CERTIFICATE.md`.

Run everything:

```bash
./scripts/verify_all.sh
```

Each layer is skipped with a notice if its toolchain is absent, so a partial
environment reports honestly instead of passing vacuously.

## Repository layout

```text
.
├── archive/2026-09-08/        # preserved source corpus: manuscripts, notes, instruments
├── docs/                      # proof architecture, conjecture ledger, verification architecture
├── mojo/                      # exact computational kernel (Mojo)
│   ├── psc/                   #   modules
│   ├── tests/                 #   kernel regression tests
│   ├── verify.mojo            #   the certificate, executable
│   └── census.mojo            #   exhaustive alphabet-3 PIP census
├── tla/                       # TLA+ specs, models and check.sh
├── PscVerif/                  # Lean 4 + Mathlib proofs
├── src/psc_research/          # reusable BPA and boundary-sync tooling (Python)
├── tests/                     # Python regression tests
├── scripts/verify_all.sh      # run every layer
├── .github/workflows/ci.yml   # automated runner
└── pyproject.toml             # Python project metadata
```

## Quick start

```bash
python -m venv .venv
. .venv/bin/activate
pip install -e .[dev]
pytest
```

Run the boundary-sync demo:

```bash
python -m psc_research.examples
```

Run a random sweep:

```bash
python scripts/sweep_boundary_sync.py --trials 500 --seed 1729
```

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
4. Scripts must include named examples: Tribonacci, flipped-Tribonacci, and Smith-type substitutions.
5. All manuscript edits should preserve the distinction between proved content, conditional results, and open conjectures.
