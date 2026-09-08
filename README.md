# Pisot Substitution Conjecture Research Program

Automated research workspace for the balanced-pair route to the Pisot Substitution Conjecture (PSC), with emphasis on reproducible experiments, conjecture tracking, manuscript hygiene, and theorem-audit automation.

## Current mathematical state

The project is organized around the v12.1 reframing:

- **Level 2:** unique decodability + phase padding + predecessor contraction gives finiteness of the balanced-pair automaton `B_sigma` under the primitive irreducible Pisot regime.
- **Level 3:** the open gap is the **SCC Producer Theorem**: every recurrent noncoincident SCC of `B_sigma` produces a coincidence sibling at some inflation step.
- The old cycle-exclusion route is retired: recurrent noncoincident cycles may exist, and displacement nonvanishing is not the right invariant.
- The active next target is the **Boundary Synchronization / Nonsynchronizing Trap** layer: prove that no recurrent noncoincident SCC can keep every zero-return boundary trapped forever in nonsynchronizing prefix/suffix endpoint cores.

This repository is for automated research support, not for hiding conjectural steps. Anything unproved belongs in `docs/conjecture-ledger.md` or an issue.

## Repository layout

```text
.
├── docs/                      # proof architecture, conjecture ledger, research notes
├── src/psc_research/           # reusable BPA and boundary-sync tooling
├── tests/                     # regression tests for known examples and invariants
├── .github/workflows/ci.yml   # automated test runner
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
