# Boundary synchronization automation ledger

## Added surface

- `docs/boundary-synchronization.md` documents the Boundary Synchronization Lemma, the synchronizing-end criterion, and the nonsynchronizing trap normal form.
- `src/psc_research/` contains lightweight Python BPA and boundary-sync utilities.
- `scripts/sweep_boundary_sync.py` provides a small random sweep driver.
- `scripts/audit_manuscript.py` guards against known stale manuscript claims.
- `.github/workflows/boundary-sync.yml` runs the focused lightweight checks.

## Regression targets

The lightweight tests cover:

- balanced-pair decomposition basics;
- Tribonacci and flipped-Tribonacci boundary synchronization;
- Smith-style partial synchronization, where neither endpoint map is globally synchronizing but the Boundary Synchronization Lemma still applies;
- audit rejection of known stale statements.

## Current caveat

This layer is not a proof of PSC. It provides a boundary normal form for the SCC Producer obstruction. The next conjectural target remains the Newborn Synchronizing Boundary Conjecture.
