# Repository integration note

This repository already contained a substantial PSC research estate before the boundary-synchronization automation layer was added.

## Current integration stance

- The boundary-synchronization layer is additive.
- Historical archives, Mojo census code, proof ledgers, and prior manuscript checks remain part of the broader estate.
- New source-hygiene checks should run against the canonical current surface unless explicitly auditing the full archive.

## Canonical current surface for lightweight audit

The lightweight `scripts/audit_manuscript.py --strict-current` mode currently audits:

- `README.md`
- `docs/proof-ladder.md`
- `docs/conjecture-ledger.md`
- `docs/boundary-synchronization.md`
- `docs/automation-protocol.md`

This is intentional: archives may contain stale or superseded claims as historical records.

## Estate CI caution

The pre-existing `.github/workflows/ci.yml` contained a large estate workflow with Mojo census gates and provenance checks. Boundary-sync checks should be added as a separate workflow rather than replacing those gates. If CI history shows that the estate workflow was collapsed or simplified, restore it from the last known good commit and keep `.github/workflows/boundary-sync.yml` as the focused lightweight gate.
