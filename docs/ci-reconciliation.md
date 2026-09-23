# CI reconciliation

A focused boundary-synchronization workflow now exists at:

- `.github/workflows/boundary-sync.yml`

The pre-existing repository also had a large estate workflow at:

- `.github/workflows/ci.yml`

The large workflow included provenance checks, Python governance checks, Mojo kernels, and exact census gates. Because this repository is not a fresh scaffold, future changes must treat the estate workflow as authoritative unless deliberately superseded.

## Required reconciliation

- Compare current `.github/workflows/ci.yml` with commit `e0bff9eb1a12cca1ee885918148156b9d4fbc0a1`.
- Restore any estate gates that were unintentionally removed.
- Keep boundary-sync checks additive.
- Do not use the lightweight boundary-sync workflow as a replacement for full estate CI.
