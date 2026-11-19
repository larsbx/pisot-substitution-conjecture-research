# Witness selection under (NM_V) — local acceptance, 19 November 2026

Base: `main@9774624`, the merge of #613. The
[witness-selection note](../../docs/c4-witness-selection-2026-11-19.md) carries the
statements and the non-claims. Runtimes: Mojo 1.1.0.dev2026090805 from
`kernel/pixi.lock`; Lean `v4.34.0-rc2` with the pinned Mathlib. Hosted CI has not run.

| Command | Exit | Log |
| --- | --- | --- |
| `(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_zero_fibre_asymptotes.mojo)` | 0 | [zero-fibre-asymptotes.log](zero-fibre-asymptotes.log) |
| `(cd kernel && pixi run --locked mojo run -I . nmv_census.mojo)` | 0 | [nmv-census.log](nmv-census.log) |
| `python3 -m pytest -q tests/test_nmv_literal_rays_oracle.py` | 0 | the independent oracle still confirms all 96 failing pairs |
| `./tools/check_c4_periodic_partner.sh` | 0 | [periodic-partner-gate.log](periodic-partner-gate.log) (marker lines only): ten modules, 531 compiled declarations, standard axioms only |

Source digests (sha256):

| File | Digest |
| --- | --- |
| `kernel/psc/zero_fibre_asymptotes.mojo` | `c5ff54e185f2f7828a6082d1abc8413417c744564c5fb1d6ac0870c076e6fe90` |
| `kernel/nmv_census.mojo` | `809ad900de55a46073fd50726bfc358aa9f8617473c9078367f8a71c7f67c515` |
| `kernel/tests/test_zero_fibre_asymptotes.mojo` | `f7b1dd63d2dba37d4259f44cf19f5cdcd232a0babdb73d0d21bff60d43443a12` |
| `proof/PscVerif/PscVerif/PeriodicPartnerSelection.lean` | `13c39c9aea34b64f377cbfd3eb074fe436a952e8f0d806eb9ed37f6c2ef70e41` |
