# PR #326 / #327 integration receipts

Parents: #326 `ed51df01080c64039c803b52c585291dd15c5dd3` and main
`2bfb350` (#327). See `docs/issue139-ac-integration-2026-10-23.md`.

- `canonical.log`: fresh native replay of main's 18 default rays, full
  finite prefixes from n=0 and two occurrence cross-checks per ray.
- `rank.log`: fresh native replay of #326's eight alternative rank tables,
  all original floors/counts, finite prefixes, two occurrence cross-checks
  per ray and corruption/refusal controls.
- `typed.log`: finite carrier regression and the updated budget refusal at 49.
- `rank-synthesis.log`: five `--rank-tables` synthesis replays; all four
  standard/alternative table files retain their original bytes.
- `python.log`: combined exact-oracle, countercontrol, source-inventory,
  integrity and workflow regressions.
- `mapping.json`: original and current table digest mapping and C source checks.

Runtime is the same minimal lock-matched Mojo 1.1.0.dev2026090805 compiler
used by #326, not a full local Pixi installation. Native programs were rebuilt
from the integrated sources. Neither original evidence packet was edited.
C sources and their native dependency inputs were not changed by the merge;
its historical receipts are not presented as a new execution. Hosted CI is
required separately. The proof-bank generator is repaired and both outputs
are regenerated, including the exact C4 locator.

Replay from the repository root:

```bash
python -m pytest -q tests/test_class_a_residue_rays.py tests/test_class_a_d2_plus_ray_carrier.py tests/test_issue139_gap_four.py tests/test_proof_bank.py tests/test_recorded_data_integrity.py tests/test_line_certificate_workflow.py tests/test_class_d_integration_ci.py
bash tools/verify_all.sh provenance
```

From `kernel/`, use `pixi run --locked mojo run -I .` on
`tests/test_class_a_residue_rays.mojo`, `tests/test_class_a_gap_four_rank.mojo`
and `tests/test_class_a_typed_carrier.mojo`. The shared A workflow runs both
registries. C's dedicated workflow remains in place.

No new mathematical promotion or universal #139 closure is asserted.
