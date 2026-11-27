# Zero-fibre proof increment: integration against current main

The user authorized opening a PR against `main` and merging after reviewing
local commit `05ace7234df2aff5e84903cdb7c3bfbdbd2813ea`. This note records
the integration of that reviewed result. Its mathematical scope is unchanged:
the full zero-fibre characterization and explicit seam/interior witnesses
are proved, while universal anchor coincidence and the invariant-measure
spectral conclusion remain unproved in Lean.

## Source ancestry

| Input | Exact revision | Role |
| --- | --- | --- |
| Current main at integration | `c4cc728883451a9de9741eeb74837f2fc3c080e2` | Includes merged PR #644's graded-lift work |
| PR #643 | `7a5025ed7b8104413477ea7fbd15b52206e0959c` | Unmerged prerequisite: actual finite-to-one solenoid factor |
| Reviewed proof increment | `05ace7234df2aff5e84903cdb7c3bfbdbd2813ea` | Seven new proof modules and scoped audit |

The PR against main includes the exact #643 commit as a prerequisite and
the reviewed increment's source contents. It preserves the exact #643
commit in its ancestry. The local review commit identifies the original
reviewed artifact; publication may use a distinct commit identity with
the same verified source contents. No proof body was edited to resolve
the integration.

## Reconciliation

Main's intervening #644 changes affect the graded-lift module, its
periodic-partner audit/workflow, documentation and generated inventories.
They intersect none of the 50 baseline or eight candidate source files
used by the recorded scoped acceptance. The three pinned Lean/Lake
configuration files are also unchanged.

The integration preserves the graded-lift import and the solenoid and
zero-fibre imports. It retains both sides of the append-only findings
ledger and regenerates `docs/proof-bank.md` and `proof/proof-bank.json`
from the combined source tree. Generated inventories were not resolved
by choosing one branch's stale output.

## Acceptance and replay

The original [review](c4-zero-fibre-witness-review-2026-11-21.md) and
[evidence](../evidence/c4-zero-fibre-witnesses-2026-11-21/README.md) remain
historical records of the local review stage. In particular, the original
`candidate-reviewed-source-sha256.json` binds the reviewed commit, rather
than the subsequently reconciled aggregate imports, ledger and proof bank.

The integration receipts under
`evidence/c4-zero-fibre-witnesses-2026-11-21/integration/` check that all
58 accepted source inputs and three configurations still match, rerun
both scoped audit fixtures against the accepted strict-build artifacts,
and record the combined inventory and pin checks. These audit reruns are
not represented as a second complete source rebuild.

| Audit | Owned declarations | Theorem constants | Endpoint types | Refusal controls |
| --- | ---: | ---: | ---: | ---: |
| Exact #643 family closure | 1,053 | 905 | 35 | 70 |
| New zero-fibre modules | 49 | 45 | 38 | 76 |

Both scopes permit only `propext`, `Classical.choice` and `Quot.sound`.
The original acceptance rebuilt project sources while reusing pinned
external dependency artifacts. It did not run the complete isolated
shell gate or establish hosted acceptance. Those limits carry forward.

The updated repository entry point is
`tools/check_c4_parameter_family.sh`; the focused commands remain in the
review note. Hosting or merging this result does not turn queued
workflows into passing acceptance or supply the missing universal
witness theorem.
