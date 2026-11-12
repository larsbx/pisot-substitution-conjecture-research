# Named overlap balance: evidence boundaries

The mathematical argument and replay commands are in
[the implementation note](../../docs/c4-named-overlap-balance-2026-11-11.md).
[PR #549](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/549)
records candidate revisions and subsequent hosted results as they become available.
The first published source was `6472eab38efa623640f00285954b8525a56f6e8e`,
tree `cd20306d416c41aed17bf2cbd88d088e92ce5ec8`; its new Lean acceptance was
pending at publication.

## Existing-contract replay

`baseline-receipt.json` binds the three archived native tests and three
independent Quint suites to clean main
`765bb39c83035b5ccacbc8115ecc26acc4111865`. The kernel tree and all model/runner
Git objects listed there are unchanged in the first candidate. These
replays test the reused interval, literal occurrence, transpose and finite
duality contracts; they do not decode the new mathematical finite domains.

| Suite | Passed tests | Rejected assertion-reaching mutations |
| --- | ---: | ---: |
| Physical mass Quint | 20 | 6 |
| Overlap mass Quint, serialized retry | 16 | 9 |
| Inverse occurrence Quint | 18 | 13 |

Native contract receipts are retained in `baseline-native/`. The native
overlap checks include 1,600 bounded physical budgets and 512 directed
three-state quotient cases. The inverse checks include 6,400 digit
identities, 25,600 two-step histories, 64 declared swap-closed domains and
450 nonunit adjugate reconstructions. These are finite controls, not PIP
class theorems.

The original scratch paths inside receipts remain unchanged as provenance.
Their archived locations are:

| Original run directory | Archive directory here |
| --- | --- |
| `baseline_native/` | `baseline-native/` |
| `baseline_quint/physical/` | `baseline-quint-physical/` |
| `baseline_quint/overlap_retry/` | `baseline-quint-overlap/` |
| `baseline_quint/inverse/` | `baseline-quint-inverse/` |
| `baseline_quint/overlap/` | `historical-failed-quint-overlap/` |

## Failed attempts and development imports

The first overlap Quint attempt reached no tests and failed. It remains in
`historical-failed-quint-overlap/`; the successful retry has a separate
receipt. `local-development-history.json` also preserves interrupted and
signal-killed initial Lean probes. They supply no mathematical verdict.

Local development used source-matched pinned imports. Those probes are
distinct from the canonical `tools/check_lean.sh` gate, which builds a fresh
source workspace and performs the compiled declaration/axiom audit.
Initial later probes of the new budget module stalled before reaching any
new declaration. Inspection found an upstream blanket Mathlib import in
`Cyclicity.lean`; the tracked repair narrows imports while retaining all
existing theorem statements and proof bodies. The exact import-only
replacement and successful pinned compiler run are retained in
`import-repair/`; its first missing-import diagnostic is retained separately.
This repairs the development startup blocker. Acceptance of the new
theorems still requires their own compilation and the full hosted audit.

All 39 new theorem declarations passed source-matched development
compilation: eight in the generic budget adapter, nine direct controls and
22 in the named Haar bridge. Their receipts and actual compiler logs are
in `development/`. The named bridge passed its first actual elaboration in
119.3 seconds following a 42-module source/dependency build. Earlier
elaboration failures and the successful control retry are distinguished
there. The local classical decision instances and finite-index/cardinality
proof repairs add no mathematical premises. These development results
remain separate from the complete isolated-source hosted audit.

Two development logs retain compiler-emitted trailing whitespace and are
therefore stored as `.log.gz`, preserving their exact original bytes.
`development/compressed-log-index.json` maps the original receipt names to
those archives and records their decompressed hashes. The other development
logs remain plain text.

`historical-hosted/` preserves the first candidate's failed full-Lean,
physical-mass and packet-bridge audits at `6472eab3`. All three rejected the missing classical
decidability in the budget theorem statements; later dependent modules were
not accepted. Raw logs are losslessly gzip-compressed, with decompressed
SHA-256 values and readable diagnostic extracts. These failed receipts stay
failed even though the corrected budget passed development compilation.
The corrected published revision must obtain its own complete audit.

## Required acceptance

Only a successful complete isolated-source build at the published candidate
and a compiled audit reaching every inventoried declaration supplies Lean
acceptance for the new adapter. The first candidate has 39 new theorem
declarations. The hosted audit allows only the repository's established
`propext`, `Classical.choice` and `Quot.sound` axiom budget. Exact hosted
URLs and revision results are maintained in the PR, rather than inferring
new-source acceptance from the older native/Quint controls.

`SHA256SUMS` authenticates the archived baseline logs, receipts and history.
It does not claim to authenticate future hosted artifacts or constitute
the new Lean acceptance receipt.
