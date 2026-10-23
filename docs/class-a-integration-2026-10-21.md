# Class-A investigation integration, 2026-10-21

This records the accepted CI scope of the class-A investigations and their
reconciliation with a concurrent main contribution. Independent human review
remains pending. Issue #139 and the remaining uniform A/C obligations stay open.

## Results and scope

| Contribution | Established scope | Remaining obligation |
| --- | --- | --- |
| Run-index family, #300 | For every n>=4, the explicit reachable recurrent A_n satisfies n/10 < L(A_n) <= n+2; written proof with coefficient-checked Mojo identities | All-state arbitrary-n coverage and descent |
| Rectangular cover obstruction, #303 | For every n>=4, the explicit real occurrence V_n -> W_n escapes the proposed formal rectangle | No seed reachability or failure of hitting is asserted |
| Complete graphs and independent calibration | Finite survey and exact ordered-occurrence checks at their recorded parameters | No finite survey supplies a uniform cover |

Derivations and replay commands remain in
[p1b-class-a-run-index-2026-10-21.md](p1b-class-a-run-index-2026-10-21.md) and
[class-a-cover-obstruction-2026-10-21.md](class-a-cover-obstruction-2026-10-21.md).

## CI already completed

PR #303 passed all 63 checks on head
`2f30628a77ce5c26166900da2637b55711c245c1` and merged into #300 as
`902c68eebf1ea6ed5a6997a990d1ab6945d01b99`. Both revisions have tree
`b748716497740733539be531697a99d23c140e90`. This was integration into the
research branch, not yet into main.

The dedicated locked native jobs include the run-index identities, complete
finite survey/export and independent calibration, and the rectangular-cover
identities, controls, strict occurrence replay and independent calibration.
The archived snapshot contains every check; raw logs and job metadata for
both dedicated jobs are preserved in
`evidence/class-a-integration-2026-10-21/`. Earlier local minimal-runtime
receipts remain historical, accurately labelled records.

## Concurrent main reconciliation

Main #304, merge `f988d043008ca9d4433c9fe19fb35f10986c6451`, adds the exact
Rauzy-torus diagnostic, its evidence and tests, and two new Pixi task names.
Merge it while retaining both append-only side-note histories. No existing
class-A or accepted class-D mathematical source is edited by the reconciliation.

The pre-repair class-D provenance audit refuses solely because it hashes the
entire current `kernel/pixi.toml`. The two new task names change that file's
bytes, although every accepted task and the whole execution environment are
unchanged. The raw refusal is retained. This does not revoke the historical
class-D acceptance or require another mathematical class-D integration gate.

The auditor now still verifies each archived source digest against the
accepted Git revision. Current mathematical sources, lock, workflows and
other pinned files must still match their accepted digest. Only for
`kernel/pixi.toml`, a difference is also accepted when parsing proves:

1. Every table outside the top-level `tasks` table is exactly unchanged.
2. Every accepted task name still exists with exactly the same definition.
3. Additional entries occur only under that top-level task table.

Canonical comparison preserves scalar types, so a boolean cannot substitute
for an integer. Changed dependencies, platforms, activation scripts, existing
tasks, omitted tasks and type substitutions are explicit refusing controls;
the full auditor also refuses a changed existing task. Lock and historical
workflow mutations retain their prior refusing tests. This exception supplies
no missing source hash or CI receipt and changes no mathematical assertion.

## Replay and integration boundary

```sh
python -m pytest -q tests/test_class_d_integration_ci.py
python tools/check_class_d_integration_ci.py
./tools/verify_all.sh provenance
```

The evidence packet binds the completed #303 CI scope, historical source
comparison and local reconciliation checks. Fresh checks on the combined
#300 head remain the final integration check; a later acceptance must record
its actual head and outcome rather than relabel these historical receipts.
The accepted class-D theorem scope, human-review label and universal #139
status remain unchanged.
