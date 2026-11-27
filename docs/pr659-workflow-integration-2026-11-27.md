# PR 659: preserve the incoming workflow hardening

Main advanced from `47db0f142573ebdd75cab7ecdaf1345e2e149df2` to
`4c95c7b6da647ed3c1c233174783316c41826751` through
[PR 661](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/661)
while the integrated head `d9850d406900fca9fa4682f296faa853c44d41aa`
was awaiting hosted execution.

The incoming change modifies only
[the physical-mass workflow](../.github/workflows/physical-mass-kernel.yml).
It raises the full Lean job limit from 35 to 60 minutes and authenticates
its existing official GitHub asset downloads with the job token. The merge
preserves both authenticated downloads, their exact asset URLs, checksums,
revision binding, build commands and audit requirements. It retains this
branch's 180-minute full Lean allowance instead of the incoming 60 minutes.
The merged workflow is byte-identical to main after that single timeout
replacement; no other workflow edit is introduced.

The allowance is supported by the observed 35-minute timeout documented in
[the preserved integration packet](../evidence/pr659-main-integration-2026-11-27/ci-diagnosis.md)
and by the existing 180-minute overlap gate. A previous successful complete
overlap-packet job lasted 77 minutes 30 seconds:
[run 46000930013, job 140512068044](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/46000930013/job/140512068044).
That historical duration is evidence that 60 minutes need not suffice; it
is not acceptance of the present tree.

No mathematical source, generated inventory, pinned dependency or historical
evidence packet changes in this second integration. The only additional
files are this note and an appended side-ledger entry. Thus the prior local
302-test and 223-test records retain their precise earlier scope. They are
not rewritten as completed hosted checks for a later commit. The PR records
the current published head and its hosted outcomes separately.

The earlier dedicated BH success and the interrupted full-bank jobs remain
attached to `ab71641`. Any runs at `d9850d4` are likewise historical once the
second integration is published. No conjecture status or independent-review
label changes here.
