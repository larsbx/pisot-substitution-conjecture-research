# Class-D closure rebind, 2026-10-30

Provenance only. This packet asserts no new mathematics.

**Scope.** The class-D acceptance of 2026-10-21 (accepted head `a9457d9`) froze
the import closure of `kernel/class_d_plus_positive_b_chambers.mojo` byte for
byte. The fit-first change edits one file of that closure,
`kernel/psc/symbolic_line.mojo`. This packet admits exactly that edit, at
exactly the pinned bytes, and nothing else. The 2026-10-26 packet's two
rebound files are untouched.

**What is rebound, and why.**

- `kernel/psc/symbolic_line.mojo` (`native-replay`): the line closure now fits
  both walls of a run block first and clips them to the run ends by exact
  integer signs in `q`. #288's endpoint tests at `beta` run only where a wall
  has no certified fit. Both paths are exact, so only the sign reads and floors
  move: every pinned Theorem E line and wedge returns to its pre-#288 floor
  (`docs/p1b-boundary-hitting-progress-2026-10-08.md`, §4b correction of
  2026-10-30). The complete plus-chamber aggregate was replayed in CI on a
  commit carrying exactly these bytes.

**Receipt.** Workflow run 41066419210 (`workflow_dispatch`), job `chambers`, id
124098895410, ran on the rebind head `bb69c6c` itself. No merge commit was
tested, so the v2 format binds the head directly. The complete raw job log is
`124098895410.log.gz`. It shows the head checked out and contains the native
receipt

`CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED wedges= 6 explicit_lines= 6
boundary_lines= 51 finite_prefix_pip= 287 max_symbolic_vertices= 164`.

The same six cores and six interface lines certify; the lower wedge floors
return 51 strips instead of 73 and 287 finite-prefix obligations instead of
952, with the same 164 maximum vertices. A local native run on the same bytes
printed the same line (3981 s). The job metadata is in `jobs.json`.
`tools/check_class_d_closure_rebind.py` validates all of this, including the
bytes at the head and in the tree, the job's head, conclusion and steps, the
log digest, and the receipt's shape.

**Non-claims.** This is a hosted-CI exact-revision receipt, not independent
validation (`independent_human_review: false`). The 2026-10-21 packets and
their counts are unchanged and stay the accepted receipts. Any further edit to
a rebound file is refused.
