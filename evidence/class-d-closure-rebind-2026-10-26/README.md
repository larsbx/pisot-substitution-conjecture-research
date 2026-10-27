# Class-D closure rebind, 2026-10-26

Provenance only. This packet asserts no mathematics.

**Scope.** The class-D acceptance of 2026-10-21 (accepted head `a9457d9`) froze
byte for byte the import closure of `kernel/class_d_plus_positive_b_chambers.mojo`
and the provenance checker `tools/check_class_d_assembly_evidence.py`. PR #345
edited one file of that closure and that checker. This packet admits exactly
those two edits, at exactly the pinned bytes, and nothing else.

**What is rebound, and why.**

- `kernel/symbolic_line_certificate.mojo` (`native-replay`): the Theorem E pin
  tables moved into the data file `kernel/symbolic_line_pins.txt`, which only
  `report` and `report_wedge` read at run time. `certify` and `certify_wedge`
  are unchanged, and the class-D plus chambers never call `report`. The plus-chamber
  aggregate was replayed natively on a commit carrying exactly these bytes.
- `tools/check_class_d_assembly_evidence.py` (`provenance-tool`):
  `check_hashes` now also accepts a digest that this packet admits.

**Receipt.** The workflow run is 40427511692 and the job is `chambers`, id
121936856950. Head `7a36f91` was tested as the merge commit `8079447`, whose
commit object is `tested-merge.commit`. The complete raw job log is
`121936856950.log.gz`. It contains the native receipt
`CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED wedges= 6 explicit_lines= 6
boundary_lines= 73 finite_prefix_pip= 952 max_symbolic_vertices= 164`. The job
metadata is in `jobs.json`. `tools/check_class_d_closure_rebind.py` validates
all of this. That includes the merge's parent, the bytes at the rebind head
and in the tree, the job's head, conclusion and steps, and the log digest.

**Non-claims.** This is a hosted-CI exact-revision receipt, not independent
validation (`independent_human_review: false`). The 2026-10-21 packets are
unchanged, and their results are not regenerated. Any further edit to a
rebound file is refused.
