# Class-D assembly rebind, 2026-10-30

Provenance only. This packet asserts no new mathematics.

**Scope.** The class-D acceptance of 2026-10-21 (accepted head `a9457d9`) froze
the assembly `kernel/psc/class_d_assembly.mojo` and its test byte for byte.
Under the fit-first line closure (PR #407), the fresh minus aggregate that
`class-d-assembly.yml` feeds the assembly prints the two minus-strip receipts
with floors 19 and 21 instead of 42 and 72. Vertex counts 140/137 are unchanged,
every prefix member is PIP and hitting, and the independent `Q(beta)` oracle
agrees. The frozen assembly requires those receipt lines exactly, so it
refused the fresh run. This packet admits exactly the two edited files at
exactly the pinned bytes:

- `kernel/psc/class_d_assembly.mojo` (`assembly-replay`): the two minus-strip
  receipts at 19/21. The accepted plus receipt (73 strips, 952 obligations, the
  immutable 2026-10-20 aggregate the assembly consumes) is unchanged.
- `kernel/tests/test_class_d_assembly.mojo` (`assembly-replay`): the fixture
  at 19/21, plus a control that the accepted run's 42/72 receipts now refuse.

**Receipt.** The provenance gate of `class-d-assembly.yml` refuses an edited
accepted source before it replays anything. `class-d-assembly-replay.yml`
therefore runs the same replay steps without that gate:
- the fresh minus aggregate and seed controls;
- the independent calibration and receipt agreement;
- the assembly with the immutable plus receipt.

Run 41116962718, job `assembly-replay` (id 124273585897), ran on PR #407's
head `ded8203c`. It tested the merge commit `4e97eedb`, whose commit object
is `tested-merge.commit`. The complete raw job log, `124273585897.log.gz`,
contains the fresh strip receipts and

`CLASS_D_ASSEMBLY_CANDIDATE plus_positive_b=complete minus_residual=complete
plus_b0=complete inherited_wedges=ClassDWedgeBoundaryHitting
target=offset_zero integration=pending universal_139=open`.

`tools/check_class_d_closure_rebind.py` validates the merge, the bytes at the
head and in the tree, the job's head, conclusion and required steps, the log
digest, and the receipt.

**Why a separate packet.** #407 merged before this packet was recorded, so
`main` refused its own assembly until now. The engine rebind
(`class-d-closure-rebind-2026-10-30`) is unchanged.

**Non-claims.** This is a hosted-CI exact-revision receipt, not independent
validation (`independent_human_review: false`). The 2026-10-21 packets are
unchanged. Any further edit to a rebound file is refused.
