# Class-A run-index investigation — 2026-10-21

Uniform written argument and exact scope:
`docs/p1b-class-a-run-index-2026-10-21.md`.

- `survey.log`: canonical coefficient identities and every complete graph
  n=1..24; explicit family replay n=4..24. All exits are recorded separately.
- `tests.log`: canonical controls, including the exact n=18 recurrent depth-15
  countermodel and the family replay at n=64.
- `graph-n4.log`, `graph-n18.log`: complete integral labelled graphs, ordered
  occurrences, seed identities and first-hit depths. V records are
  `V n id top bottom wx wc wy depth`; E records are
  `E n parent_id child_id top_index bottom_index`; indices are zero-based.
  SUMMARY is `n vertices max_depth recurrent_vertices recurrent_max_depth
  explicit_A_n_depth`. Coincidences are terminal.
- `oracle-n18.json`: independent Fraction-field reconstruction agrees on all
  835 vertices, 17,178 occurrences, seeds and depths. It checks occurrence
  uniqueness, legal indices and strict interiority as well as full support.
- `python-controls.log`: independent n=4 reconstruction and six damaged-export
  controls. Seven tests pass.
- `repository-validation.log`: 101 evidence, independent-oracle and proof-bank
  tests pass. `provenance.log`: the repository provenance/governance gates pass.
- `runtime.json`: observed compiler/runtime identity, checked against the prior
  accepted compiler binary hash. This is a minimal-runtime execution, not a
  fresh complete Pixi install or new CI receipt.
- `source-sha256.json`: all canonical kernel sources and the independent oracle
  inputs at execution. Baseline is main after #298; four new implementation
  source snapshots are included as `*.txt` for exact reconstruction.

Replays (repository root):

```bash
(cd kernel && pixi run --locked mojo run -I . class_a_run_index.mojo 24)
(cd kernel && pixi run --locked mojo run -I . tests/test_class_a_run_index.mojo)
python oracles/python/class_a_run_index.py evidence/class-a-run-index-2026-10-21/graph-n18.log
python -m pytest tests/test_class_a_run_index.py
sha256sum -c evidence/class-a-run-index-2026-10-21/SHA256SUMS
```

For the local minimal runtime, set MODULAR_MAX_PACKAGE_ROOT and
MODULAR_MOJO_MAX_PACKAGE_ROOT to its root and MODULAR_MOJO_MAX_IMPORT_PATH to
root/lib/mojo, then use root/bin/mojo. No unpinned runtime result is substituted
for the reported version.

The proof establishes n/10 < L(A_n) <= n+2 on an explicit reachable recurrent
family for all n>=4; it excludes a parameter-independent constant depth bound.
It does not establish all-state coverage for arbitrary n, all-class-A/C BH,
or universal #139. Human review remains pending. Class-D acceptance is not
changed or recertified by this packet.
