# Integration evidence, 2026-11-06

`preintegration-*` files are complete receipts from successful hosted run
42109144786 at `654c24561dae1172acc973c43f3db67322a17fb8`, not from the
integrated revision. The complete generic audit log is losslessly gzip-compressed.
The full generated source/module/audit/packet artifact is linked and SHA-256
pinned in `docs/c4-overlap-lean-integration-2026-11-06.md`; the full ZIP is not
committed a second time.

`inspection.json` describes the artifact and independent full-packet checks
performed against the integrated sources. It explicitly denies a fresh
integrated-revision Lean kernel replay. `focused-python-tests.log` is the
exit-zero focused 96-test run; pytest's quiet configuration suppresses its
summary. Test counts: proof-bank 57, packet replay protocol 5, cut-attractor 8,
H1 4, overlap class 22.

Local provisioning logs preserve the locked Mojo proxy failure and the initial
Lean executable-path lookup failure. The already archived host-proc-path
adapter restores Lean's version probe; it is a runtime trust input rather than
a compiler or proof modification. Standard hosted CI requires no adapter.

The integration introduces no new theorem/claim status and is not a merge
approval. Actual geometric recurrence, scaling and graph/set refinement remain
unformalized hypotheses, as the packet receipt's `geometry_formalized: false`
also records.
