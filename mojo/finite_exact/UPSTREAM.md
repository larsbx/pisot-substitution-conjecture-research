# finite_exact upstream pin

Vendored from `larsbx/NLAP-JT` at commit `35e2e3049dfaa5d15ca3441585cc796fac477df1`.

Public boundary and stability promise: `docs/exact-arithmetic-public-boundary.md`
in that repository. Semantics: `docs/rational-interval-arithmetic-spec.md` there.

The only local edit is the package qualification of the intra-package import
lines (`from bigint_z import` becomes `from finite_exact.bigint_z import`,
likewise `rat_q`). `scripts/check_finite_exact_sync.py` reverses that rewrite
and checks the SHA-256 of each file against the upstream digest below. Any
other local change fails CI: fix upstream, then re-vendor and update this pin.

| Upstream file | Vendored file | SHA-256 of upstream bytes |
| --- | --- | --- |
| `src/bigint_z.mojo` | `mojo/finite_exact/bigint_z.mojo` | `d02a0c033042661161a24f0b31f1e89fbf3ed908ccc86e42b5b80b8df4240df1` |
| `src/rat_q.mojo` | `mojo/finite_exact/rat_q.mojo` | `543e88b3d86895b3a172d2a82b3c5825ac4183953298ecb891785d4c565b4bbe` |
| `src/interval_q.mojo` | `mojo/finite_exact/interval_q.mojo` | `b653c694794731a5d8459d35742aa279a89e914cef5bddcdcbf17c877587b284` |

Re-vendoring procedure:

1. Fetch the three files from the new upstream commit.
2. Apply the import rewrite: `sed -e 's/^from bigint_z import/from finite_exact.bigint_z import/' -e 's/^from rat_q import/from finite_exact.rat_q import/'`.
3. Replace the commit and digests in this file with the upstream values.
4. Run `python scripts/check_finite_exact_sync.py` and `pixi run test` in `mojo/`.
