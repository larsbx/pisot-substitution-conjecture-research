# (NM_V) census — local acceptance, 18 November 2026

Base: `main@4f8b358`, the merge of #609. The
[unique-partner note](../../docs/c4-unique-partner-exclusion-2026-11-18.md),
section *Scope on the corpus*, carries the contract and the non-claims.
Runtime: Mojo from `kernel/pixi.lock`. Hosted CI has not run.

| Command | Exit | Log |
| --- | --- | --- |
| `(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_zero_fibre_asymptotes.mojo)` | 0 | [zero-fibre-asymptotes.log](zero-fibre-asymptotes.log) |
| `(cd kernel && pixi run --locked mojo run -I . nmv_census.mojo)` | 0 | [nmv-census.log](nmv-census.log) |
| `python3 -m pytest -q tests/test_nmv_literal_rays_oracle.py` | 0 | the independent oracle confirms all 96 failing pairs of the census log |

Source digests (sha256):

| File | Digest |
| --- | --- |
| `kernel/psc/zero_fibre_asymptotes.mojo` | `e8781f84d57ea9b84d25ab60b96a5feeecd1b738b4158795a41fdbb572a14fe4` |
| `kernel/nmv_census.mojo` | `ac90661a542040e6e1de197fb39e36ad3da14679617ad8cab9c7756a910a04cf` |
| `kernel/tests/test_zero_fibre_asymptotes.mojo` | `c919e6e4c2366973b0932b6cf0e167077346797874009ee8688ac454d06cb441` |
| `oracles/python/nmv_literal_rays.py` | `dababf2b089563e07ba9a141b8981ff88d7b7bd3da0087fe6edf93b1e58060ab` |
| `tests/test_nmv_literal_rays_oracle.py` | `684ad9fbee621494fcdddce3036f7b234b338f2a1c63d3ef5c1b808877d075ad` |
