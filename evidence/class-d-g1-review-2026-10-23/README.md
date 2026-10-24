# Class-D scoped G1 — independent verification replay, 2026-10-23

This packet records a **fresh local execution** made while independently
checking the derivation of `docs/class-d-g1-corollary-2026-10-22.md`. It is
not hosted CI, not independent human review, and it does not replace the
archived acceptance packet
[`class-d-integration-accepted-2026-10-21`](../class-d-integration-accepted-2026-10-21/),
which remains the canonical record of the accepted certificates. The earlier
[`class-d-g1-ledger-2026-10-22`](../class-d-g1-ledger-2026-10-22/) packet is
unchanged.

Executed tree: the merge of `main` (`c439081`, through PR #328) into PR #324;
`runtime.txt` pins the commit, tree, Mojo, pixi, JVM and the TLC jar digest
(identical to the earlier packet's pin).

## Files

Each `*.log` is the unedited combined stdout/stderr of one command; the
matching `*.exit` is its process exit code. All are zero.

| File | Command (from repository root) | Contract it exercises |
| --- | --- | --- |
| `native-test_class_d_boundary_template` | `cd kernel && pixi run mojo run -I . tests/test_class_d_boundary_template.mojo` | minus `b=0`: symbolic tail `a>=4` (145/781), exact prefix `a=0..3`, every half-depth `<=4`, refusal controls |
| `native-class_d_plus_boundary_certificate` | `cd kernel && pixi run mojo run -I . class_d_plus_boundary_certificate.mojo` | plus `b=0`: symbolic tail `a>=7` (718/4,326), exact prefix `a=0..6`, every half-depth `<=6` |
| `native-test_class_d_minus_certificate` | `cd kernel && pixi run mojo run -I . tests/test_class_d_minus_certificate.mojo` | independent minus spine for `a>=2`, affine occurrence rank descent |
| `tlc` | `TLA_TOOLS=… ./proof/tla/check.sh` | all 18 dependency models, expected outcomes |

The depth bounds used by the corollary (`K_-<=4`, `K_+<=6`) are asserted by
`certify_boundary` in `kernel/psc/class_d_boundary_template.mojo` on **both**
the symbolic tail and every exact finite-prefix vertex (a missing target,
depth `<0`, also raises). The printed plus prefix line ("all hitting") is a
summary of that asserted bound, not a weaker check.

## What was verified by derivation (no new mechanism)

- `L` is the maximal image length: `3a+8` (minus), `3a+5` (plus).
- `ell_max/ell_min <= beta^2`: a shortest path in a strongly connected
  three-vertex occurrence graph has at most two edges, and `b` in `sigma(a)`
  gives `ell_b <= beta ell_a`. Here `x` and `c` reach every letter in one
  step and `y` reaches `c` in one step (`y -> cc` at plus `a=0`).
- `beta <= L` by the maximal column sum.
- Proposition 4 at levels `n>=K` and seed inflation at levels `n<K` give
  `|u| <= 2L^(K+2)`; `H` is monotone in `K` since `L>=5`, so the depth
  upper bounds may be substituted: `2(3a+8)^6`, `2(3a+5)^8`.
- `sum_{m=1}^H 9^m = (9^(H+1)-9)/8`.
- Run-index guard: `k_bottom-k_top` ranges exactly over
  `[-(n_top-1), n_bottom-1]`, witnessed by `k_top=max(0,-m)`,
  `k_bottom=max(0,m)`; an empty run gives an empty interval, which the exact
  plus `a=0` graph handles.
- Parameter cover: prefixes end at `a=3` / `a=6` and tails start at
  `a=4` / `a=7`; no parameter is uncovered.

No counterexample or missing hypothesis was found. Non-claims are those of
the corollary: no universal G1, no equal-letter coincidence, productivity,
PDS or PSC, and no branch-wide constant for positive `b`.
