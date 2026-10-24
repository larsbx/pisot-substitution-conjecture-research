# Class B top layer: step-1 label fit (2026-10-24)

## The runs

`labels-*.log` and `labels-*.exit` are the unedited output and exit codes (all 0)
of the following command, one run per file name, local, not hosted CI:

```sh
cd kernel && pixi run mojo run -I . class_b_top_layer_profile.mojo labels BRANCH D QMAX
```

Each run builds the complete canonical swap-seed graph of every PIP member on the
top-layer line of gap `g = D + 1` with `q <= QMAX`. It raises on a capped graph or
on a vertex without an offset-zero descendant. Each member's labels are encoded as
typed k-intervals `(top, bottom, u, v, k_lo, k_hi)`, where `u = 3k + c + y`,
`v = 3k - c` and `(k, c, y) -> (u, v, k)` is unimodular. For every residue class
of `q mod g`, the run reports the least floor from which all later members share
interval keys and every endpoint is affine in `q`.

## Negative control

`negative-control-raw-encoding-plus-d0-q26.tail.log` holds the last lines of the
same mode run on plus `g = 1`, `q <= 26`, before the basis change (commit
`6a36082`). That run grouped labels as class A does, by k-intervals at fixed
`(k + c + y, y)`. It found **no** affine floor. Only the tail of that run's
output was kept, because it was captured through `tail`.

## Scope

These are finite verdicts on the probed windows. They are not certificates.
