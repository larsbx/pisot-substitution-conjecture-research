# Class B top layer: exploratory residue profile (2026-10-23)

These are the unedited logs and exit codes of
`cd kernel && pixi run mojo run -I . class_b_top_layer_profile.mojo BRANCH D QMAX`,
one run per file name (`BRANCH-dD-qQMAX`). They are local runs, not hosted CI.

Each run builds the complete canonical swap-seed graph for every PIP class-B member
on the top-layer line `p = 3q + 11 - d` (plus, `r = q + 1`) or `p = 3q - 1 - d`
(minus, `r = q - 1`), with `q <= QMAX`, outside Theorem C's region. It raises on a
capped graph or on any vertex without an offset-zero descendant; exit 0 means
neither occurred.

The affine-fit lines are finite verdicts on the probed window only. This is an
exploratory probe for the stop/go decision in
`docs/class-b-top-layer-stopgo-2026-10-23.md`, not a certificate.
