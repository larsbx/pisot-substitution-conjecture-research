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

## Extended runs and the Barge check

The files named `*-q26`/`*-q30` extend lines to larger `q`, using the same driver
with the arguments in their names. `barge-d11-q40.log` holds the output of
`class_b_top_layer_profile.mojo barge 11 40`, which counts Barge power/rotation
witnesses (up to power 3) among PIP top-layer members; it found none.

The `*-q18` runs predate the addition of the `barge` mode. The profile code path
they exercised is unchanged. `plus-d2-q18` leaves residue 1 mod 3 unfitted;
`plus-d2-q30` fits it. Both are kept.

The archived logs end each `mod k:` line with a trailing space, which the driver
printed at the time. The driver no longer does; no number changed. The logs are
kept byte-identical.
