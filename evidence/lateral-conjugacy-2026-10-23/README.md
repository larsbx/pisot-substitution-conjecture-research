# Lateral move 1: conjugacy census of Theorem E's classes (2026-10-23)

This packet holds the unedited stdout/stderr and exit code (0) of one local run:
`cd kernel && pixi run mojo run -I . lateral_conjugacy_census.mojo 30`.
`runtime.txt` gives the Mojo version and the base commit; the sources of the run
are `kernel/psc/conjugacy_orbit.mojo` and `kernel/lateral_conjugacy_census.mojo`
as committed with this packet.

The census raises on any departure from the conjugacy-chain proposition of
`docs/lateral-generalization-strategy-2026-10-23.md` §2, so exit 0 means every
check passed on the box `p, q, r <= 30`. These are bounded counts. The proposition
itself is proved by hand for all parameters, and the spectral transfer rests on
the imported conjugacy invariance. This is local execution, not hosted CI and not
independent review.

## Graph cross-check (move 6 calibration)

`bh-qmax4.log` / `bh-qmax8.log` hold the unedited output of
`cd kernel && pixi run mojo run -I . lateral_conjugacy_census.mojo bh 4` (and
`bh 8`); the `.exit` files hold their exit codes (0). Each run builds the complete
uncapped seed-overlap graph of every Theorem C member with `q <= QMAX` and of all
its conjugates, and raises on a vertex without an offset-zero descendant. The
catch-up counts are finite observations.
