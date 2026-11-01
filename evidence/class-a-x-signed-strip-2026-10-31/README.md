# Signed unit-strip evidence

Parent #436 revision: d8f2a8d4eb3693f1663764f176713725e3536d4b.
The two earlier evidence packets are preserved unchanged.

The [written argument](../../docs/class-a-x-signed-strip-2026-10-31.md)
proves local productivity of P_p=(x,y,p,3p+1,-6p) and its genuine
reversal for k,t>=0 and K|p|<=n-1. Here K=k+1, n=k+t+3 and
D=floor((n-1)/K). A bounded negative pump reaches one of four typed
exits; the selected path has at most 4D+6 edges. This is not a uniform
carrier covering X descendants or a complete Pisot substitution proof.

* `native-signed-strip.log`: the canonical locked Mojo regression passes
  1,464 oriented paths / 46,462 indexed edges over 120 specimens.
  Each edge checks full Parikh coordinates, actual indexed child types
  and exact Perron strictness; terminal labels are typed full-zero
  coincidence. Both signs, true reversals, parameter faces, all four
  exits, overflow, path-budget and invalid-occurrence controls are covered.
* `probe.json`: independent literal-word/Fraction replay of both actual
  orientations gives the same totals, with 4,412 two-edge pump iterations
  and per-member lengths. Separately, the immutable 22-graph certificate
  is checked for the finite signed interval -D..D in Reach(X). The parent
  certificate digest is recorded. The 120 path replays are not 120 full
  completed graphs.
* `symbolic.json`: 28 directed edge schemas over Z[k,t,r], five exhaustive
  integer wall regimes with 31 nonnegative guard/budget certificates,
  five root/physical-shift identities, and the exact selected path bound.
  These are coefficientwise checks, not interpolation on tested members.
  Strict geometry is proved in the manuscript; no full Lean formalization
  is claimed (`lean-probe.log` records the pre-compilation tool failure).
* `python-tests.log`: combined old and new research regressions. The
  four new tests independently check receipts, all wall types and low
  parameter faces, genuine reversal ordinals, full-offset mutations,
  domain/cap refusal and false LAST/RUN correction.
* `python-initial-failure.log`: preserved first test failure, a mistaken
  expected wall name for (0,0,-1). The path was correct; the expected
  label was repaired from high to near.
* `evidence-integrity-tests.log` and `governance.log`: proof-bank,
  source-integrity and ledger checks plus the existing README consistency
  failure. The six unchanged governance findings are not represented as
  a pass. #437 addresses them separately; this PR does not duplicate it.
* `dependency-status.json`: inspected heads and acceptance states before
  publication. #428/#430/#431/#432/#433 remain open; their conditional
  identity is not promoted. Hosted exact-head CI is separate from local
  execution and remains pending at this inspection.
* `source-provenance.json`: hashes of the new sources and load-bearing
  parent kernels, oracle and completed graph certificate.

Replay from the repository root:

    python -m pip install pytest==8.4.2 sympy==1.14.0
    python -m pytest -q tests/test_class_a_x_signed_strip.py
    python oracles/python/class_a_x_signed_strip.py > /tmp/x-strip-probe.json
    cmp /tmp/x-strip-probe.json evidence/class-a-x-signed-strip-2026-10-31/probe.json
    python oracles/python/class_a_x_signed_strip_symbolic.py > /tmp/x-strip-symbolic.json
    cmp /tmp/x-strip-symbolic.json evidence/class-a-x-signed-strip-2026-10-31/symbolic.json
    cd kernel
    pixi run --locked mojo run -I . tests/test_class_a_x_signed_strip.mojo

Specimens: k=0..12,t=0..8 plus (0,20),(0,64),(32,0); every index
-D..D and both orientations. The rejected immediate fold at (0,8,-1)
would use y ordinal 19 although only 0..11 exist. The valid route pumps
six times and takes cap1. The cap at (0,2,-1) must land at H(2,1)
through real LAST x. These are guard calibrations, not obstructions to
productivity. Fixed caps and checked machine arithmetic refuse a verdict
when exhausted; neither supplies an unbounded theorem by itself.
