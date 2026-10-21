# CI repair after the first class-D assembly publication

Head 2e7d88f had real failures, recorded with exact job links and excerpts in
ci-failures.json. The new receipt logs existed locally but were omitted by
the global *.log ignore rule. No archived receipt is regenerated or relabelled:
the original bytes are now published, including empty successful build logs.
Evidence logs/out files are explicitly exempted from that ignore rule.

The generic full Python job and the polynomial-kernel full verification job
used shallow checkout, but provenance requires immutable historical commits.
Both now fetch complete history. The existing scoped assembly job already
did. Missing history remains an error, not a skipped provenance test.

Five earlier minus packets lacked SHA256SUMS; their existing bytes are pinned
without changing results. The chamber-execution packet's nested checksum paths
used ambiguous bare subdirectories; an original manifest copy is preserved,
and ./ prefixes make those paths unambiguously packet-relative. Hash values
and actual archived evidence bytes remain unchanged.

Six old CI jobs still demanded successful whole-quadrant constant graphs or
fixed real carriers. Their exact undecided-sign failures are preserved, and
those candidate sources are left intact. The workflow now executes the full
native minus aggregate and full native plus chamber aggregate (including all
cores/strips/interfaces/prefixes), as well as plus b=0 and existing obstruction
controls. This replaces failed mechanisms with their completed successors;
no arbitrary exception is accepted as a passing proof. Independent support
calibration and all failure artifacts remain enabled. The separate chamber,
minus-carrier and scoped-assembly workflows remain active.

This is a CI/publication repair. It changes no mathematical engine, lock pin,
component receipt, theorem hypothesis or governed claim status. Combined
integration acceptance, universal #139 and general PSC remain open until the
required current-head validation actually passes.

Main advanced through #295 during this repair. Merge 824a2b9 preserves both
append-only side-note histories and its moment-interface source/evidence;
derived proof inventory is regenerated. The moment-interface native test
passes with the same locked compiler (`merged-moments.log`). On the reconciled
tree, the integrity/provenance/ledger subset passes 58 tests, with one optional
TLC mutation skip (`merged-regressions.log`). The actual 18-model replay from
the preceding assembly remains recorded separately; no new model was added.

A fresh Git clone of repair commit 264cdd9 verifies immutable receipt
provenance and all repository provenance/governance gates (`clean-*` files).
The complete Python suite was also launched in that clean clone; its result
is reported separately when completed. These focused receipts do not assert
that pending full-suite or remote current-head CI checks already passed.
Existing exact obstruction controls pass unchanged (`obstruction-controls.log`).
