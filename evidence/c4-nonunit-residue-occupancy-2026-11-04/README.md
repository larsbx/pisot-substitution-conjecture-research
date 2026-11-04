# Non-unit residue occupancy: evidence and review scope

This packet accompanies the [finite residue proof](../../docs/c4-nonunit-residue-occupancy-2026-11-04.md)
and [compact M-adic bridge](../../docs/c4-nonunit-madic-counting-bridge-2026-11-04.md).
The canonical finite implementation is Mojo; the independent oracle uses
Python `Fraction` Gaussian inversion. Analytic statements rest on the
written proofs, not on these executable receipts.

## Baseline and provenance

Initial inspection used main `9c6cd170d02e93049592cf01811a63a870097460` and
PR #493 at `d9f8f0a69d6ae0b311578b255a53f2403d428eee`. During development,
main advanced through merged #493 to
`ea9807688164f819534f74bc1682c415e6601508`; that revision was incorporated
before final validation. The historical scratch occupancy program was not
available or used. The six depth-two rows and the upper-bound proof were
derived independently from the literal substitution.

The local compiler is Mojo `1.1.0.dev2026090805 (34562fa1)`, matching the
repository's pinned compiler build. Local replay uses an existing minimal
installation with its `MODULAR_HOME` configured; this is distinct from a
fresh hosted `pixi run --locked` environment. Compiler crash-reporting
warnings are preserved in logs and are not test failures when the recorded
process exit is zero.

## Local validation result

Every final check below exited zero. The JSON receipt beside each log records
the exact command, environment overrides, start time and process exit.

| Check | Result | Receipt |
| --- | --- | --- |
| New canonical Mojo regression | Passed; contract receipt reached | `native-regression.receipt.json` |
| Deterministic native driver | Passed; all six depths, 144 nonzero rows | `native-driver.receipt.json` |
| Independent native/oracle comparison | All 11 tests passed, no skips | `oracle-native-parity.receipt.json` |
| Related Python regressions | All 22 tests passed, no skips | `related-python-regressions.receipt.json` |
| Existing cut-pair native regression | Passed on the refreshed source | `cut-pair-regression.receipt.json` |
| Existing pairwise-frequency native regression | Passed on the refreshed source | `cut-frequency-regression.receipt.json` |
| Generated proof inventory | 124 governed claims, 68 named Lean proofs, 355 source openings; synchronized | `proof-bank.receipt.json` |
| Claim governance | All six audits passed | `governance.receipt.json` |
| Markdown integrity | Passed | `markdown.receipt.json` |
| Vendored package synchronization | All pinned packages match | `vendored-sync.receipt.json` |

The native and oracle root brackets are independently chosen rational
brackets. The native certificate uses `2.26953 < beta < 2.26954`; the oracle
uses the wider `2.2695 < beta < 2.2696`. Both establish the same exact
polynomial identities and strict inequalities.

The first vendoring invocation incorrectly supplied a `check` subcommand
and exited 2 after printing usage. Its receipt is preserved as
`vendored-sync-cli-error.receipt.json`; the valid no-argument invocation
then passed. This was a command-usage correction, with no vendored edits.
The existing frequency test's unused-loop-variable warning is also
preserved; the new native sources emit no source warnings.

`validation-manifest.json` identifies the validated source commit and gives
SHA-256 digests for the source and evidence files. It distinguishes source
validation from subsequent evidence-only commits and hosted CI.

## Reproduction

From the repository root:

```bash
python tests/test_c4_nonunit_residue_occupancy_oracle.py
cd kernel
pixi run --locked mojo run -I . tests/test_c4_nonunit_residue_occupancy.mojo
pixi run --locked mojo run -I . c4_nonunit_residue_occupancy.mojo > /tmp/nonunit-occupancy.txt
cd ..
PSC_OCCUPANCY_NATIVE_OUTPUT=/tmp/nonunit-occupancy.txt python tests/test_c4_nonunit_residue_occupancy_oracle.py
python tools/make_proof_bank.py --check
PYTHONPATH=tools python -m claim_governance.cli --root .
python tools/check_markdown_source.py
```

Without `PSC_OCCUPANCY_NATIVE_OUTPUT`, the direct native-table comparison
is explicitly skipped; the other ten oracle tests still run. With the
driver output supplied, every native nonzero row at each of depths 1
through 6 is compared with the independent rational-inverse reconstruction.
Duplicate/missing rows and missing depths fail. The focused GitHub workflow
supplies this output.

## Automated mathematical review

The first separate skeptical review independently reconstructed the full
depth-two table and all three literal strong-coincidence witnesses. It
found no proof-blocking defect in the finite-index occupancy argument or
the compact completion's lattice, measure-scaling, positive-volume,
set-equation and strict-cut arguments at their stated scope. It explicitly
checked the use of a fixed point of a power, arbitrary fixed residue depth,
regular outer covers and the distinction between lifted and Euclidean
null intersections.

A follow-up pass checked the finite-cylinder approximation, its intersection
limit, the exact slice formula and the proposed upper-certificate inequality.
It found no proof defect. Its two clarity suggestions were applied: the
certificate uses a positive multiple of the fixed-point period, and its
Euclidean outer sets are explicitly bounded and measurable.

The second separate mathematical review accepted both notes and Corollary
M3 after identifying a missing explicit hypothesis: the one-pair
coincidence consequence concerns **distinct** letters. That hypothesis is
now stated before the implication. The review separately checked finite
residue counting, the compact group and lattice, fixed-point set equations,
strict-cut bounds, finite-cylinder approximation and source compatibility.

A separate native-code review accepted the supported constructor/driver
path, checked complete occurrence enumeration, quotient keys, integer
bounds, cap ordering, exact interval decisions and literal witnesses. Its
recommended six-depth requirement was added to the independent replay
parser. The final native certificate additionally authenticates every row,
word, matrix and adjugate against a canonical reconstruction, and its
regression rejects a forged row that preserves aggregate conservation.
The aggregate `verify_conservation` helper is not represented as a general
authenticator for arbitrary serialized tables.

This is an automated review, **not independent human review**. It does not
prove that a no-witness cut pair has small overlap, identify the volume
constant with an integer covering degree, or promote general C4/PSC.

The exact source revision, file digests and process receipts in this packet
make finite replay separately inspectable. Hosted workflow results must be
read at the PR's actual head; local receipts are not labelled hosted passes.
