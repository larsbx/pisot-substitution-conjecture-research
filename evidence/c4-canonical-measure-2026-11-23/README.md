# Literal-family canonical-measure review packet

This packet records local acceptance of the invariant-probability uniqueness
and explicit spectral-transport follow-up to PR #653. Publication requires
the requester's approval. Independent human review remains pending.

## Exact source identity

| Item | Revision |
| --- | --- |
| Starting PR head | `ce52d46bc4706fd2c15ddd3bb345f6e2067f49cd` |
| Local proof commit | `68e5ba028e863efedd4774ce4e07bd8678dc9143` |
| Local proof tree | `5e62ac3ef21a0a1fe7529dd0582f6765fcda7e2d` |
| Lean release | `leanprover/lean4:v4.34.0-rc2` |
| Lean compiler commit | `6a10ac8c22beadecabdbb0919c2b50214762f91d` |
| Mathlib source commit | `4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09` |

The isolated workspace was copied from source only. Before project
compilation, all 334 copied source/configuration files were compared byte
for byte against the clean local proof checkpoint. `source-snapshot.json`
records those digests and the two verification-script digests. The
subsequent review commit adds documentation and this evidence packet;
the recorded proof, audit, gate and dependency inputs are unchanged.

The compiler and the upstream Mathlib source-hash artifact cache are
explicit trust inputs. Dependency checkouts were fresh, at the unchanged
manifest pins, and checked before and after compilation and the audits.
No project `.olean` or pre-existing `.lake` configuration/cache artifacts
entered the isolated copy.

## Acceptance and scope

`tools/check_c4_parameter_family.sh` exited **0**. It built **87 project
modules** across the selected family import closure and passed **12 audit
fixtures**. Its 3,211 Lake jobs include external dependencies; they are not
a count of new theorems. This is the dedicated family gate, not the full
repository Lean gate.

The new canonical-measure audit checks three owned modules, **45 compiled
declarations**, **25 theorem constants**, **8 independent endpoint types**
and **22 controls**. Its recursive axiom allowance is exactly `propext`,
`Classical.choice` and `Quot.sound`. The unchanged original symbolic audit
still checks 198 declarations, 125 theorem constants, 7 endpoint types
and 3 controls.

The controls include 16 missing/wrong-type endpoint refusals, 3 altered
contract refusals and 3 proved measure counterexamples. In particular,
zero is invariant but is not a probability and differs from `wordMeasure`;
a point mass on an actual legal word is a probability but is not shift
invariant. Refusal of a contract without `k >= 2` preserves this proof's
parameter range and asserts no failure of unique ergodicity at `k = 1`.

The new equality quantifies over an arbitrary invariant Borel probability
on the actual two-sided legal shift. It is not an equality to a newly
defined alias. The spectral transport retains the original complex L2
closed eigenvector-span statement. The existing
`C4FamilySymbolicSpectrum.lean` source is unchanged from the starting head.

## Recorded files

- `acceptance.json`: source identity, complete built-module list, all 12
  completion receipts, dependency pins, scope and remaining obligations.
- `source-snapshot.json`: exact source and verification-input SHA-256 digests.
- `isolated-family-gate.log`: complete fresh gate output, including inherited
  warnings and all audit fixtures.
- `canonical-audit.log` and `symbolic-audit.log`: verbatim audit sections
  extracted from the full isolated log.
- `scoped-canonical-build.log`: the earlier successful scoped build.
- `metadata-checks.log`: proof-bank, claim-governance and Markdown checks.
- `focused-tests.log` and `focused-tests.xml`: the focused proof-bank and
  recorded-data-integrity regression results: **262 tests passed**. After
  adding these logs, recorded-data integrity is checked again against the
  finalized packet.
- `upstream-state.json`: read-only GitHub context, kept separate from local
  acceptance. The old family workflow passed and Physical Mass failed at
  the starting PR head; the PR was open but reported conflicted when checked.
- `SHA256SUMS`: exact coverage of all other files in this packet.

## Replay

From the repository root, with the pinned Elan toolchain available:

```sh
python3 tools/make_proof_bank.py --check
tools/check_c4_parameter_family.sh
PYTHONPATH=tools python3 -m claim_governance.cli --root .
python3 -m pytest tests/test_proof_bank.py tests/test_recorded_data_integrity.py
python3 tools/check_markdown_source.py
git diff --check
```

The narrower new-endpoint replay, from `proof/PscVerif`, is:

```sh
lake --no-cache build PscVerif.C4FamilyCanonicalSpectrum
lake --no-cache env lean -DautoImplicit=false -Dpp.unicode.fun=true \
  C4FamilyCanonicalMeasureAudit.lean
```

## Mathematical boundaries

The [proof note](../../docs/c4-family-canonical-measure-2026-11-23.md)
gives the derivation, primary sources and exact Lean signatures. The proof
uses dense-flow Haar uniqueness, Haar-conull singleton fibres and the
actual corrected constant-strip suspension. Extensionality of measures
through continuous tests is used on the metrizable solenoid.

A separate frequency-defined canonical measure and a general primitive-
substitution frequency/unique-ergodicity theorem are not constructed here.
Any independently supplied canonical probability on the same carrier is
identified once its probability and shift-invariance proofs are given.
Physical variable-roof disintegration remains a written statement. No
`k = 1`, arbitrary Pisot-substitution, universal PSC, BH, residual A1-prime
or general C4 promotion is asserted.
