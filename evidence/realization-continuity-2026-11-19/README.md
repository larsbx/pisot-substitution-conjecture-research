# Concrete realization continuity: fresh scoped acceptance

Base: `c8d582ff502b18745f7b0a73037458c92e705ad9` (merge of PR #625).
Verified local source checkpoint: `5697ae4ef9757e5f02be32387975853b3dca376a`.
Published source checkpoint: `4e5b0dd9ec474b42c3a58d779d5747e2b0c8544b`.
Both checkpoints have Git tree `05be35058b81bb62c7e2f2fa234dfcc78ee3c47d`.
The published checkpoint was fetched and its complete tree compared with the
local source checkpoint; the diff is empty.

Final documentation and evidence packaging preserve every checked Lean
source, pin and acceptance-support file. This packet records local scoped
acceptance. It does not assert a full root-library build or hosted acceptance.
Independent human review remains pending; agent source review does not
change that status.

## Accepted formal scope

The unchanged canonical gate rebuilt the entire local periodic-partner
import closure in a new temporary project. It cloned the pinned dependency
repositories and restored only selected upstream source-hash artifacts.
No local project objects were reused. Lean is 4.34.0-rc2, compiler commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`, with mathlib revision
`4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`.

The compiled audit checks **31 modules and 1536 declarations**,
including **1135 theorem declarations and all 630 source-named proofs**.
Only `propext`, `Classical.choice` and `Quot.sound` are accepted. The seven new
modules add **53 named proofs**; definitions and generated helpers are
counted separately by the compiled audit.

All **243 source and pin bindings** match the canonical snapshot
`e55d0dd7d8deef9b15b60bf4ffebd82e48342638a32f922c2cf429fb198b3f20`.
The gate rechecks the sources and exact dependency pins after cloning,
upstream cache restoration, compilation and the compiled audit. Binding all
project sources does not mean all bound modules were built: the accepted
compilation scope is the 31-module periodic-partner import closure.

## Records

| Record | Meaning |
| --- | --- |
| `periodic-partner-gate.log.gz` | Lossless combined stdout/stderr from the completed canonical gate. Empty audit fields and original line endings are preserved. |
| `gate-summary.log` | Selected terminal receipts extracted from that log without changing their text. |
| `receipt.json` | Exact revisions, scope, audit counts, pins, accepted axioms, regression counts and review boundary. |
| `source-bindings.json` | Canonical JSON reconstructed from the logged source bindings; its SHA-256 equals the gate snapshot digest. |
| `support-bindings.json` | SHA-256 of the unchanged canonical gate and proof-bank generator, checked against the verified source checkpoint. |
| `replay-command.txt` | Replay command and the environment supplied to the recorded gate invocation. |
| `repository-checks.log.gz` | Lossless inventory, ledger, governance, Markdown-source and diff checks, bound to the source checkpoint named at the start of the log. |
| `repository-tests.log` | The final focused regression run, archived after it completed. |
| `repository-tests.xml` | Corresponding JUnit receipt with exact test counts and outcomes. |
| `SHA256SUMS` | Checksums of exactly the files in this packet, excluding the manifest itself. |

The source-checkpoint repository checks and final focused regression run
have separate receipts from the Lean gate. Final regression logs were added
after the run, and the complete packet manifest and Git tracking were then
checked again. The regression run does not claim to checksum its own
still-unwritten output. Subsequent replay outputs should stay outside this
packet.

## Mathematical result and boundary

`Psc.PeriodicPartnerRealizationContinuity.continuous_realizeLocal P hR hβ`
proves continuity of the actual solenoid-valued realization on the ordinary
legal hull. It keeps the existing finite nonempty alphabet, `LengthSubst`,
`PisotData`, bijective-inflation and strict-expansion hypotheses. It adds no
continuity, compactness or recognition-radius premise.

The proof supplies completeness of the exact hull, compact fixed-origin
fibres, finite possible parent origins and a closed-map argument deriving
exact desubstitution continuity. The uniform geometric series estimate then
proves exact-source realization continuity, and the previously proved
equivariant criterion gives the ordinary result. Inflation is also a
homeomorphism of the ordinary hull under the original bijectivity input.

The new generic control proves discontinuity of the ordinary origin-start
coordinate at a seam and on every inhabited hull. It does not separately
assert noncontinuity of the full real-vector lift. The latter lift's proved
continuity belongs to the exact presentation.

Recognizability itself, normalized BBK identification, surjectivity and
finite fibres remain separate. Global ordinary-hull compactness and
Hausdorffness are not proved in this increment. No BDS, witness-selection,
remaining rank-two, C4 or PSC obligation is promoted by this packet.

See the [implementation note](../../docs/c4-realization-continuity-2026-11-19.md)
and [pre-code source decision](../../docs/c4-realization-continuity-stop-go-2026-11-19.md)
for the full derivation, assumptions, controls and literature boundaries.

## Replay

From the repository root, with the pinned Lean/Lake executables and Python
test dependencies available:

```sh
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
python3 tools/make_ledger.py --check
PYTHONPATH=tools python3 -m claim_governance.cli --root .
python3 tools/check_markdown_source.py
python3 -m pytest -q tests/test_markdown_links.py tests/test_check_markdown_source.py tests/test_proof_bank.py tests/test_recorded_data_integrity.py
sha256sum -c evidence/realization-continuity-2026-11-19/SHA256SUMS
```
