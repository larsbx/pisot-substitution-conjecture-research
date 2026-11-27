# Upper plus-Class-A literal-entry acceptance packet

**Local acceptance passed. These changes are unpublished.** The new Lean endpoint
proves central entry for every strict full-integral source in the stated upper
parameter chamber. It does not conclude central-source coincidence or universal BH.

The mathematical derivation, hypotheses, exact endpoint names, and remaining
obligations are in the [proof note](../../docs/class-a-plus-upper-literal-entry-2026-11-23.md).

## Exact source identity

| Item | Identity |
| --- | --- |
| Accepted base source | `1bdaa34c63e6de97a0f17998c4f06887a18f099c` |
| Main merge with identical base tree | `7bfcd8c15e845f148b3c0ee405ca839ae6039e2d` |
| Base tree | `225e933c2ca2d8aaa8be550c003e824ac93fa201` |
| Local proof commit | `d723cc4bd1860b4e9c42f80b3d1c03cd7cb292f5` |
| Local proof tree | `fac2e528d4c48b419a91356f923c01bdba485cb8` |
| Source snapshot SHA-256 | `b9e4e176fe13f6a1d99894892a6f560bcd15a6e58e89032c8eda0ae1a6881cf9` |
| Lean release | `leanprover/lean4:v4.34.0-rc2` |
| Lean compiler commit | `6a10ac8c22beadecabdbb0919c2b50214762f91d` |
| Mathlib source commit | `4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09` |

`source-bindings.json` pins all **344** copied Lean source/configuration files.
Every binding was checked before and after the isolated build and then checked
against the local proof commit's Git blobs. The evidence follow-up changes
records only; the proof, audit, and gate inputs retain these bindings.

The gate reused the manifest-pinned upstream package build cache. It verified
all dependency checkout pins and tracked source bytes before and after the run.
It copied no project `.olean`, build directory, or Lake configuration cache.
The compiler and upstream compiled cache are explicit trust inputs; this is not
a rebuild of Mathlib from source.

## Mechanical acceptance

`tools/check_class_a_plus_upper_literal_entry.sh` exited **0**. It rebuilt all
**28 project modules** in the target import closure and ran **three audit
fixtures**. The total **2,281 Lake jobs** includes upstream dependency checks;
it is not a count of new proofs.

The combined independent audit checked all five new modules:

```text
PSC_UPPER_LITERAL_AUDIT_COMPLETE  5  208  168  12  39
```

The fields are module count, owned declarations, compiled theorem declarations,
independently restated endpoint contracts, and refusal controls. Compiler-generated
theorem declarations are included in the 168; the source proof-bank inventory
adds 86 named Lean proofs. Recursive axiom closure permits exactly `propext`,
`Classical.choice`, and `Quot.sound`. No additional axiom, `sorry`, or admitted
proof occurs in the audited closure.

The 12 independent contracts include the literal `n,d` words, exact length
formula, all integral coordinates, the least exponent and `k+1` path bound,
strict central target, and both recursive original `MarkTrace` witnesses.
The 39 refusals comprise missing, wrong-type, and extra-premise checks for each
contract, plus changed-bound, omitted-track, and closed-boundary contracts.
A refused weaker contract is an exact API mismatch, not an assertion that its
weaker proposition is false.

The second fixture checks four explicit control endpoints and prints ten
recursive axiom closures. The third replays the five existing arithmetic
entry axiom reports. `isolated-gate.log` retains the full output, including
inherited linter warnings from unchanged project dependencies. The five new
source modules and the combined audit are warning-free.

The focused proof-bank and recorded-data-integrity suite passed **265 tests**
with no failures, errors, or skips. Regenerated proof-bank consistency,
claim governance, and Markdown source integrity also passed. The claim registry
and ledger source are byte-for-byte unchanged from the accepted base.

## Fresh exact executable replay

| Check | Result |
| --- | --- |
| Canonical Mojo entry replay | 33,324 strict sources; 41,232 literal edges |
| Independent exact oracle | 33,684 sources; 47,412 edges; maximum depth 37 |
| Native/oracle comparison | All 33,324 native index and complete-target paths matched |
| Standalone original-prefix replay | All 33,684 records and 47,412 edges passed |
| Documented negative controls | All 96 passed |
| Complete target-coordinate mutations | All 72 rejected |
| Original-prefix coordinate mutations | All 6 rejected |
| Complete orientation reversal | All 33,684 records preserved counts and swapped complete tracks |
| Existing upper cycle/symbolic/central/independent regressions | 148 passed |

The exact sampled domain, limits, commands, tool versions, source hashes, and
nonblocking environment messages are in `replay-summary.json` and
`replay-summary.md`. The finite computations are separate from the universal
Lean theorem. The 22,748 sampled compositions to typed zero do not close the
remaining general central-source Lean assembly.

Both historical output hashes were reproduced exactly:

| Decompressed artifact | SHA-256 |
| --- | --- |
| `upper-entry-native.txt.gz` | `36ef371410b3817ddcde53403c25d972c4a9b4e035e7a7f3a93bb2d5e83d5acb` |
| `upper-entry.jsonl.gz` | `c1dccf0c6f7f1ae8fcc953733035d705741e14787f5cf56c9890a3617015688d` |

The complete stdout, stderr, and transcript are compressed without changing
their decompressed bytes. The original stderr ends in blank lines; retaining
it as `upper-entry-native.err.gz` preserves that exact output while keeping
the proposed text patch free of trailing-whitespace errors.
`SHA256SUMS` covers the compressed files themselves and
every other file in this packet.

## The two-edge control is now universal in Lean

For every allowed upper-family member, the strict source `y/c (0,1,0)` has no
empty or one-edge central path, and has the actual strict two-edge path

```text
y/c (0,1,0) --(n+2,0)--> c/c (0,1,-1) --(1,2)--> y/y (0,0,0).
```

The original prefixes satisfy
`P=(n+3,n+2,n+d+(n+1)^2)`, `Q=(0,1,1)`, and `M^2*(0,1,0)=P-Q`.
The wrong first top index `n+1` is proved incapable of selecting the claimed
`c` type, for any supplied offset. In the finite replay, all 9,192 possible
one-edge children across the 24 tested members also fail to be central.

## Reproducible checks

From the repository root with the pinned Lean/Lake on PATH and the existing
manifest-pinned upstream dependencies available:

```sh
tools/check_class_a_plus_upper_literal_entry.sh
python3 tools/make_proof_bank.py --check
PYTHONPATH=tools python3 -m claim_governance.cli --root .
python3 tools/check_markdown_source.py
python3 -m pytest tests/test_proof_bank.py tests/test_recorded_data_integrity.py -q
git diff --check
```

To replay the preserved full transcript and extra mutation/reversal controls:

```sh
PSC_ENTRY_REPLAY=$(mktemp -d)
gzip -dc evidence/class-a-plus-upper-literal-entry-2026-11-23/upper-entry.jsonl.gz > "$PSC_ENTRY_REPLAY/entry.jsonl"
python3 oracles/python/class_a_plus_upper_entry_independent.py --replay-transcripts "$PSC_ENTRY_REPLAY/entry.jsonl"
python3 evidence/class-a-plus-upper-literal-entry-2026-11-23/verify-entry-extra-controls.py \
  --root . --transcript "$PSC_ENTRY_REPLAY/entry.jsonl" --output "$PSC_ENTRY_REPLAY/controls.json"
```

The main proof note also gives the fresh native/oracle generation commands.
There is no hosted acceptance for this unpublished patch. The dedicated family
spectral success and wider mixed results on #654 remain historical results of
that separate source revision.

## Remaining boundary

The entry obligation is mechanically discharged at this scope. The central
endpoint retains its possibly nonzero full vector. The next step is to build
the end-to-end central-source Lean coincidence theorem and concatenate its
literal occurrence transcript and both original tracks at exactly this endpoint.
Universal BH, residual A1′, general C4, and independently reviewed closure remain
separate. No claim-status entry has been promoted.
