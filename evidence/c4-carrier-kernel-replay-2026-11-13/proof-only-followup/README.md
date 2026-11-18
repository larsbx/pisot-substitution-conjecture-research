# Explicit proof-only definitions: source-bound follow-up

This packet follows published commit
`8a385e8b58a5583a7f643a838efd530528f894f8`. It retains a successful native
replay of the modified candidate sources and the failed concrete Lean replay
of the preceding typed-chunk source. **It contains no complete concrete
carrier or termination acceptance.** Earlier packet files remain unchanged.

## Change and source binding

The canonical Mojo exporter now marks its generated closed data definitions
explicitly `noncomputable`, and the named `checkedStates` consumer carries
the same modifier. Removing those modifiers and the explanatory comment
reproduces the preceding generated Lean sources exactly. The original JSON
packets, words, rows, seeds, checking propositions and generic checker are
unchanged.

The pinned Lean compiler adds these definitions to the kernel environment
before its `shouldGenCodeFor` decision skips executable code generation.
They remain transparent to kernel reduction. An enclosing `noncomputable
section` alone does not have this effect. See the
[source rationale](../../../docs/c4-forward-carrier-kernel-encoding-2026-11-13.md).

| Candidate source or executable | SHA-256 |
| --- | --- |
| Fixture 0 Lean source | `019856bf4e01550382be9e2607d28a126b36da66c0533929c550e26a2c171d1a` |
| Fixture 1 Lean source | `4d1d3a9a1d16b04536ec12dba5e1e55a86b2a37d5dd27cc75a5d8b9661500844` |
| Forward exporter | `62a67c3ffa025911bf5d13fd58ce5547b46f74c27ce139bab5b23e3feed138b4` |
| Native test executable | `619c4db5563cf9d496bb09f98379077b31e48b00b511fb65c4c961712e2f914f` |

## Completed native gate

`native-replay.tar.gz` retains the complete output of the unchanged
`kernel/check_forward_carrier.sh` gate: generated sources and packets,
commands, logs, source and executable hashes, compiler metadata, refusal
results, independent oracle and terminal receipt.

The gate exited zero in **93.526 seconds**. Its focused suite passed
**186 tests**, including the required-modifier removal controls. Both
original JSON packets and both candidate Lean modules matched byte for
byte; both budget refusals produced empty stdout. Source hashes, executable
hashes and HEAD were stable across the run.

The recorded HEAD is the published parent `8a385e8`, with the candidate
source edits present. `SOURCES.sha256` identifies the actual tested bytes.
The worktree records also show proof-bank regeneration outside the gate's
source set. This is a source-bound local result, not a clean-head or hosted
acceptance result for a later commit.

The gate truthfully records `binaries_built_by_this_gate: false`.
`forward-export-noncomputable-source-bound.json` records a separate build
against the complete recorded source set, unchanged before and after; it
reproduced exactly the exporter digest used by the completed gate. The
unchanged test executable retains its earlier source-bound build receipt in
the parent packet. The installed compiler package metadata matches the
repository lock; the package archive was not rehashed by this gate.

| Native record | SHA-256 |
| --- | --- |
| Terminal replay receipt | `a69678f4d9472d689bea48ffab28b7e9b22481bbb579946c1cb52309d83a0281` |
| Internal checksum manifest | `33bb23274812b1c48d93437589e8e68853be4afbc720680cfb116518b7518de0` |
| Tested source manifest | `b30a05490c20a4bce1d6849a71bd81bdd0e239639f595635668cd44c9e1724c1` |

`governance-checks.tar.gz` retains the subsequent local validation logs and
receipt. The archived-endpoint protocol suite passed 12 tests, the
proof-bank suite passed 57, and recorded-evidence integrity passed 166.
Together with the 186 carrier tests, these are **421 passing focused
tests**. Generated proof-bank consistency, vendored pins, generated ledger,
Markdown integrity, claim governance and whitespace checks also passed.
The inventory remains 126 claims, 2,974 named Lean proofs and 411 source
openings. Inventory and protocol checks are not compiled proof acceptance.

## Failed preceding concrete replay

`first-typed-carrier1-failure.tar.gz` retains the preceding exact fixture-1
source, start and terminal records, complete log and sampled resource
history. Lean terminated with **return code -9 (SIGKILL)** after
**1,576.880 seconds**, with sampled peak RSS **4,353,761,280 bytes**.
The source was unchanged and no object file was produced. No Lean proof
error was reported. The cause of the signal is unconfirmed; this was not
an observed successful proof or a mathematical counterexample.

That run used cached development dependencies. Its start record did not
bind the compiler and dependency object digests, so the later diagnostic
runner records those additional identities. No missing historical field
has been reconstructed or added to the original receipt.

`additional-prefix-diagnostics.tar.gz` preserves the additional bounded
prefix probes, their available terminal records and their raw logs. Some
diagnostic histories have no terminal record. Unequal import times and
post-import budgets prevent a controlled comparative timing conclusion.
These probes do not supply full carrier acceptance.

`cancelled-development-build.tar.gz` separately retains the partial log of
the cached `NamedFiniteProductivity` dependency build and an observed
interruption record. The agent deliberately interrupted its session to
focus local resources on the concrete carrier replay. The session exited
130 without a target object; the compiler's own return code is unknown.
This is a cancellation, not a proof failure or a completed isolated gate.

## Remaining acceptance gates

Both concrete carrier modules, their named consumer, and both archived
payloads with all nine semantic endpoints still require successful terminal
Lean compilation and the isolated compiled axiom audit. The native checks
and source proof inventory cannot substitute for those gates. All 126
governed claim statuses remain unchanged.
