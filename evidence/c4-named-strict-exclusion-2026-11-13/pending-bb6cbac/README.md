# Repaired named-exclusion candidate: verification ready, acceptance pending

This is a **nonterminal evidence checkpoint** for commit `bb6cbac16a620da4784f5b30d0a9a242618aef22`, tree `42472cf9f43d2e13bb999fd5c339abfea782d690`. The seven source/protocol checks passed at that exact clean source. Repaired Lean acceptance remains **pending**.

The current-status snapshot is explicitly dated **2026-11-13T04:44:16.519Z**. At that capture, [primary archived run 43365333027](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43365333027) was `queued`, with `conclusion: null`. Job `131688284776` was also `queued`, with `runner_id: 0`, no steps and no conclusion. The raw run and jobs responses are retained byte for byte with GET URLs and separate capture start/end timestamps. These records describe the capture time only; they are not a terminal verdict or a guarantee of later status. The job's raw `started_at` field does not establish execution while its status is queued and its runner and steps are absent.

`pending-verification.tar.gz` contains 26 preserved input files, this README and `manifest.json`. `checkpoint.json` binds the archive, README, embedded manifest and every retained input by size and SHA256. All archive members are safe relative regular files; timestamps, ownership and modes are normalized, and gzip uses `mtime=0`. No compiler outputs, executables or caches are included. The retained Python files are source code.

## Work shown

### Assumptions and hypotheses

The candidate theorem takes an authenticated `ArchivedPayload.Packet`, its `Valid` proof and any finite word-pair carrier `C`. `Valid` binds the literal fixture, complete positional rows, exhaustive decoded closure, original roots and integer potential. The final `Packet.no_strictSystem` interface constructs normalized Haar measure internally and has no caller-supplied Haar, root-coverage, positivity or carrier-size premise. Its substitution scope is exactly `1/021/001` and `1/012/001`.

These are descriptions of the candidate statement and source construction. The exact theorem inventory and source hashes are retained in `artifacts/static-review-v5/source-metadata.json`; this checkpoint does not claim that the repaired statements have completed the compiled acceptance gate. See the [candidate derivation](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/bb6cbac16a620da4784f5b30d0a9a242618aef22/docs/c4-named-strict-exclusion.md) and [pre-code source decision](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/bb6cbac16a620da4784f5b30d0a9a242618aef22/docs/c4-named-strict-exclusion-literature-2026-11-12.md).

### Derivation / reduction

Distinct-letter cut pairs reduce all six ordered letter intersections to the three original zero-offset roots `01`, `02` and `12`. A strict carrier overlap lies inside their finite union. The positive-overlap bridge and archived root-nullity theorem use the same product measure `(volume : Measure Stable).prod nu`, so finite-union nullity contradicts carrier positivity. Compactness provides the normalized Haar measure used internally.

The earlier hosted source failed in a reversed conjunction. The repaired source supplies explicit typed commutativity proofs in the three reversed cases; it preserves the theorem statement, archive roots, measure and fixture scope. The metadata records that the earlier static review missed this real error. The repair author reviewed the narrow source change; no new independent proof review or human review is claimed.

### Evidence and replay

All seven checks below ran once at this exact clean commit/tree. Each receipt preserves its command, working directory, environment, start/end time, exit status and raw-log hash. The source remained clean and unchanged before and after each command. The retained environment records Python 3.12.14 and `pypdf` 6.21.4. These are source/governance and protocol results, with no Lean compilation in this group.

| Check | Exit | Elapsed seconds |
|---|---:|---:|
| audit-protocol | 0 | 0.114251 |
| proof-bank | 0 | 2.072701 |
| ledger | 0 | 0.164442 |
| claim-governance | 0 | 7.736690 |
| vendored-pins | 0 | 0.064130 |
| markdown-source | 0 | 0.214496 |
| manuscript-source | 0 | 0.916007 |

The protocol suite reports eight passing tests. The proof-bank source check reports 126 claims, 2,798 named Lean proofs and 411 source openings; this is inventory freshness, not a compiled proof-bank audit. The ledger check reports 32 current generated surfaces; vendored pins report 13 matching packages; Markdown reports 521 checked files; manuscript source reports six required files and three `.tex`/`.pdf` files checked. Claim-governance subchecks all pass. Original stdout and receipts are retained without rewriting.

The exact source-level replay commands, from the repository root, are:

```sh
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
python -m unittest discover -s tests -p test_archived_payload_lean_replay.py -v
python tools/make_proof_bank.py --check
python tools/make_ledger.py --check
PYTHONPATH=tools python -m claim_governance.cli --root .
python tools/vendoring/check_vendored_sync.py
python tools/check_markdown_source.py
python tools/check_manuscript_source.py
```

The unchanged full checker recipe, after supplying the native exporter built from the exact candidate source and a fresh output directory, remains:

```sh
./tools/check_lean.sh --archived-packets /absolute/path/to/c4-archived-export /absolute/path/to/fresh-c4-named-exclusion-replay
```

That recipe is not executed by this checkpoint. No activation command is used here. Full acceptance still requires the actual successful hosted gate, the compiled global proof-bank audit, all twelve new explicit declarations (ten theorems and two definitions), both concrete seven-proof semantic consumers, permitted transitive axioms, archive/source binding and the intended compiled exclusion-only wrong-type rejection.

The retained refresh helper is SHA256 `18ea491b266dfaea74970fa31f5936ff738e3c2dda6149c7e0fc514e46318a4d`. It produced metadata for 26 source records and twelve exact declarations at this candidate. The helper received independent source review as tooling; that does not supply a new independent theorem review.

The retained hosted inspector is SHA256 `dcf15450b88c4048b551b199ad9a870848d4bc68acdbc811aad91a59f2a555b7`; its guidance is SHA256 `a08562efb523b2050939d17bde13daab050346e0f430a6cc0ecd1adf95fab5f5`. The inspector requires explicit expected commit/tree/run ID, matching static metadata, genuine completed/success GitHub run/job/critical-step verdicts and the complete bound artifact. It records actual hosted verdicts and never invents a local gate return code. It has not been run against a successful repaired artifact.

The inspector's final narrow compatibility repair was independently reviewed as source. The genuine old artifact's successful oracle step emitted exactly eight dots plus `[100%]`, without a textual `8 passed` summary. The parser now accepts that complete observed format only when the bound oracle step succeeded; it retains `reported_passed_count: null` and does not manufacture stdout. Normal exact eight-passed summaries remain supported, while skips, xfails, errors and incomplete/extra output are refused. The original inspector hash and observed transcript provenance remain in `artifacts/hosted-acceptance-inspector.md`.

The archive preserves the complete `source-checks-v5` and `static-review-v5` directories, both reviewed scripts, inspector guidance and fresh raw primary run/jobs capture. Tooling review and metadata integrity are preparation for the later compiled inspection, not theorem acceptance.

### Negative controls

The eight protocol tests passed at this candidate, including the protocol's required exclusion declaration and seven-proof transcript rules. Earlier native reconstruction on both original literal fixtures observed all 32 oracle mutation refusals; those original receipts and bytes are linked in the durable failed-head evidence below and were not rerun for this checkpoint.

The source includes two measure counterexamples showing why distinct letters and all three roots are required. The final compiled gate must also reject a `no_strict_system : True` control through the intended exact-type mismatch, with its explicit `StrictSystem` import. Compiled controls and the two generated exclusion proofs remain pending at the repaired source.

### Non-claims / remaining gaps

No repaired Lean theorem, concrete payload import, full compiled proof-bank audit or complete acceptance verdict is certified here. No inspector acceptance output or terminal repaired gate receipt exists in this checkpoint. The finite carrier size is unrestricted within the two named substitutions, but general C4, PSC, G1, pure discrete spectrum, all-`strictPackets` coverage and odd-ancestry closure remain unproved by this increment. Claim statuses are unchanged and independent human review is not claimed.

The [earlier nonterminal local checkpoint](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/bb6cbac16a620da4784f5b30d0a9a242618aef22/evidence/c4-named-strict-exclusion-2026-11-13/pending/README.md) retains failed/cancelled attempts, focused timeout history and the old scheduled run's log prefixes. That old run's execution handle became unavailable after 49 recorded module completions, without a terminal receipt; its outcome remains unknown. The [failed hosted checkpoint](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/bb6cbac16a620da4784f5b30d0a9a242618aef22/evidence/c4-named-strict-exclusion-2026-11-13/failed-head16dd/README.md) retains both actual failed hosted verdicts at `16dd825648d1a1bcdba9038e079463a9bebbaf3d`, their raw logs and digest-verified artifacts. Both failures exposed the reversed-conjunction error after `NamedPositiveOverlap` compiled; neither established full proof-bank or concrete Lean acceptance.

Those already durable bundles are referenced by fixed-commit links and their byte hashes in `checkpoint.json`; they are not duplicated in this smaller checkpoint. Preparing this evidence changed no repository source, HEAD, index, workflow or remote state and launched no tests or compilers.
