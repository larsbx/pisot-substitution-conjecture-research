# Nonterminal C4 verification checkpoint

**Verification remains pending. Current V4 process liveness and terminal outcome are unknown. This checkpoint does not record a full Lean gate pass. General C4 remains open.**

Candidate commit: 16dd825648d1a1bcdba9038e079463a9bebbaf3d  
Candidate tree: ae73f53be5b43879d92c8995597960909afef684  
Snapshot completed: 2026-11-13T03:59:39.320029+00:00

The candidate adds a named packet exclusion theorem and generated consumers for exactly two archived substitutions: fixture 0, [1, 021, 001], and fixture 1, [1, 012, 001]. Their original packet and graph identities are retained. This does not establish an exclusion theorem for every substitution or settle general C4.

## Recorded results

| Evidence | Observed result | Scope |
| --- | --- | --- |
| Native payload oracle | Both fixtures reconstructed; all 32 mutation controls rejected; process exit 0 | Native reconstruction only; no Lean acceptance |
| Seven source checks at this commit | All passed, including eight audit-protocol unit tests | Source, governance, pins, Markdown and manuscript checks |
| Static reviews v2/v3 | Source analyses and provenance retained | Source review only |
| Scheduler preflight | All 16 harmless controls passed, matching the scheduler source recorded at V4 launch | Process-control checks only |
| Focused development attempt | NamedPositiveOverlap timed out after 1200.369 seconds; compiler -15, controller 1; empty diagnostic log; no outputs | Incomplete development attempt |
| Full isolated V4 | 49 successful project-module entries and 0 build-error lines in the captured prefix; terminal receipt absent | Last-observed progress; current liveness and terminal outcome unknown |

The two live V4 logs were each opened once and read once to their initial file length. Their exact byte prefixes are archived as:

- artifacts/isolated-v4/full.log.prefix — 19888 bytes; SHA256 a204bc932767f89259e7574af4849ee7a0fe2b418aba95c6091773c5b47235e5
- artifacts/isolated-v4/scheduler.jsonl.prefix — 49651 bytes; SHA256 5173cf93e55130b84facf98f835c3a1c92d1cd689fccff0f6736f5904056d6e3

These are sequential prefix snapshots, not terminal logs or one atomic snapshot. The JSON records each capture window and byte range. V4 start/process receipts are included. No terminal receipt was present before or after capture. Root subsequently reported that the tool returned 'Unknown process id' for session 78123 after compaction. Neither this tool-session observation nor an absent terminal receipt establishes whether the gate is alive or has exited. Current process liveness, the terminal outcome, and archived Lean replay acceptance are unknown. The exact unavailable-handle observation is retained at artifacts/evidence-preparation/v4-handle-unavailable.json; its file sizes and hashes match all four retained V4 captures.

## Preserved history and gaps

The initial isolated run exited 137 after cache provisioning. V2 was intentionally cancelled to repair the wrong-type fixture import; V3 was intentionally cancelled to restart the unchanged gate with the reviewed external scheduler. Their original logs, cancellation and cleanup records are retained without acceptance credit. The first isolated attempt and native development build lack prelaunch receipts; the cancelled wrappers lack normal terminal receipts. The native summary preserves its later source comparison without presenting it as a prelaunch record.

The focused 1,200-second timeout produced neither a successful compilation nor a source/type-error finding. Later focused modules were not started. Completed compiled audits of the new theorem, both generated exclusion consumers, and intended compiled negative-control rejection remain pending.

## Work shown

### Assumptions and hypotheses

The candidate API takes an original `ArchivedPayload.Packet`, its `Valid` proof, and an arbitrary finite word-pair carrier `C`. Validity must authenticate the literal fixture, complete positional rows, decoded closure, original roots and integer potential. The final statement is restricted to the packet's fixture in `Fin 2`, with no bound on the size of `C`. The source constructs normalized Haar measure internally; compilation of that construction and its consumers remains pending. See [docs/c4-named-strict-exclusion.md](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/16dd825648d1a1bcdba9038e079463a9bebbaf3d/docs/c4-named-strict-exclusion.md).

### Derivation / reduction

Strictness makes the represented cut-pair labels distinct. At zero displacement, the six ordered distinct-letter intersections are covered by the three archived roots 01, 02 and 12. The candidate places the carrier overlap inside their finite union, combines root nullity with positive carrier-overlap measure using the same product measure, and applies the existing null-cover contradiction. Compactness supplies the proposed normalized Haar construction. The standard argument and hypothesis boundaries are recorded in [docs/c4-named-strict-exclusion-literature-2026-11-12.md](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/16dd825648d1a1bcdba9038e079463a9bebbaf3d/docs/c4-named-strict-exclusion-literature-2026-11-12.md).

### Evidence and replay

The exact source-level commands recorded in the seven passing receipts, from the candidate repository root, are:

```sh
cd /workspace/scratch/5535bb23ca85/psc
python -m unittest discover -s tests -p test_archived_payload_lean_replay.py -v
python tools/make_proof_bank.py --check
python tools/make_ledger.py --check
PYTHONPATH=tools python -m claim_governance.cli --root .
python tools/vendoring/check_vendored_sync.py
python tools/check_markdown_source.py
python tools/check_manuscript_source.py
```

The unchanged full checker command recorded at V4 launch was:

```sh
cd /workspace/scratch/5535bb23ca85/psc
./tools/check_lean.sh --archived-packets /workspace/scratch/5535bb23ca85/c4-archived-export /workspace/scratch/5535bb23ca85/isolated-v4/replay
```

This is the historical V4 invocation, not an instruction to reuse its output directory. A new full replay requires fresh output/TMPDIR paths and its own start receipt. The recorded environment and executable hashes are in `artifacts/isolated-v4/start.json`. The command uses the already built, receipt-pinned exporter; its successful native build recorded `MODULAR_TELEMETRY_ENABLED=0`. No activation command is prescribed or run here.

Full aggregate compilation, the compiled proof-bank audit, exact types and transitive axioms for both generated `no_strict_system` consumers, and the intended compiled wrong-type rejection remain pending. Static review and protocol tests do not supply those results.

### Negative controls

Observed evidence includes all 32 native mutation refusals and eight passing audit-protocol unit tests. The new Lean control sources test why distinct labels and all three roots are needed, using a diagonal singleton and an omitted 12 root. A separate generated exclusion control has proposition `True`; its exact-type audit is required to reject it through the intended type mismatch. That compiled rejection and the Lean control compilation are not credited by this checkpoint.

### Non-claims / remaining gaps

This evidence-only checkpoint does not claim a full Lean pass or infer an exit from the unavailable V4 tool handle. The candidate covers the two authenticated substitutions and arbitrary finite carriers for those fixtures; it supplies no universal C4/PSC conclusion, global strict-packet coverage, or independent human review. The earlier failures, cancellations and focused timeout remain preserved. Verification is pending and general C4 remains open.

## Files and integrity

README.md explains scope. checkpoint.json contains results, identities, gaps, every retained artifact's byte size/SHA256, and the archive identity. pending-evidence.tar.gz contains this README, manifest.json, and the unchanged retained artifacts. The duplicate focused-v4 evidence copy was verified identical and retained once.

The archive uses sorted safe relative names, regular files, normalized tar metadata and gzip mtime 0. Compiled objects, executable binaries and caches are excluded. Source, git HEAD/index, source logs and scheduler source were not edited. No test or compiler job was launched for this checkpoint. Nothing was published; publication is intended for a separate checkpoint branch.
