# Isolated-attempt history and supplemental diagnostic

These records preserve incomplete or failed isolated attempts and one
supplemental diagnostic. None supplies formal acceptance for this increment.

## Attempt 01: terminal outcome unknown

`attempt-01.tar.gz` stores all seven original interruption-packet files,
including their original manifest, checksum file and unmodified raw log.
The archive uses sorted filenames and fixed tar/gzip metadata. Actual
extraction was checked against every original filename and byte; the
original packet in scratch remains unchanged. Root reported `Unknown process id` for session 25398
at approximately 18:36 UTC on 2026-11-12, after the last recorded build
progress 9021/9023. The original receipt still says running, with no terminal
exit or complete compiled audit. The cause of session loss is not known.
This is neither a mathematical failure result nor an acceptance result.

`../gate/process-start-snapshot.json` and
`../gate/isolated-in-progress-snapshot.log` belong to attempt 01. They retain
their original bytes and must not be interpreted as later-attempt snapshots.

### Restore and check the original first-attempt packet

Run these commands from this evidence packet's top-level directory:

```bash
sha256sum --check SHA256SUMS
psc_attempt01_restore=$(mktemp -d)
tar -xzf history/attempt-01.tar.gz -C "$psc_attempt01_restore"
(cd "$psc_attempt01_restore" && sha256sum --check files.sha256)
```

The tar contains exactly seven regular files at its root, with their
original names. The extracted original `files.sha256` checks its six other
files; the outer `SHA256SUMS` pins the complete container, including that
checksum file itself. `integration-provenance.json` records all seven member
digests and the extraction comparison. The raw compiler warning whitespace
and both original integrity records are preserved exactly. The separate
start and partial snapshots in `../gate/` retain their original bytes.

## Supplemental aggregate import

`aggregate-diagnostic/` preserves the exact runner, result, process samples,
wrapper output and child output. In the retained first workspace the command
imported `PscVerif.lean` with `lake --no-cache env lean`, without `-o`. It
exited zero in 58.95742816599886 seconds without timeout. Child output is
empty; no aggregate `.olean` was created. The selected source/configuration
hashes stayed unchanged. Sampled peak process-group RSS was 5,464,904 KiB.
The result explicitly grants no formal acceptance credit. This import does
not satisfy the unchanged full isolated-checker contract.

## Attempt 02: terminal failure

`attempt-02/` copies the complete failed-attempt archive. The unchanged
checker exited 1 after 136.322 seconds because official dependency-cache
extraction ran out of disk space. The original terminal receipt confirms
unchanged HEAD, tree and recorded sources and binds the complete raw-log
SHA256. The archived gzip preserves all raw bytes. No completed compiled
audit was produced. No mathematical failure is inferred from this
provisioning failure; no formal acceptance is claimed.

No original attempt 02 start receipt was copied before terminal completion.
The actual start time is retained in the unmodified terminal receipt; no
start receipt was reconstructed.

Only a fresh unchanged checker invocation with a real zero terminal exit,
unchanged code/tree/source bytes and a successful matching compiled-audit
inspection can establish local acceptance. These retained histories cannot
replace any of those conditions. Their preservation launched no gate.

## Cleanup and fresh attempt 03

`cache-cleanup.json` records the root-owned deletion of only the abandoned
generated attempt01 source/build/cache directory after archive checksums
passed. Free bytes rose from 1,371,938,816 to 10,683,248,640. The repository
and archived logs/receipts were retained. The preservation task performed
no deletion.

Root began the fresh third unchanged checker at
2026-11-12T18:46:08.507683+00:00, reported as session 45485. Its genuine
running receipt was captured at 18:46:31.191315 UTC in
`../gate/attempt-03-process-start-snapshot.json`, with capture provenance
and the exact runner beside it. The start receipt binds the same code,
tree and source hashes. The runner emits separate 20-second heartbeats;
the child's raw log remains byte-for-byte in its own distinct file.
The real terminal receipt and matching inspector for this third attempt
are the only selected acceptance inputs.
