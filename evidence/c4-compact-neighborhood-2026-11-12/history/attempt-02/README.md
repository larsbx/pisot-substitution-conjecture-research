# Failed isolated attempt 02

The unchanged checker ended with real exit code 1 after 136.322 seconds on
2026-11-12. Its terminal receipt reports unchanged HEAD, tree and recorded
source bytes. The official dependency-cache extraction reported repeated
`No space left on device` errors and ended with 8616 failed decompressions.
This attempt failed and supplies no local acceptance. No mathematical
failure is inferred from this provisioning failure.

`process-terminal.json` and `runner.py` preserve the exact original bytes.
`isolated-lean.log.gz` decompresses to the complete original raw log, whose
SHA256 and byte count are bound by the terminal receipt and observation.
No successful compiled audit was produced. No raw start-receipt snapshot
was captured before the process ended; the actual start time remains in
the unmodified terminal receipt. No start receipt has been reconstructed.

This preservation made no repository, HEAD or active-input changes and
launched no build, retry, test, CI request or remote operation.
