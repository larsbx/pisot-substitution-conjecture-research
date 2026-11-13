# Scoped archive-integrity review

This review checks the five hosted/diagnostic archives and prepared inspector
listed in its receipt. All inner manifests and nested ZIP copies match, and
all 4,181 historical tracked evidence files and modes match the recorded merge
commit. It does not execute packet code, Lean or a native gate. The source-check
archive and final parent inventory were packaged later and are outside this
review's scope.

The local fixture-0 failure archive originally lacked an internal manifest.
The packaging repair adds that manifest while preserving every one of its eight
original record bytes. Both versions, exact preservation hashes, and the repair
code remain in this review archive.

The initial text scan flagged three masked CI Authorization headers. A separate
classification confirmed that each contains only masking asterisks followed by
an escaped newline and timestamp. The initial needs-review receipt, logs and
script are retained alongside the final passing review; their bytes were not
rewritten. This pattern/URL scan is not a general proof about arbitrary binary
contents.

`review-records.tar.gz` contains the complete original review directory and its
unchanged `SHA256SUMS`, including the executed scripts, original and final
receipts, all historical evidence hashes and the original local-failure archive.
All 13 archive members are safe regular files, and their extracted bytes
were compared with their originals before publication. Check `SHA256SUMS` from
an empty directory after extraction.

Archive SHA-256: `7421e7eee631505576dc6e0e8f3816aed4d894c9be8c74f2a1bee944dfeb17dd`.

For the research result and remaining acceptance boundaries, read the parent
packet's [README](../README.md).
