# Failed hosted full Lean gate at 6021f042

This packet preserves GitHub Actions run 43435276869, attempt 1, job
131918630728, at exact source 6021f042056d3cb0f9717d2488144339721c2071
(tree 3355716258114a4f5353b10233fa1fa79bb34bbd).

The run reported successful compilation of NamedForwardCarrierData1
(558 seconds) and NamedForwardCarrierData0 (986 seconds). It then failed
at NamedForwardCarrier.lean line 77 with "maximum recursion depth has been
reached", followed by build exit 1. The same consumer diagnostic was also
observed in the separate archived-payload run 43435276766; that run has its
own preserved evidence packet. Neither failure was reported as a timeout.

This packet contains the original 4,533-byte ZIP, its single audit log,
raw REST run/job/artifact metadata, the full decoded job log and provider
response, exact source consumer/workflow/gate blobs and commit identity,
plus the executed preservation review code and receipt.

The ZIP digest and byte size match raw provider metadata. Its log matches
the extracted bytes. Run, job and artifact metadata agree on source and run
identity. The artifact contains no compiled object or source hash inventory.
Reported module compilation does not establish completed whole-repository
acceptance or the missing compiled axiom audit. No termination acceptance
is claimed, and no local Lean compiler was invoked for this review.

SHA256SUMS covers the retained files other than itself; review.json records
the checks. The enclosing tar has sorted entries, zero timestamps and fixed
owner/mode fields. Earlier evidence is unchanged.
