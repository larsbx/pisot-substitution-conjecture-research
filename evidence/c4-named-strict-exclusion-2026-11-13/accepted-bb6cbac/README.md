# Accepted named strict-system exclusion at bb6cbac

The complete archived-payload workflow and its retained-artifact inspection
verified strict-system exclusion for **1/021/001** and **1/012/001**, uniformly
over every finite carrier. The checked source is commit
`bb6cbac16a620da4784f5b30d0a9a242618aef22`, tree `42472cf9f43d2e13bb999fd5c339abfea782d690`.
Later evidence and documentation commits preserve that accepted source.
General C4, G1 and PSC retain their existing statuses.

- [Successful full archived gate](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43365333027):
  run 43365333027, attempt 1, job 131688284776.
- [Successful full-library gate](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43365333049):
  run 43365333049, attempt 1, job 131688283732.
- [Actual inspection result](inspection.json): completed at
  `2026-11-13T06:45:19.026216+00:00`, with postprocessor exit 0.
- [Preservation receipt](receipt.json): complete archive and input identities.

## Work shown

### Assumptions and hypotheses

The generic consumer takes an original ArchivedPayload.Packet and its Valid
proof. Both actual generated fixtures discharge that validity obligation in
Lean. The final Packet.no_strictSystem conclusion quantifies over an arbitrary
finite word-pair carrier and has no caller-supplied Haar, positivity, root-cover
or carrier-size premise. Compactness supplies normalized additive Haar measure
internally on the original matrix-adic carrier.

The substitution is the literal fixture authenticated by the packet. This
result covers exactly the two substitutions above. It does not add an
arbitrary-substitution quantifier.

### Derivation / reduction

Strictness makes each represented cut pair distinct. Each of the six ordered
distinct-letter intersections is one of the three original zero-offset roots
01, 02 and 12; the three reversed cases use explicit intersection
commutativity. Therefore the actual carrier overlap is contained in their
finite union. The positive-overlap bridge and root-nullity certificate use
the identical stable-volume times original-carrier probability-Haar measure:

$$0 < \mu(O_C) \leq \mu(O_{01} \cup O_{02} \cup O_{12}) = 0.$$

The contradiction excludes the strict system. Existing projections give the
strict-component and BPA-strict-component corollaries. The finite graph
certificate proves the needed root nullity; the deduction applies uniformly
to finite carriers of every size.

[Composition and hypotheses](../../../docs/c4-named-strict-exclusion.md)
and the [pre-code literature decision](../../../docs/c4-named-strict-exclusion-literature-2026-11-12.md)
give the source-level derivation and prior-art boundary.

### Evidence and replay

The unchanged full verifier completed in the successful producing workflow.
The unchanged source-bound inspector subsequently checked the actual run/job
verdicts and critical steps, original archive identity, exact source hashes,
complete compiled axiom audit, both generated consumers and controls.

| Verified item | Actual result |
| --- | --- |
| Global compiled audit | 6,805 declarations; 4,996 theorem rows; all 2,798 named source proofs reached |
| New public declarations | Ten theorems and two definitions, all exact identities/kinds matched |
| New owners including generated helpers | Sixteen declarations, including four generated theorem helpers |
| Fixture 0: 1/021/001 | Seven semantic proof types; 1,800 audit declarations / 777 theorem declarations |
| Fixture 1: 1/012/001 | Seven semantic proof types; 1,800 audit declarations / 777 theorem declarations |
| Independent native mutation controls | All 32 rejected |
| Exclusion-only wrong-type control | Intended type mismatch verified; no unresolved-name credit |

The seven semantic proofs are `valid`, `accepted`, `typed_accepted`,
`domain_iff`, `roots_null`, `ancestors_null` and
`no_strict_system`. The last is checked at the exact unconditional type
for literal fixture 0 or 1. Every transitive axiom is in the permitted set
`propext`, `Classical.choice`, `Quot.sound`.

| Original fixture | States | Positional edges | Ordered lift positions | Rate |
| --- | ---: | ---: | ---: | --- |
| 1/021/001 | 7,150 | 34,826 | 69,652 | 99/20 |
| 1/012/001 | 7,083 | 34,853 | 69,706 | 101/20 |

Both original graph identities and complete addressed payloads were
independently reconstructed. The original radii are 16 and 8, and the maximum
rooted inverse depth is 13. The native and Lean-emitted 3,908,423-byte payloads
have identical SHA256
`447d58d811359235d1f4689433500494ae14724b89b5da91f429e7e7247beaca`.
The native oracle itself supplies no Lean acceptance; the successful full
Lean gate and its inspected transcripts supply that part of the result.

The original hosted artifact is **14016128149**, **19,234,309 bytes**, SHA256
`f70f8514a3e79b2f7ec7bee241e89a61a87a332677a1179a7d350945c5ff5e24`.
Both the official size and digest were verified before safe extraction.
Its 32 regular files total 80,590,878 extracted bytes. The complete original
ZIP is retained unchanged inside `acceptance-evidence.tar.gz`, so all
32 files can be reconstructed without duplicating their extracted bytes in
this outer archive. The repository stores this archive as two contiguous
parts, `acceptance-evidence.tar.gz.part-01` and
`acceptance-evidence.tar.gz.part-02`. Concatenating them in that order
reproduces the independently reviewed **19,138,093-byte** archive, SHA256
`555ba1397cce8ac661ced0410243428219ccf2423c57b56f3d67819721a13f55`.
The receipt records each part's size, offset and digest. The split changes
no archive member or proof evidence. The inspector's complete file manifest
is retained too.
The inspection reads transcripts and hashes and launches no Lean or test
process; full replay uses the pinned source workflow.

The archive also retains the inspector and guidance, raw REST verdicts and
artifact metadata, download/extraction receipts, all actual inspection
outputs, the seven earlier source-check receipts, v5 source metadata,
restored bare-library and integration evidence, and the three fresh
post-outage integrity checks. Those latter checks passed at clean commit
`8c8abde7d64f9eadebb139910d6591ae87230b7e`, tree `3d6e3234d5b2d2b854d67f0f270dc783f7e21f2a`;
their exact commands, timings and logs are preserved.

Run the following from the repository root, using fresh temporary
destinations:

~~~sh
sha256sum -c evidence/c4-named-strict-exclusion-2026-11-13/SHA256SUMS
mkdir -p /tmp/c4-named-exclusion-evidence
cat evidence/c4-named-strict-exclusion-2026-11-13/accepted-bb6cbac/acceptance-evidence.tar.gz.part-01 \
  evidence/c4-named-strict-exclusion-2026-11-13/accepted-bb6cbac/acceptance-evidence.tar.gz.part-02 \
  > /tmp/c4-named-exclusion-evidence/acceptance-evidence.tar.gz
printf '%s  %s\n' 555ba1397cce8ac661ced0410243428219ccf2423c57b56f3d67819721a13f55 \
  /tmp/c4-named-exclusion-evidence/acceptance-evidence.tar.gz | sha256sum -c -
tar -xzf /tmp/c4-named-exclusion-evidence/acceptance-evidence.tar.gz -C /tmp/c4-named-exclusion-evidence
python3 -m zipfile -e /tmp/c4-named-exclusion-evidence/inputs/primary/artifact-14016128149.zip /tmp/c4-named-exclusion-evidence/artifact
git worktree add --detach /tmp/c4-named-exclusion-source bb6cbac16a620da4784f5b30d0a9a242618aef22
python3 -B /tmp/c4-named-exclusion-evidence/tools/inspect-hosted-named-exclusion-audit.py \
  --root /tmp/c4-named-exclusion-source \
  --expected-commit bb6cbac16a620da4784f5b30d0a9a242618aef22 \
  --expected-tree 42472cf9f43d2e13bb999fd5c339abfea782d690 \
  --expected-run-id 43365333027 \
  --metadata /tmp/c4-named-exclusion-evidence/inputs/static-review-v5/source-metadata.json \
  --artifact-root /tmp/c4-named-exclusion-evidence/artifact \
  --run-metadata /tmp/c4-named-exclusion-evidence/inputs/primary/run.json \
  --jobs-metadata /tmp/c4-named-exclusion-evidence/inputs/primary/jobs.json \
  --output /tmp/c4-named-exclusion-evidence/reinspection
~~~

For a fresh mathematical replay, provision the repository's pinned Lean,
Mathlib and Mojo versions and use the original workflow or the composition
document's full `tools/check_lean.sh --archived-packets` recipe.

### Negative controls

The compiled singleton/Dirac examples show why distinct labels and all three
roots are necessary for the covering argument. The independent audit's
exclusion-only wrong-type fixture must fail for the intended type mismatch.
Its explicit StrictSystem import prevents an unknown identifier from being
mistaken for that rejection. The live seven-proof protocol also refuses
legacy six-proof transcripts while retaining historical receipts at their
original scopes.

The 32 native mutations cover substitution identity, missing or altered
states/weights/addresses, repeated positional edges, orientation and graph
direction, incomplete inverse ancestry, incorrect bounds and hidden payload.
Their actual refusals are retained in the original artifact.

### Non-claims / remaining gaps

This is mechanical certification at the two-fixture, arbitrary-finite-carrier
scope. General C4, G1, pure discrete spectrum and PSC are not concluded.
All 126 governed claim statuses remain unchanged, and independent human
review remains separate validation debt.

The previous failed and nonterminal proof attempts keep their original
outcomes in the sibling evidence directories. In particular, both hosted
runs at 16dd825 failed on the reversed-intersection conjunction, and the old
local V4 terminal outcome remains unknown. The two broader workflows at
bb6cbac failed on the missing packet-root checksum index; the separate
evidence repair does not rewrite those verdicts.

A workspace outage removed scratch files after the successful bare-library
inspection. The source, inspector, metadata and seven source checks were
restored from committed byte-pinned checkpoints. The original bare raw
captures and ZIP were recovered exactly. The old local bare inspection
report/script and the first local integrity-check receipts were not
recoverable as exact bytes; their historical identities are labelled in
loss notes, and new integrity checks have separate actual receipts.
The complete primary archived inspection here was executed after restoration.
The prepared GitHub fallback inspection workflow at ec3e0db3 was never
launched; its reviewed source is retained only as unused preparation.
