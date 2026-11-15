# Original archived C4 payload: accepted code and durable evidence

Accepted code revision: 249a71b0330401ada5adbff7d9cd280bf0d7530f.
Accepted code tree: 97b54a6fdccb9a1828be815c2718fbcc5bc67960.

The [focused hosted run 43175356240](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43175356240) and
[job 131038172377](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43175356240/job/131038172377) completed successfully at that exact
checkout. The [provider artifact 13929993392](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43175356240/artifacts/13929993392)
was downloaded and completely inspected. Its 19,222,973 bytes have SHA256
e4e8ed4e5ed77385dbfce4a6b770c4b070fd4e1b2312ef2fa20102b4dfd317d1, matching the provider's digest.

This supplement records acceptance of the immutable code revision above.
A later evidence-only archival commit is a distinct revision. These receipts
do not claim that the later commit itself received a fresh hosted replay.
The archive commit must separately preserve the complete source closure, or
provide a complete tracked diff limited to approved evidence/documentation.

## Mathematical scope and hypotheses

The original two substitutions retain their original 16,8 enclosure:

| Substitution | States | Positional edges | Original contraction rate |
| --- | ---: | ---: | --- |
| 1/021/001 | 7150 | 34826 | 99/20 |
| 1/012/001 | 7083 | 34853 | 101/20 |

The concrete proofs bind literal parent/local occurrence addresses, track swaps,
matrix-adic residue and geometric exclusions, complete sigma-squared rooted
inverse ancestry restricted to nonempty overlap domains,
every positional multiplicity and the original positive potentials to the
named geometric consumer. Each generated source passes 1,799 declaration audits
and 776 theorem-declaration audits. The full bank reaches 6,537 declarations,
4,774 theorem declarations and all 2,633 inventoried named proofs. Allowed
transitive axioms remain propext, Classical.choice and Quot.sound.

The domain equivalence has the same nonempty-overlap guard on both sides:
membership in the ordered finite lift together with nonempty original overlap
is equivalent to sigma-squared rooted inverse ancestry together with nonempty
original overlap. The ancestor-nullity theorem covers every sigma-squared
ancestor, including geometrically empty ancestors omitted from the finite table.

The resulting scope is original named rooted inverse overlap domains and their
product-Haar nullity. Probability additive Haar assumptions remain explicit.
No identification with every noncomputable strict packet, positive strict-root
measure, obstruction-to-rooted-domain implication, C4 or general Pisot
Substitution Conjecture conclusion is supplied. Independent human review remains
separate validation debt.

## Retained bytes and inspection

[provenance.json](provenance.json) binds the exact code/run/job/artifact identities and outcomes.
[inspection/success.json](inspection/success.json) records the full source, type-auditor, axiom, original
and addressed graph digest, payload and control comparisons. It is artifact
inspection, not fresh local kernel execution.

[artifact-file-map.json](hosted-focus/artifact-file-map.json) maps all 30 original ZIP entries to their
retained bytes or an explicit compiled-object omission. Exact duplicate records
are stored once, commonly under local-complete-replay, with direct-byte-equality
aliases identifying each hosted original path. This includes both complete
generated Lean sources, both typed auditors and full audit/data logs, the exact
original payload, receipts and the real wrong-proof-type control.

The full hosted native, oracle, isolated source-build/axiom log and provider job
log are retained. The complete payload has 3,908,423 bytes and SHA256
447d58d811359235d1f4689433500494ae14724b89b5da91f429e7e7247beaca. The native and Lean streams and successful local stream agree
byte for byte. Native controls record nine field and eighteen semantic refusals;
the production oracle records sixteen refusals per fixture.

The three hosted compiled .olean files and three earlier local compiled objects
are omitted from this reduced archive. Their sizes/hashes and the original ZIP
inventory remain recorded. No archived compiled object was executed by inspection
or staging. Reproduction uses the complete source and pinned build workflow;
no binary reproducibility claim is made.

[archive-index.json](archive-index.json) binds every retained record's compressed and decompressed
bytes, hashes, original path and aliases. Large text uses gzip with mtime zero
and no stored filename. SHA256SUMS pins exactly every packet file except itself
using explicit ./ packet-relative paths.

## Preserved earlier evidence

local-complete-replay retains the completed local two-source proof execution
and its distinct timings. Its source manifest checks the eleven replay receipt
hashes and 1,619 tracked source inputs against the immutable Git tree, with all
6,230 tracked-tree identities retained.

hosted-generic-bank and hosted-python-tests preserve separate successful jobs on
synthetic merge d841d572d34a9ca10e4a88e3fbce33ed01a76b32, whose tree equals the
accepted candidate tree. They are not labelled exact candidate-commit checkouts.
The Python result is 2,110 passed, 12 skipped and 28 passing subtests; its raw
provider metadata and log are retained.

The original incomplete artifact inspection is retained. It assumed pytest
would print an explicit summary, but the pinned configuration and workflow each
pass -q and produce exactly the eight-dot 80-byte completion line. Both helper
versions and the narrow repair calibration are preserved. The successful format
check binds all eight static cases, the exact log bytes, pinned command/config
and the successful provider step; altered or incomplete forms refuse.

The historical pending template and pre-acceptance staging summary remain under
pending-hosted and history. They are preserved preparation snapshots, not the
current focused outcome. The prior repository development/failure packet is
unchanged.

## Replay

Use a clean checkout of the accepted code revision and the pinned tools. The
authoritative workflow source is
.github/workflows/c4-archived-payload-lean.yml at that revision. Its core replay is:

    ./tools/setup_lean.sh
    cd kernel
    pixi install --locked
    pixi run --locked mojo build -I . c4_archived_lean_export.mojo -o /tmp/c4-archived-lean-export
    cd ..
    PATH="$HOME/.elan/bin:$PATH" ./tools/check_lean.sh --archived-packets /tmp/c4-archived-lean-export /tmp/fresh-c4-archived-replay

The output directory must be fresh. The full workflow also runs the canonical
native controls and independent oracle controls before the isolated proof gate.
To reconstruct the original retained text layout, follow artifact-file-map.json
and the decompression records; compiled objects must be rebuilt.
