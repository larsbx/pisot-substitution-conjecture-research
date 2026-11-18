# Failed hosted verification at head 16dd825

**Both hosted jobs failed. These records provide no full proof-bank audit or concrete Lean payload acceptance. General C4 remains open.**

Failed source commit: `16dd825648d1a1bcdba9038e079463a9bebbaf3d`  
Failed source tree: `ae73f53be5b43879d92c8995597960909afef684`  
Evidence recorded: 2026-11-13T04:22:06.361043+00:00

## Work shown

### Assumptions and hypotheses

This is failure evidence for the candidate named packet exclusion theorem. Its proposed consumer takes an original `ArchivedPayload.Packet`, a `Valid` proof authenticating its literal data, and an arbitrary finite word-pair carrier. Its intended scope is exactly the archived substitutions `1/021/001` and `1/012/001`. See the candidate's [scope and derivation](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/16dd825648d1a1bcdba9038e079463a9bebbaf3d/docs/c4-named-strict-exclusion.md) and [pre-code decision](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/16dd825648d1a1bcdba9038e079463a9bebbaf3d/docs/c4-named-strict-exclusion-literature-2026-11-12.md). No pending candidate proof is treated as compiled by this bundle.

### Derivation / reduction

Both hosted builds report the same unfinished reversed-letter intersection case at `NamedStrictExclusion.lean:42:14`:

```text
⊢ x ∈ K 1 ∧ x ∈ K 0 ↔ x ∈ K 0 ∧ x ∈ K 1
```

Lean also reports `and_comm` unused in that simplification. This is a concrete source-level compilation failure. The preceding `NamedPositiveOverlap` dependency compiled in both jobs, with linter warnings, in 6.3 seconds for the archived workflow and 5.7 seconds for the overlap workflow. That successful module build does not supply the complete proof-bank audit or validate the failed exclusion theorem.

### Evidence and replay

| Workflow | Run / job | Actual verdict | Failed step |
| --- | --- | --- | --- |
| [Original archived payload import](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43345576753) | 43345576753 / 131624030047 | completed / failure | Isolated full build and both concrete geometric imports |
| [Overlap Lean verification](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43345576693) | 43345576693 / 131624024712 | completed / failure | Compile from isolated sources and audit every local declaration |

The archived workflow's native construction and independent oracle steps both completed successfully before the Lean failure. The native receipt verifies both original fixtures and all 32 mutation refusals. Its literal packet is 3,908,423 bytes with SHA256 `447d58d811359235d1f4689433500494ae14724b89b5da91f429e7e7247beaca`. Fixture 0 has 7,150 states and 34,826 positional slots; fixture 1 has 7,083 states and 34,853 slots. Exact addressed-packet and historical-graph digests are preserved in the receipt and original ZIP.

The two original downloaded ZIPs are retained unchanged and independently match their GitHub-reported digests:

| ZIP | Bytes | SHA256 |
| --- | ---: | --- |
| archived-artifact.zip | 1,183,308 | `a3ba4c34e2246aa4a9f077205ec95b57b9f387694106bae2ed6c2ad3eea188b5` |
| overlap-artifact.zip | 4,526 | `c9ee81c9cd6c781526bbfed77e10368ec5bcb261326344d623d512a248bae93c` |

The archive retains raw run/job/artifact metadata, download receipts, full job-log JSON strings, available decoded logs, and the artifact audit logs. A derived UTF-8 archived-job log is explicitly labeled; its original JSON string remains unchanged. The 3.9 MB native packet is retained only inside the original ZIP. There are no temporary signed download URLs.

`receipt.json` binds each retained input's size and SHA256, every original ZIP member, actual GitHub step verdicts, and the package identity. `failure-evidence.tar.gz` contains this README, `manifest.json`, and the retained records. Its tar paths and metadata are normalized and gzip mtime is zero. No new test, Lean process, or source-check suite was run to prepare this evidence. Future acceptance requires a fresh complete replay at the repaired candidate with matching revision, compiled audit and both concrete payload receipts.

### Negative controls

The successful independent native oracle recorded 16 rejected mutations per fixture, 32 in total. The native test log separately records nine field refusals and eighteen semantic refusals. The retained oracle test log is the producer's exact eight-dot `[100%]` quiet transcript; its successful bound GitHub step supplies the process verdict. No textual passed-count summary is invented.

The global compiled audit and generated Lean replay were not reached. This bundle therefore credits no new compiled exclusion-only wrong-type rejection, generated seven-proof consumer audit, or axiom inventory.

### Non-claims / remaining gaps

Both final GitHub job verdicts are failures. The positive-overlap module build and successful native controls do not turn either failed gate into acceptance. This record does not validate the repair, establish the named exclusion theorem, supply global strict-packet coverage, or prove general C4/PSC. Independent human review is not claimed. The historical failed head remains explicitly separate from the repair worktree and any later successful run.
