# PR #583 late link failures and additive repair

On November 15, 2026, a fresh inspection of PR #583's producing head
`4aa257950d81c81506a9cdebe740e18e66a9eda2` found two late workflow
failures. The main merge `febe7535afd59cbe56d9ae0bbc541b1bb8b57995` has
the identical source tree. The preserved `ci-status.json` records the
provider's pull-request workflow and job responses; it does not claim a
separate successful push run on the merge commit.

## Producing failures

- [PSC research checks, Python job](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43728657348/job/132856019519):
  `test_relative_links_resolve` was the sole failing test; 2,242 tests
  passed, 13 skipped and 28 subtests passed. Every other job in that PSC
  run, including `lean-proofs`, succeeded.
- [Canonical polynomial verification job](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43728657364/job/132856019338):
  its repository-verification step reported the same Markdown-link failure
  after the native kernel checks. The final verification result was a
  failure, not an accepted run.

The failures are the same two unresolved targets:

| Imported document | Missing target |
| --- | --- |
| `docs/bh-class-a-entry-stop-go-2026-11-14.md`, line 126 | `class-a-zero-defect-escape-2026-11-14.md` |
| `docs/class-a-plus-upper-entry-target-2026-11-14.md`, line 10 | `class-a-plus-constant-entry-2026-11-14.md` |

The failure excerpts retain the exact producing timestamps and diagnostic
lines. Their raw bytes, including provider trailing whitespace, are stored
as `psc-python-failure.log.gz` and `polynomial-verification-failure.log.gz`;
`../raw-log-containers.json` binds the compressed containers to the original
uncompressed hashes in the historical receipt. These failures were
introduced by the narrow historical-source import. They
are distinct from the earlier installer refusal, whose retry succeeded.
The dedicated upper-cycle, full-library Lean and research-integration
workflows also succeeded; those results do not erase these two failures.

## Repair and verification

Two small landing documents now resolve the paths and link the original
proof documents at revision
`9f0138d213357b866e7ceef0dcbfab96a667526d`. They explicitly describe their
provenance-only purpose. They do not reproduce or promote the full
historical theorems.

The original imported-source manifest and all 11 imported files were
checked against their recorded digests and original Git objects and remain
byte-identical. Neither original failed workflow was rerun or relabeled by
this repair.

The exact focused regression passed:

```sh
python -m pytest -o addopts= -q \
  tests/test_markdown_links.py::test_relative_links_resolve
```

The repository test enumerates tracked Markdown with `git ls-files`.
Before staging, it can therefore miss new documents themselves. The repair
receipt additionally checks every relative link in both new landing pages
and the new recurrence gate using the same link parser; all five resolve.
`markdown-link-test.log` contains the actual test output, and
`repair-receipt.json` binds the source and evidence hashes.

This is a focused documentation regression receipt. It does not stand for
a new full Python, native or Lean run. New recurrence work requires its
own source-bound acceptance.
