# Publication provenance for the cut-prefix embedding

This directory preserves the original local Git history and records its
mapping to the publication history. It is supplementary provenance for
[`../c4-cut-prefix-embedding-2026-11-12/`](../c4-cut-prefix-embedding-2026-11-12/).
The final provenance commit changes only this dedicated directory.

## Why the histories have different commit identifiers

The authenticated publication connector creates commits from a message,
source tree and parent identifiers. Its commit operation does not accept
the original author/time metadata. Recreating a commit through that
operation therefore changes its Git commit identifier even when every
source byte, file mode and tree identifier is preserved.

[`commit-map.json`](commit-map.json) records the original and recreated
identifiers, their parents, and the exact source tree at each step. The
three recreated commits were read back from GitHub, and every parent and
source tree identity was verified before marking the map complete. The original author/time metadata
and original commit objects remain intact in the attached Git bundle.

The inspected and tested implementation revision is
`73a0b6a95539beb1b6712afec0f8412571b41cd3`, with source tree
`8233701f593a8ba680356a88c2c6fc8e4cf01df5`. Existing evidence continues to
name that original revision. Mapping an identical source tree to a new
commit does not assert that GitHub Actions ran at the new commit, nor does
this later provenance-only commit acquire the earlier revision's hosted
status.

## Exact original history

The incremental bundle contains exactly these three new commits, in order:

| Purpose | Original commit | Source tree |
| --- | --- | --- |
| Pre-code literature and scope gate | `34999f2829412b24b43a82afdcf44370fc7d7f6c` | `6cbbd84c279bda1b861a6d681356c338a87006ad` |
| Implementation and verification interfaces | `73a0b6a95539beb1b6712afec0f8412571b41cd3` | `8233701f593a8ba680356a88c2c6fc8e4cf01df5` |
| Recorded local evidence and remaining obligations | `68aac93df3a02c7813486bde7c3f8741674ebe5b` | `cb0e5c406cc8d28971ebde200a7a30b7cbcf3c15` |

The prerequisite commit is
`9a1357ed5dae3b4502d29c34396d0e9403ccca75`, with tree
`fa8127d84df479c5e276b8578edd6a324bf175ab`. The bundle is incremental and
must be restored into a repository containing that exact base snapshot.

Bundle: [`cut-prefix-original-commits.bundle`](cut-prefix-original-commits.bundle)

- Size: **276,363 bytes**.
- SHA-256: `1cdf0ba7e154b2f2925f84c8bb91bef8f4cf1d253895b610b29783428acc74e8`.
- Advertised ref: `HEAD` at
  `68aac93df3a02c7813486bde7c3f8741674ebe5b`.

## Restore the exact original commits

Download the bundle as a binary file, retaining its exact bytes. Set
`PSC_BUNDLE` below to its absolute path. These commands create a new
repository and fetch only the exact existing base snapshot before importing
the three original commits.

```bash
PSC_BUNDLE=/absolute/path/cut-prefix-original-commits.bundle
sha256sum "$PSC_BUNDLE"
git init psc-cut-prefix-restore
git -C psc-cut-prefix-restore fetch --no-tags --depth=1 \
  https://github.com/larsbx/pisot-substitution-conjecture-research.git \
  9a1357ed5dae3b4502d29c34396d0e9403ccca75
git -C psc-cut-prefix-restore bundle verify "$PSC_BUNDLE"
git -C psc-cut-prefix-restore fetch --no-tags "$PSC_BUNDLE" \
  HEAD:refs/heads/c4-cut-prefix-original
git -C psc-cut-prefix-restore switch c4-cut-prefix-original
git -C psc-cut-prefix-restore rev-list --reverse \
  9a1357ed5dae3b4502d29c34396d0e9403ccca75..HEAD
git -C psc-cut-prefix-restore rev-parse HEAD HEAD^{tree}
git -C psc-cut-prefix-restore rev-parse \
  73a0b6a95539beb1b6712afec0f8412571b41cd3^{tree}
git -C psc-cut-prefix-restore fsck --no-reflogs --connectivity-only HEAD
```

The first command must print the SHA-256 above. The commit list must be the
three originals listed in the table. The final tip and tree must be
`68aac93df3a02c7813486bde7c3f8741674ebe5b` and
`cb0e5c406cc8d28971ebde200a7a30b7cbcf3c15`; the tested implementation tree
must be `8233701f593a8ba680356a88c2c6fc8e4cf01df5`.

For an offline restore, replace the GitHub URL in the base-fetch command
with an absolute path to a local clone containing the exact base snapshot.
Keep `--depth=1` if only the required base snapshot, rather than all earlier
history, is needed. The tested implementation can then be inspected directly
with `git -C psc-cut-prefix-restore switch --detach
73a0b6a95539beb1b6712afec0f8412571b41cd3`.

## What the recorded restoration verified

[`bundle-restore-verification.json`](bundle-restore-verification.json)
records a successful independent temporary-repository restore. The exact
base was fetched from the local clone at depth one. The bundle verified,
all three original commit objects matched the source objects byte for
byte, every original tree identifier matched, the restored commit range
contained exactly those three commits, and connectivity checking exited
successfully. Verification disabled lazy object fetching and restricted Git
to the local `file` protocol. No network operation was used for that check.

The preceding attempt to fetch the entire earlier local history failed
because the local object store lacked historical object
`3facfb31751aa8cb026cdfb3ccdf7504cf5737ed`. That failure is retained in the
verification record. The successful depth-one-base restoration proves that
the incremental bundle recovers these three commits over the required base
snapshot; it does not certify completeness of pre-existing repository
history or replace any mathematical, runtime, or hosted acceptance gate.
