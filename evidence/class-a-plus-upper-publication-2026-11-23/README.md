# Upper plus-Class-A publication record

This record accompanies publication of the locally completed literal entry and
all-source coincidence proof. The original check-time receipts remain in the
[entry packet](../class-a-plus-upper-literal-entry-2026-11-23/README.md) and the
[central completion packet](../class-a-plus-upper-central-completion-2026-11-23/README.md).
Their descriptions of local, unpublished work are historical observations.
Opening a PR does not convert them into hosted acceptance.

## Exact source correspondence

The publication snapshot is `d26b1e04f8dff02d6837ed887760d2550e889fb7`, directly
on main `7bfcd8c15e845f148b3c0ee405ca839ae6039e2d`. Its complete Git tree is
`00617042bb4341234faa0e35bdc4757630f1aba4`, exactly the tree of local review
head `d2ce5c805437d9b2263135f363a2bfbbe75e1a4b`.

The GitHub connector created the publication commit because the command-line
Git client had no write credentials. Only commit metadata and ancestry differ
between the publication snapshot and local review head; every file and mode
matches. This record adds provenance artifacts and a side-note without
changing any Lean source, audit, gate, canonical executable, or archived receipt.

## Recover the original four-commit history

`local-history.bundle` preserves the exact original entry proof, entry evidence,
central/all-source proof and final evidence commits. It requires the accepted
base `1bdaa34c63e6de97a0f17998c4f06887a18f099c`, already in current main history.
After cloning the published repository with that history available, run:

```sh
git bundle verify evidence/class-a-plus-upper-publication-2026-11-23/local-history.bundle
git fetch evidence/class-a-plus-upper-publication-2026-11-23/local-history.bundle refs/heads/local/upper-entry-20261123:refs/heads/review/upper-plus-local
git diff --exit-code d26b1e04f8dff02d6837ed887760d2550e889fb7 d2ce5c805437d9b2263135f363a2bfbbe75e1a4b --
```

The final diff must be empty. The recovered commits also permit exact
`git show` inspection of the proof revisions named by the evidence manifests.
Use the evidence READMEs for proof and native replay commands.

## Publication checks and scope

Before publication, both archive checksum sets (28 entry files and 59 central
files), all 344 original entry source bindings, all 349 final central source
bindings, and both gate/helper bindings were checked. Main and the accepted
baseline share tree `225e933c2ca2d8aaa8be550c003e824ac93fa201`; a clean
merge-tree calculation with the local result produces the same tested tree.

These checks establish source identity and retained local evidence. Hosted
acceptance and independent human review must be reported separately. The
mathematical scope remains every strict integral typed source for the literal
upper plus-Class-A words with `n>=7,n+5<=d<=2n+11`. Universal BH, residual
A1-prime, general C4 and universal PSC retain their existing status.
