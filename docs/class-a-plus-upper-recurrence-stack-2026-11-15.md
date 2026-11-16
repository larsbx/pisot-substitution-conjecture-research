# Upper central recurrence: stack compatibility addendum

Inspection date: November 15, 2026. This records read-only source/path
comparison and a merge-tree conflict inventory, not an applied merge or
acceptance of the wider Class-A stack.
It supplements the historical
[eight-cycle compatibility note](class-a-plus-upper-stack-compatibility-2026-11-15.md).

## Exact revisions and unchanged imports

The current recurrence increment starts from main commit
`febe7535afd59cbe56d9ae0bbc541b1bb8b57995`, which merged PR #583. The compared
[#579 revision](https://github.com/larsbx/pisot-substitution-conjecture-research/commit/729bbc33e9306d170eaa0d93bcf269aca6aeeece)
is `729bbc33e9306d170eaa0d93bcf269aca6aeeece`; the recorded
[stack metadata](../evidence/class-a-plus-upper-recurrence-2026-11-15/stack-status.json)
identifies it as the open draft stack head containing the merges of
#580, #581 and #582. Their common ancestor with this main base is
`a19670c521927a8f6ac7e08f26cd3d563eafdce3`.

**This increment imports no additional source from that stack.** Both new
Lean modules import `PscVerif.ClassAPlusUpperCycles`, already on main.
The new recurrence module, cycle-completion module, their standalone
audits, the new canonical Mojo module and dedicated recurrence workflow
have no same-path files at the compared #579 revision. This observation
does not decide conflicts in the rest of the tree.

All 11 paths in the existing
[import provenance manifest](../evidence/class-a-plus-upper-cycles-2026-11-15/imported-source-provenance.json)
were rechecked against both their recorded SHA-256 digests and
`git show SOURCE_COMMIT:PATH`. They remain byte-identical to their original
sources. The manifest itself is unchanged from the main base, with SHA-256
`beb01a0ef92a0e31f53d81f342e84d0d7c8be1ac0a05d2d83d93729b0f29f2e6`.
Ten of these 11 files also match #579 exactly.

The sole imported-source difference remains
`proof/PscVerif/PscVerif/ClassAZeroDefectEscape.lean`:

| Selected source | SHA-256 |
| --- | --- |
| Current main import, original #581 revision `9f0138d213357b866e7ceef0dcbfab96a667526d` | `a50672744789443300b5c7c4b6c0467c941fec5b1d833d7544e62440c729fa58` |
| Compared #579, including the later #580 extension | `04c10c8f84a07b5712dd1e5f05f713478d511a526496f4c1cb082a14d86188a7` |

The later source factors out `run_slice_first_digit_step`, reuses it in
the two-step proof, and adds strict clipping and boundary-return lemmas.
This increment preserves the original source; its fresh proof receipts
are bound to that selection. Future integration must review the later
source explicitly and rerun the affected source-isolated audits after
any dependency change.

## Two document paths require reconciliation

The additive repair for PR #583's broken historical relative links
introduced two short provenance landing pages. The compared #579 tree
already contains full source documents at those exact paths. Both paths
are absent from the common ancestor and this increment's main base, and
the independently added contents differ:

| Path under `docs/` | Current landing page | Full document at #579 |
| --- | ---: | ---: |
| `class-a-plus-constant-entry-2026-11-14.md` | 978 bytes | 36,367 bytes |
| `class-a-zero-defect-escape-2026-11-14.md` | 952 bytes | 23,256 bytes |

The full stack documents are themselves byte-identical to the original
documents at `9f0138d213357b866e7ceef0dcbfab96a667526d`:

- [Plus constant-entry source](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/729bbc33e9306d170eaa0d93bcf269aca6aeeece/docs/class-a-plus-constant-entry-2026-11-14.md),
  SHA-256 `2bfde5c66d359db49d592f06b5a0848c898342ff37ddaeb62d6180ad5b7ff9fd`.
- [Zero-defect source](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/729bbc33e9306d170eaa0d93bcf269aca6aeeece/docs/class-a-zero-defect-escape-2026-11-14.md),
  SHA-256 `15c385e42b44514bf2788db60b0bebe877070d50c77284795e35480e32131cd8`.

These are concrete same-path add/add reconciliation candidates. When
integrating the broader stack, replace the landing-page contents with
the authoritative full source documents selected for that integration.
Retain the current
[link-repair record](../evidence/class-a-plus-upper-recurrence-2026-11-15/link-repair/README.md)
and historical import manifest as provenance; the repair pages are not
competing theorem documents. Replacing them does not by itself accept the
full documents' mathematical or executable claims.

## Read-only merge-tree result

The [recorded merge-tree operation](../evidence/class-a-plus-upper-recurrence-2026-11-15/stack-merge-tree.json)
compares source snapshot `b1f597fe18415eef826516e3f82d9a29397602f3`
(tree `175f2f3233d067ca0284900034ce9b2bcf0b6358`) with the stated
`729bbc33...` stack head. It returned exit 1 with six conflicted paths:

- `docs/class-a-plus-constant-entry-2026-11-14.md`;
- `docs/class-a-zero-defect-escape-2026-11-14.md`;
- `docs/proof-bank.md`;
- `docs/side-notes-ledger.md`;
- `proof/PscVerif/PscVerif/ClassAZeroDefectEscape.lean`;
- `proof/proof-bank.json`.

The exact source snapshot and prerequisite are preserved in a verified
[Git bundle](../evidence/class-a-plus-upper-recurrence-2026-11-15/compatibility-source-snapshot.bundle).
It contains the complete staged implementation, proof, tests, workflow
and documentation before the fresh-build acceptance records were added.
No checkout, working-tree merge or conflict resolution was performed;
`git merge-tree` did not change the worktree or index. The returned
conflict tree is a diagnostic artifact, not an accepted source tree.

The earlier clean merge-tree result in the eight-cycle note compared
pre-#583 main with the stack and does not carry forward. This increment's
direct main base is unchanged, so these six paths concern a future
broader-stack integration, not its direct main integration.

## Integration checks still required

After selecting the final integrated sources, reconcile the root Lean
imports and regenerate `proof/proof-bank.json` and `docs/proof-bank.md`
with `tools/make_proof_bank.py`. Do not resolve a generated-inventory
conflict by copying one branch's inventory over the other. Preserve both
branches' dated side-note entries, rerun link and governance checks, and
obtain fresh native and Lean acceptance for the actual integrated source.
The existing receipts certify their recorded source sets, not a future
merge or the broader stack's unresolved obligations.
