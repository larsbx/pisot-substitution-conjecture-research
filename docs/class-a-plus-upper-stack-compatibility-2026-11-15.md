# Plus-Class-A upper cycles: main and stack compatibility

Inspection date: November 15, 2026. This note records the integration
decision for the eight upper-cycle occurrence paths. It is not an
acceptance receipt for the entire Class-A dependency stack.

## Integration decision

The increment targets main directly, starting at
`a19670c521927a8f6ac7e08f26cd3d563eafdce3`, on
`research/bh-class-a-plus-upper-cycles-main`. Only the missing Lean source
dependency closure, its historical hypothesis gates, and the exact
deferred problem statement are imported. The user authorized publication
and integration of this increment; that authorization does not turn the
unrelated stack into a required merge.

The initial problem source remains PR #581 revision
`9f0138d213357b866e7ceef0dcbfab96a667526d`. Subsequent PR merges into the
research stack do not change the source of the eight-case problem or
retroactively certify this new construction.

## Freshly inspected PR relationships

These are GitHub metadata observations, not inferred from PR titles.
The listed heads were also available in the fresh local clone.

| PR | Observed head | Status | Base or recorded merge destination |
| --- | --- | --- | --- |
| [#577](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/577) | `01c4e376a652fd93e981e7b302e989c65774a0de` | Open draft | main `a19670c521927a8f6ac7e08f26cd3d563eafdce3` |
| [#578](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/578) | `34ff471c24960729527ae5f090e96c7c16ae4584` | Open draft | #577 |
| [#579](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/579) | `729bbc33e9306d170eaa0d93bcf269aca6aeeece` | Open draft | #578 |
| [#580](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/580) | `3faf3cb4f4c4a39bdbedbb8fd58cb59a1ae17500` | Merged into #579 | Merge `729bbc33e9306d170eaa0d93bcf269aca6aeeece` |
| [#581](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/581) | `c972c4598cf0ddadb30ea6d8f205e1dec5bbafd2` | Merged into #579 | Merge `32524dc441073c2764a77ac35bfb833ceab3c0a0` |
| [#582](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/582) | `3091554246ffd673eb7148d00221631f878dfa42` | Merged into #579 | Merge `64c70311fe6ef69378f7bd308c034bb4193daa63` |

Thus #580--#582 being merged does not mean their source is present on
main. Main contains none of the five missing Class-A prerequisite modules
listed below.

The read-only merge-tree check of main and #579's observed head completed
without a textual conflict and produced tree
`f9d9dfd75cc138e79fad76d4324926871e38338e`. But that integration would add
304 changed files, 65,069 insertions and 8 deletions relative to main,
including density and boundary arguments, earlier family entry claims,
generated inventories and extensive separate evidence. Textual merge
compatibility does not justify importing that scope into an eight-cycle
increment.

## Exact Lean dependency closure

The new module imports `ClassAPlusConstantRecurrence` and
`ClassAMinusPrefixAssembly`. Recursively following local imports until a
module already exists on main gives exactly these five missing files:

| Module under `proof/PscVerif/PscVerif/` | Recorded source commit | SHA-256 |
| --- | --- | --- |
| `ClassAZeroDefectEscape.lean` | `9f0138d213357b866e7ceef0dcbfab96a667526d` | `a50672744789443300b5c7c4b6c0467c941fec5b1d833d7544e62440c729fa58` |
| `ClassACentralRecurrence.lean` | `9f0138d213357b866e7ceef0dcbfab96a667526d` | `f7e27955fe4238bf0a74bf31f6afe618c6d4769f047ad8ce5ffbdb4d39484a5b` |
| `ClassAMinusConstantRecurrence.lean` | `9f0138d213357b866e7ceef0dcbfab96a667526d` | `748b13de20f335033940b3cdddf2d648d10365c23080301b66dfd8db8a498e04` |
| `ClassAPlusConstantRecurrence.lean` | `9f0138d213357b866e7ceef0dcbfab96a667526d` | `c6dbd0f1065e698ee58a04c1781d63692129f2b5c17c97d0a74cc832fd25f79a` |
| `ClassAMinusPrefixAssembly.lean` | `3091554246ffd673eb7148d00221631f878dfa42` | `a2d6944184b75c47c6d307cee5cf5f6db78de4768f0b09b3d3218861665aaa7d` |

`OccurrenceSuccessor` already exists on main and terminates this local
closure. Boundary escape, root-spectrum, density and minus-family central
bridge modules are not dependencies of the new upper-cycle module.

The prefix helper is imported byte-for-byte from #582. Its generic
ordered-path, actual-mark trace, positive-scaling strictness and original
prefix assembly results are useful to the plus paths as well as the
minus development. Reusing those generic results does not assert a
plus-family recurrence classification or arbitrary-source entry theorem.

Compared with current #579, the original #581 versions of the central,
minus-constant and plus-constant recurrence modules are identical.
`ClassAZeroDefectEscape.lean` changed later in #580. This increment
deliberately retains its exact original #581 version; it does not silently
import the newer boundary-related revision. The later version has SHA-256
`04c10c8f84a07b5712dd1e5f05f713478d511a526496f4c1cb082a14d86188a7`.
Any future reconciliation with the larger stack must review that one
source difference explicitly.

The [import provenance manifest](../evidence/class-a-plus-upper-cycles-2026-11-15/imported-source-provenance.json)
records all 11 imported paths, commits, source URLs and digests. Fresh
local comparison checked both their SHA-256 digests and byte identity
against `git show COMMIT:PATH`.

## Historical documents and current executable scope

The five imported stop/go reviews and the deferred upper-entry memo are
unaltered historical source documents. Their relative links and narrated
workflow outcomes refer to the source commits recorded in the manifest;
the current main increment does not import every linked old artifact.
Use the manifest's canonical source URLs to read them in their original
repository context. The new [upper-cycle stop/go review](bh-class-a-plus-upper-cycles-stop-go-2026-11-15.md)
is the current decision for this work.

The native increment uses main's existing generic geometry interfaces.
It need not import the older Class-A central-entry implementation merely
to recognize typed zero. Independent finite replay uses the standalone
upper-cycle exact oracle. The separate symbolic checker defines the
eight complete path tables independently and proves polynomial index,
full-offset and original-prefix identities for `n=7+t`, `t>=0`.

The restored symbolic source and tests exactly match their surviving
pre-loss digests:

```text
791db6f79e236d43328eacede27617c74709eeac2c6d49f28345db7dc89b6582  oracles/python/class_a_plus_upper_symbolic.py
e4a51b16b6bd4a9a608688cd24682f219cbcee7701c3c497e70c7344a576df3c  tests/test_class_a_plus_upper_symbolic.py
```

Fresh execution in the replacement environment passed all 15 symbolic
tests. `symbolic.json` records 16 directed paths, 60 checked edges,
120 original occurrences, maximum depth 7, and 17 rejected mutation
controls. This unbounded polynomial check uses no finite sampling. Its
result covers literal occurrences and original prefixes; it does not
itself establish strict real geometry. The Lean path-to-prefix theorem
supplies strictness under explicit positive lengths and exact positive
inflation scaling. Exact finite root-interval fixtures test that geometry
independently at their stated members.

## Acceptance boundaries

The observed #579 head had successful dedicated
[plus-constant](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43698769310),
[central-entry](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43698769144),
[zero-defect](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43698769556),
[minus-constant](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43698769396)
and [literal-entry Lean](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43698769401)
runs. Its [PSC research checks](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43698769499)
and [canonical polynomial kernels](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43698769386)
failed. This compatibility review does not diagnose those two failures.

The observed #581 head independently had successful
[plus-constant](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43695233673),
[PSC research](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43695233891)
and [polynomial](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43695233722)
runs. These distinct producing heads must not be conflated. Neither
snapshot accepts the new upper-cycle candidate.

The new increment needs its own exact-source native replay, exact Lean
endpoint/axiom audits, fresh-source isolated acceptance and hosted checks
on its actual candidate head. Generated proof inventories must be
regenerated from the selected main source tree; generated artifacts from
the entire research stack are not a substitute. Importing a theorem's
source or observing an ancestor's successful workflow is not a receipt
for the assembled current source.

The replacement environment now supplies distinct local receipts:

- [Native execution](../evidence/class-a-plus-upper-cycles-2026-11-15/native-final.json)
  completed 160 directed paths and 600 edges, with 23 required refusal
  controls. The independent reader accepted the original raw output,
  including every full prefix witness. Its returned transcript digest
  equals the raw file's SHA-256. All 751 recorded native source/configuration
  inputs matched the current files at the compatibility recheck.
- [Fresh isolated Lean acceptance](../evidence/class-a-plus-upper-cycles-2026-11-15/lean-fresh/receipt.json)
  compiled the 20-module local dependency closure and the standalone
  semantic audit, using fresh pinned dependency checkouts and selected
  upstream artifacts. The audit checked 167 declarations, including
  114 theorem declarations, across the generic prefix helper and the new
  module; all eight exact endpoints and 24 negative controls passed.
  All 128 bound Lean source/configuration files still matched at recheck.
  The record preserves the failed launcher and disk-guard attempts, and
  distinguishes a later receipt-parser hardening/revalidation from the
  unchanged successful kernel compilation.

Independent adversarial inspection found and resolved two receipt-boundary
issues during reconstruction: universal-newline file reading could hide
CRLF bytes, and a fixed pre-run file list could miss newly appearing source
files. Current readers decode original bytes and accept only LF record
boundaries; the native runner re-enumerates the full source set afterward.
Actual CLI checks rejected CRLF input, and direct checks rejected Unicode
line-separator substitutions. These local checks do not assert hosted
acceptance on a future publication head.

This increment solves the eight selected cycle packets and their genuine
track reversals. The larger proposed recurrence, its tail classification,
all-source upper entry, small parameters outside the stated chamber and
universal BH #139 remain separate obligations. No closure claim for those
problems follows from stack compatibility or from these local paths.
