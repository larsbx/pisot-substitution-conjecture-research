# Exact-source hosted native carrier replay

The successful hosted native run is bound to source commit
`6021f042056d3cb0f9717d2488144339721c2071`, tree
`3355716258114a4f5353b10233fa1fa79bb34bbd`. The later merge commit
`1ce54efeff586ecda2ec1bd11a2f9c6617b2fb87` has the same tree. These are
separate identities: this packet does not relabel the hosted execution as
a run on the merge commit.

## Hosted records

- Repository: `larsbx/pisot-substitution-conjecture-research`.
- Run: https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43435276378
- Job: https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43435276378/job/131918634454
- Attempt: 1; status completed; conclusion success.
- Job started 2026-11-13 14:55:25 UTC and completed 14:56:38 UTC.
- Artifact: `14047853947`, named `c4-forward-carrier-native-6021f042056d3cb0f9717d2488144339721c2071`.
- Original ZIP SHA-256: `b362cf6b327667a4d038a847ec1422597990fec8a919c4a8ce802da6a53438e2`.

The three `*.provider.json` files retain raw GitHub REST response bodies;
`acquisition.json` records request URLs and retrieval times. The original
downloaded ZIP, every extracted member, decoded job log and provider-tool
log response are preserved. Both raw Git commit objects were checked
against their Git object identifiers. No original artifact was rewritten.

## Verified results

The hosted receipt records a fresh locked Pixi/Mojo build and a successful
45.918731-second native/oracle gate. All 258 tests passed in 32.56 seconds.
The compiler is Mojo `1.1.0.dev2026090805 (34562fa1)`, with installed package
metadata matched to the checked-in lock. The compiler package archive was
not independently rehashed by that gate; its receipt states this limit.

Independent inspection verified all 55 internal manifest entries, both
included executable hashes, and all 763 source hashes against the immutable
source commit. Revision records agree before and after replay; both worktree
records are empty and the gate records unchanged source bytes.

Both original JSON packets and all four generated Lean modules match their
source-commit bytes. Both budget refusals have nonzero exits and empty packet
output. A fresh optimized Python oracle replay of the actual downloaded JSON
packets returned zero and matched the hosted oracle receipt after removing
only machine-local input paths. The exact oracle code, executed review code,
recheck output and review receipt are retained. The review receipt records
the command and 3.418506-second recheck duration.

`verify_native_artifact.py` is the exact executed review program; its original
checkout path is preserved. To repeat it elsewhere, copy this packet into
fresh scratch space and point its `ROOT` constant to a checkout containing
the stated source and merge objects. Running it writes derived review and
recheck receipts in that copy. Preserve this original packet and manifest.

## Acceptance boundary

This is hosted native/oracle evidence for the stated source bytes. Its
receipt explicitly has `lean_kernel_acceptance: false`. It does not establish
full isolated Lean acceptance, either original archive's nine-endpoint
replay, termination, or any governed mathematical status promotion. Formal
workflows require their own successful terminal records and artifacts.
