# Open pull-request triage and main red-check repair (2026-10-31)

Status: provenance/governance audit plus one CI repair. No theorem, claim
status, kernel source or archived receipt changes. Nothing below is new
mathematical evidence; no PR was merged, closed, retargeted or commented on.

## Scope

The 30 open PRs at `main` `d4d97db` (#378–#439), each compared by its own diff
against its base, a `git merge-tree` against `main`, and the latest run per
check name on its head (GitHub check-runs API, 2026-10-31 ~20:00Z).

## 1. Main is red on three inherited checks

Every PR whose CI finished fails `complete-residual (plus)`, and #380/#411/#415/#416/#417
also fail `python-tests` and `exact-kernels` (whose `pytest oracle regressions` step runs the same link test). Both failures reproduce on `main` itself and are
independent of the PRs.

| check | cause on `main` | repair here |
|---|---|---|
| `complete-residual (plus)` (`class-d-positive-b-evidence.yml`) | Fit-first (#407) moved the replayed plus receipt from `boundary_lines= 73 finite_prefix_pip= 952` to `51 / 287`; the hosted replay 41066419210 and `evidence/class-d-closure-rebind-2026-10-30/` record the new line, but the workflow's `grep -Fx` still pinned the accepted one. Failing log: job 124433209307 at `f785232`, which prints exactly the 51/287 line. | The workflow pins the rebound receipt. |
| `python-tests`, `exact-kernels` (`tests/test_markdown_links.py`) | The 2026-10-31 ledger line about the link test quotes `o['…'](pathlib.Path(...))` in an *inline* code span; the test skipped fenced blocks only. | Fixed by #437 (merged as `cafaad01`): inline code spans are skipped too; this branch carried the same bytes. |

A third gate was red on `main` locally: the claim-governance `consistency`
audit (`PYTHONPATH=tools python3 -m claim_governance.cli --root .`) passed at
`012d563` and failed at `d4d97db` with six findings, because the README rewrite
(`2f841b9`, `d4d97db`) dropped the six `README.md` anchors that
`claim_governance.toml` binds (the five `=> …` chain lines and
`**Unique decodability:**`). The chain is restored in anchor form with its status
labels; #437 (merged as `cafaad01`) made the same repair concurrently and its wording is kept. The audit passes again. The same rewrite also dropped the
review-policy sentence `tests/test_review_policy.py` requires on every human
surface (*Independent human review is a final validation gate, not a
research-progress gate.*); it is restored with a link to the AGENTS.md rule.

The workflow is hash-frozen by `tools/check_class_d_integration_ci.py`, which
admits only an added concurrency block or added trigger paths, and a rebind
packet admits only import-closure sources, not workflows. The checker
therefore gains one narrow rule, `rebound_receipt_pin_only`: the
accepted plus receipt may be replaced by a receipt that a *valid* rebind packet
pins (`check_class_d_closure_rebind.rebound_plus_receipts`), and restoring it
must give bytes the existing rules accept. Fail-closed column: *refuse the run*.

Negative controls (`tests/test_class_d_integration_ci.py`):

* with the rule disabled, the full audit refuses the edited workflow
  (`accepted mathematical source, lock or workflow changed`);
* a forged pin (`finite_prefix_pip= 286`), an unchanged pin, an empty receipt
  set, a changed command, or an extra step each refuse;
* the live workflow must not contain the accepted 73/952 line and must contain
  exactly one rebound receipt.

The 73/952 pins in `kernel/psc/class_d_assembly.mojo`, its test, and the two
checkers are **historical** (they read the archived 2026-10-20 aggregate or the
accepted run) and stay unchanged.

## 2. Mergeability

* #411–#439 (22 PRs): merge into `main` without conflicts.
* #378, #379, #380, #382, #391, #392, #394, #395 (the 10-28/10-29 stacks): conflict
  with `main` **only** in the append-only `docs/side-notes-ledger.md`.
* Files carried by two PRs are byte-identical (`#426` ⊇ the oracles of
  #420/#424/#425; `tests/test_markdown_links.py` on #437 and here), so they
  merge in any order.

## 3. CI state

Runner starvation: none of #421–#439 has a completed success or failure;
their checks have been queued since ≈04:30Z, and superseded runs on
#428/#430/#433/#434/#438 show as cancelled. Of the PRs that finished, after
the two inherited failures above:

| PR | own failing checks |
|---|---|
| #378, #380 | `two-oriented-stars` |
| #392, #394 | `cover (plus)` |
| #415 | `six-label-typed-exits` |
| #411, #415, #416, #417, #420 | `evidence-policy`: PR body lacks the `## Work shown` headings |
| #379, #382, #391, #395 | none |

## 4. Content and dependency findings

**Class C.** #392 (BH for `n ≥ 3d+4` plus / `3d+6` minus, `d ≥ 6`) is contained
in merged Theorem T_C2 (`3d ≤ n`, every `d ≥ 1`, both signs;
[strip theorem](class-c-strip-theorem-2026-10-29.md)). #394 adds the strip
`2n ≥ 5d+8` plus / `5d+16` minus with `n < 3d`, which is inside the open lower
cone; it uses #392 only for `n ≥ 3d`, now provided by T_C2.
*Proposed:* close #392 as superseded, and retarget #394 to `main`, citing T_C2.

**Old class-A stack.** #378 → #379 → {#380, #382 → #391 → #395} rests on
`research/class-a-boundary-b4-2026-10-28`, which has no open PR and 8 commits
not on `main`. The newer PRs recover selected pieces instead (#412 merged;
#424, #425 open). *Proposed:* finish the selective recovery of Y4/E6/J9/H9 and
retire the stack, rather than merge it.

**X-hub chain** (cited dependencies):
#428 → #430 → #431 → #432 → #433 → #434 → #435 → {#438 → #439, #437};
#427 → #429; #420 → #421 → #424 → #425 → #426; #416 → #417; #411, #412, #414 → #415.
Only #430/#431, #434/#435, #417 and #439 are stacked by base branch; the rest
target `main` while citing open PRs.

**Policy gaps (AGENTS.md).** #415–#435 except #411 add Python only, with no
`kernel/` module, no recorded Mojo blocker, no stop/go note and no side-notes
line. #411 and #436–#439 carry Mojo.

## Proposed order

1. Merge this repair, so every PR's `complete-residual (plus)` / `python-tests` can pass.
2. Re-run the starved checks; add `## Work shown` sections to the five PR bodies.
3. The X-hub chain in dependency order, from #428; port each
   Python-only PR to `kernel/` or record its Mojo blocker before it merges.
4. Close #392 and retarget #394 to `main`; retire the 10-28 stack after recovery.

## Non-claims

No PR is judged mathematically correct or incorrect here; supersession is by
stated scope only. No CI result is inferred for a queued run. The new checker
rule admits no receipt that a validated hosted replay did not print.

## Follow-up, 2026-11-01

Actions taken (authorized by the repository owner, one step at a time):

| step | done |
|---|---|
| 1 | #441 merged (`288732c4`); its `complete-residual (plus)` job passed on the PR head (51/287 receipt). |
| 2 | `main` merged into #411, #415, #416, #420, #421, #424–#429, #432, #433 (update-branch) and into the stacked #417, #430, #431, #434, #435, #439 (their bases). Conflicts in #436, #438 and #394 were resolved by hand, with `main`'s side-notes entries first; #438 keeps `main`'s link test plus its own extra regression. |
| 2 | `## Work shown` added to the descriptions of #411, #415–#417, #420, #421, #424–#435. The sections are drafted only from each PR's own files, with every multi-digit figure checked against them and the original description kept verbatim on top. |
| 2 | Missing `SHA256SUMS` added to #436 (`class-a-x-signed-strip`, `class-a-x-cross-strip`) and #438 (`class-a-parikh-acceptance`); pins are the bytes as committed. |
| 4 | #392 closed as superseded by T_C ∪ T_C2 (same normal form; `n ≥ 3d+4` / `3d+6`, `d ≥ 6` ⊂ `n ≥ 3d`, `d ≥ 6`), branch kept; #394 retargeted to `main`. |

PR-own failures fixed:

* **#415** (`442d170d`): the reversal pass compared base-normalized labels with
  the reversed label set, so the assertion could never hold. With the comparison
  corrected, every pinned count reproduces. The workflow's malformed trigger entry
  is split, and it now runs the symbolic-geometry test it listed but never ran.
* **#394** (`8450a9dc`): only the source-hash step of `cover (plus)` failed. A full
  local replay on the merged head reproduced every plus and minus receipt, the
  native test log and the oracle byte-for-byte; only then were three source
  digests re-recorded (`evidence/class-c-below-three-2026-10-29/rebind-2026-11-01.md`).

Inconsistencies found while drafting, recorded in each PR's own description and
left for its author:

* Stale local-run pins: #427's test blob, #429's oracle and test blobs, and #431's
  source blob name earlier commits, not the head bytes.
* Figures quoted but not asserted by any test: #428's 351-vertex nine-seed closure
  (#429 does test it), #429's "sixteen labels", #433's Reach(S9)=351, and #434's
  (3,0) edge counts and depth bound.
* #431's `symbolic_star()` checks only a count identity; the universal E6 star rests
  on the written derivation plus finite specimens.
* #425 claims a "corrupted target" control that no test exercises. #435's
  symmetric-cycle control is run against the BFS producer only, not against
  `verify_rank`.
* #433 targets `main`, but its identity depends on the open #428, #430, #431 and #432.

Still open:

* #378 and #380 `two-oriented-stars`: their packets pin `kernel/pixi.toml`. Not
  fixed, since the 10-28 stack is proposed for retirement.
* #394's docs still cite #392 at `82dc6955` as the upper-bound dependency. Re-citing
  T_C2 is a change to the mathematical text, so it is left to the author.
* The Python-only PRs still need a Mojo port or a recorded Mojo blocker.
* #436 `python-tests` / `exact-kernels`: its tests import `sympy`, which the shared
  jobs never install, and `pyproject.toml` is hash-frozen by the class-D gate. This
  branch adds the narrow `appended_dev_extras_only` rule; after it merges, #436 can
  append `sympy==1.14.0` to the `dev` extra.
