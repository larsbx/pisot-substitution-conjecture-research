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
| `python-tests`, `exact-kernels` (`tests/test_markdown_links.py`) | The 2026-10-31 ledger line about the link test quotes `o['…'](pathlib.Path(...))` in an *inline* code span; the test skipped fenced blocks only. | The test is taken byte-for-byte from #437 (`e8cfada1`): inline code spans are skipped too, with a delimiter-run regression. |

A third gate was red on `main` locally: the claim-governance `consistency`
audit (`PYTHONPATH=tools python3 -m claim_governance.cli --root .`) passed at
`012d563` and failed at `d4d97db` with six findings, because the README rewrite
(`2f841b9`, `d4d97db`) dropped the six `README.md` anchors that
`claim_governance.toml` binds (the five `=> …` chain lines and
`**Unique decodability:**`). The chain is restored in anchor form with its status
labels, unchanged in content; the audit passes again. The same rewrite also dropped the
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
