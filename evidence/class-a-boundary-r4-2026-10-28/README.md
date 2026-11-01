# R4 complete stars and companion exits — 2026-10-28

Scope: R4=(x,y,1,-1,-2) and its real reversal throughout the inherited
minus class-A boundary k,t>=0. Complete stars have max(1,2t) occurrences
per orientation and a 20-label chamber-wide image. Selected typed exits take
three edges at t=0, four at t=1 and three at t>=2. All direct children are
productive on t<=1, including both distinct t=1 children. No all-t all-child
productivity is inferred.

Five new companions have uniform selected exits, without complete-star claims:
E4<=2, D4<=7 (<=3 at n>=4), Y4<=2, E5<=3, G5<=5. D4's sole n=3
member uses a separate seven-edge literal path. The proposed short edge at
ordinal 3 there is a real interior x/c child, not the intended x/y child.
Actual prefix types are retained throughout.

S41 now has 26 registered nonterminal complete stars plus C, 14 unregistered
complete-star labels and 27 registered exits including C. Y4 orientations have
exits without stars; T2 orientations have stars without registered exits.
Equal totals therefore cover different subsets. R4's image has two registered
complete stars but ten exits, leaving ten outgoing labels without registered
uniform exits. Every direct target lies outside S41 by c-coordinate +/-3.
The older R3/D3 36-label image now has 22 registered stars and 20 registered exits.

| Receipt | Outcome and exact scope |
| --- | --- |
| native.log | PASS: locked Mojo 1.1.0.dev2026090805; 56 members / 112 complete-star cells / 672 selected-path source cells / 33,096 literal pairs / 688 accepted occurrences; 352 R4 plus 1,688 companion path edges, 2,040 total; all 20 targets attained and final contract reached |
| driver.log | PASS: exact Q[t,k] field/incidence identities for all twelve oriented source labels, both complete R4 update tables, actual ancestry, constant/shifted-cone selected transitions, n=3 alternate transitions, inherited suffixes and all 61 source/image registry rows |
| python-scoped.log | PASS: twenty focused R4, B4, B3 and R3/D3 tests, including complete independent replay, true endpoint types, both t=1 children, companion exits without star flags and all-row native/source registry comparison |
| probe.json | Independent literal-word/integer-polynomial/Fraction replay: 117 members / 234 complete-star cells / 1,404 selected-path source cells / 122,616 pairs / 1,898 accepted / 728 R4 plus 3,518 companion path edges, 4,246 total; all 20 labels and actual reversals checked |
| reconciliation.json | Full 41-row candidate and 20-row image inventories, separately recording before/after complete-star and uniform-exit interfaces; every row compared with the canonical driver |
| tla.log | PASS: all 18 expected existing model outcomes, including the intended nonproductive countermodel; no new R4 TLA theorem claimed |
| lean-attempt.log | FAIL before compilation: local launcher reports `failed to locate application`; exit 1, no Lean pass credited |
| provenance.log | PASS: full `bash tools/verify_all.sh provenance`, including vendoring, generated ledgers/catalogue/proof bank, manuscript/Markdown integrity, hit-witness evidence and governance |
| dependencies.json | #377 exact-head snapshot at 318a866a; listed hosted workflows remain queued and are not passes |

The native replay reused the pinned environment at
/workspace/scratch/c319bc870de5/psc/kernel/pixi.toml with `--locked`, explicitly
compiling this worktree's absolute driver/test paths and including
/workspace/scratch/4a7239947ba8/psc/kernel with `-I`. Manifest and lock are
byte-identical to this worktree. Exact regression invocation:

```sh
/root/.pixi/bin/pixi run --locked \
  --manifest-path /workspace/scratch/c319bc870de5/psc/kernel/pixi.toml \
  mojo run -I /workspace/scratch/4a7239947ba8/psc/kernel \
  /workspace/scratch/4a7239947ba8/psc/kernel/tests/test_class_a_boundary_r4_children.mojo
```

Use the corresponding absolute driver path for the driver replay. Portable
commands are in docs/class-a-boundary-r4-carrier-2026-10-28.md. TLA ran with
TLA_TOOLS=/tmp/psc-tla2tools.jar; Lean with /root/.elan/bin on PATH. No floating
approximation enters a decision. The independent 512-refinement sign budget
refuses on exhaustion. Finite grids validate implementation; uniformity rests
on the exact guard, source-bound and shifted-cone/path reductions.

Controls preserve R4's missing proposed uniform index at t=0 and real LAST c
at t=1; D4's genuine interior LAST c edge at n=3; and E5's c-prefix giving
B2h rather than R(P0). They reject corrupt identities, bad inputs, disjoint
legal pairs, wrong interior image targets, changed/truncated paths, unequal-type
zero terminals, duplicate/incomplete stars, corrupt/omitted/duplicate registry
rows and unsupported companion complete-star requests.

No full local suite, fresh hosted acceptance, Lean pass, complete companion
stars, all-t all-child productivity, closed carrier, universal BH/#139 or PSC
conclusion is claimed. Keep this increment stacked on #377 and integrate after
required exact-head gates in dependency order. Preserve 124 governed claims,
34 named Lean proofs and 325 source openings. Independent human review remains
pending validation debt.
