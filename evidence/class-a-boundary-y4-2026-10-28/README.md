# Y4 complete stars and every-direct-child typed tails — 2026-10-28

Scope: Y4=(x,y,1,0,-1) and its real reversal throughout minus class-A
k,t>=0. Each orientation has exactly 2n+2 strict child occurrences, with an
18-label chamber-wide image. Every indexed direct child has a uniform typed
tail <=7 edges. Every actual first choice therefore has a selected completion
from Y4 of <=8 edges; the bound eight is attained by the chosen walks. The
existing two-edge Y4 source exit is preserved. This does not assert that every
continuation terminates or that the image is forward closed.

New R5/D5 exits have lengths 3/1. T2 retains its inherited complete star and
now receives a uniform selected exit: five edges at t=0 through CM->V, seven
at t>=1 through M5->F0->D. No new complete stars are supplied for the new
companions. The actual T/Y4 two-cycle remains, with typed exits from both
states. Y4->D5 escapes S41; T->Y4 and R5->R(B2h) escape the 18-label image.

S41 now has 28 registered nonterminal complete stars plus C, 12 unregistered
star labels and 31 registered exits including C (10 exit gaps). Every registered
star/terminal label has an exit; R5 orientations have exits without stars.
Y4's image has 14 registered stars and all 18 registered exits. The older
R3/D3 36-label image now has 22 registered stars and 22 registered exits.

| Receipt | Outcome and exact scope |
| --- | --- |
| native.log | PASS: locked Mojo 1.1.0.dev2026090805; 56 members / 112 complete-star cells / 784 selected-path source cells / 33,096 literal pairs / 2,352 accepted occurrences / 3,104 selected source-path edges / 13,536 all-child walk edges; all 18 labels attained, maximum produced walk eight and final contract reached |
| driver.log | PASS: exact Q[t,k] field/incidence identities for all fourteen oriented source labels, complete Y4 update table, uniform RF/LR and conditional RR representatives, T/Y4 ancestry-cycle, typed new companion transitions and all 59 source/image registry rows |
| python-scoped.log | PASS: twenty-eight focused Y4, R4, B4, B3 and R3/D3 tests; every indexed child walk, all image tails, n=3/t=0 endpoint types, real cycle/escapes and all-row native/source registry comparison |
| probe.json | Independent literal-word/integer-polynomial/Fraction replay: 117 members / 234 complete-star cells / 1,638 selected-path source cells / 122,616 pairs / 6,552 accepted / 6,500 selected source-path edges / 39,676 all-child walk edges; all 18 labels and actual reversals checked, maximum walk eight |
| reconciliation.json | Full 41-row candidate and 18-row image inventories with separate before/after complete-star and uniform-exit interfaces; each row checked against the canonical driver |
| tla.log | PASS: all 18 expected existing model outcomes, including the intended nonproductive countermodel; no new Y4 TLA theorem claimed |
| lean-attempt.log | FAIL before compilation: local launcher reports `failed to locate application`; exit 1, no Lean pass credited |
| provenance.log | PASS: full `bash tools/verify_all.sh provenance`, including vendoring, generated ledgers/catalogue/proof bank, manuscript/Markdown integrity, hit-witness evidence and governance |
| dependencies.json | #378 exact-head snapshot at 4bdacc0d; listed hosted workflows remain queued and are not passes |

The native replay reused the pinned environment at
/workspace/scratch/c319bc870de5/psc/kernel/pixi.toml with `--locked`, explicitly
compiling this worktree's absolute driver/test paths and including
/workspace/scratch/4a7239947ba8/psc/kernel with `-I`. Manifest and lock are
byte-identical to this worktree. Exact regression invocation:

```sh
/root/.pixi/bin/pixi run --locked \
  --manifest-path /workspace/scratch/c319bc870de5/psc/kernel/pixi.toml \
  mojo run -I /workspace/scratch/4a7239947ba8/psc/kernel \
  /workspace/scratch/4a7239947ba8/psc/kernel/tests/test_class_a_boundary_y4_children.mojo
```

Use the corresponding absolute driver path for the driver replay. Portable
commands are in docs/class-a-boundary-y4-carrier-2026-10-28.md. TLA ran with
TLA_TOOLS=/tmp/psc-tla2tools.jar; Lean with /root/.elan/bin on PATH. No floating
approximation enters a decision. The independent 512-refinement sign budget
refuses on exhaustion. Finite grids validate implementation; the exact guard,
index-cone and complete uniform tail arguments supply the quantified result.

Controls retain n=3's actual LR R4 instead of a fictitious RR R(T2), T2's
t=0 actual LAST c instead of RUN y, the distinct M5/CM prefixes and R5's
bottom y prefix. They reject corrupt identities, bad inputs, disjoint legal
pairs, wrong interior targets, altered/truncated all-child walks, false unequal-type
zero terminals, incomplete/duplicate stars, omitted/duplicate/corrupt registry rows,
unknown tail-dispatch labels and unsupported new companion complete-star requests.

No full local suite, fresh hosted acceptance, Lean pass, new companion complete
stars, all-T2-child productivity, forward closure, all-edge descent, universal
BH/#139 or PSC conclusion is claimed. Keep this increment stacked on #378 and
integrate after required exact-head gates in dependency order. Preserve 124
governed claims, 34 named Lean proofs and 325 source openings. Independent human
review remains pending validation debt.
