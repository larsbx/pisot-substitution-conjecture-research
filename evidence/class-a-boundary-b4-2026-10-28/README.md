# B4 complete stars and three-case typed exits — 2026-10-28

Scope: B4=(y,x,0,-1,-1) and its true reversal throughout the inherited
minus class-A boundary k,t>=0. Complete stars have max(1,2t-1) occurrences
per orientation and a 32-label chamber-wide outgoing union. The inherited
exact alpha=1/2 separator changes indices, not the total count. B4 has a
three-edge typed exit at t=0 and a five-edge exit otherwise.

The two new companions D0=(x,x,-1,-2,3) and F4=(x,y,-1,-2,4) have uniform
two- and four-edge selected exits. Their complete stars remain unproved in
this packet and are not registered. At t=1 the existing reversed Dxx proof
is reused. On t<=1, B4 has a single child and the selected suffix proves
that sole child productive. No all-t all-child productivity is inferred.

S41 now has 24 registered nonterminal complete stars plus C and 16 unregistered
labels, with 23 registered exits including C. The T2 orientations retain stars
without registered uniform exits. B4's outgoing image has only two registered
complete stars but six exits; D0/F4 supply exits without complete-star flags.
Twenty-six of its 32 labels still lack registered exits. All 32 outgoing labels
lie outside S41 by their c-coordinate +/-2. The older R3/D3 36-label image
now has 20 registered stars and 18 registered exits.

| Receipt | Outcome and exact scope |
| --- | --- |
| native.log | PASS: locked Mojo 1.1.0.dev2026090805; 56 members / 112 complete-star cells / 336 selected-path source cells / 33,096 literal pairs / 592 accepted occurrences; 528 B4 and 672 companion path edges, 1,200 total; all 32 targets attained and final contract reached |
| driver.log | PASS: exact Q[t,k] field/incidence identities, both complete B4 typed update tables, actual ancestry, constant/shifted parameter-cone selected transitions, inherited suffixes and all 73 source/image registry rows |
| python-scoped.log | PASS: fourteen focused B4, B3 and R3/D3 tests, including independent complete replay, endpoint/half-chamber controls, separate star/exit coverage and all-row native/source inventory comparison |
| probe.json | Independent literal-word/integer-polynomial/Fraction replay: 117 members / 234 complete-star cells / 702 selected-path source cells / 122,616 pairs / 1,690 accepted / 1,118 B4 plus 1,404 companion path edges, 2,522 total; all 32 targets and real reversals checked |
| reconciliation.json | Complete 41-row candidate and 32-row image inventories, each with separate before/after complete-star and uniform-exit interfaces; extracted from the independent probe and compared individually with the canonical driver |
| tla.log | PASS: all 18 expected existing model outcomes, including the intended nonproductive countermodel; no new B4 TLA theorem claimed |
| lean-attempt.log | FAIL before compilation: local launcher reports `failed to locate application`; exit 1, no Lean proof pass credited |
| provenance.log | PASS: full `bash tools/verify_all.sh provenance`, including vendoring, generated ledgers/catalogue/proof bank, manuscript/Markdown integrity, hit-witness evidence and governance |
| dependencies.json | #376 exact-head snapshot at 995331ff; listed hosted workflows remain queued and are not passes |

The native replay reused the existing pinned environment at
/workspace/scratch/c319bc870de5/psc/kernel/pixi.toml with `--locked`, explicitly
compiling this worktree's absolute driver/test paths and including
/workspace/scratch/4a7239947ba8/psc/kernel with `-I`. The manifest and lock are
byte-identical to this worktree. Exact regression invocation:

```sh
/root/.pixi/bin/pixi run --locked \
  --manifest-path /workspace/scratch/c319bc870de5/psc/kernel/pixi.toml \
  mojo run -I /workspace/scratch/4a7239947ba8/psc/kernel \
  /workspace/scratch/4a7239947ba8/psc/kernel/tests/test_class_a_boundary_b4_children.mojo
```

Use the corresponding absolute driver path for the driver replay. Portable
commands are in docs/class-a-boundary-b4-carrier-2026-10-28.md. TLA ran with
TLA_TOOLS=/tmp/psc-tla2tools.jar; Lean with /root/.elan/bin on PATH. No floating
approximation enters a decision. The independent sign budget is 512 refinements;
exhaustion refuses. Finite grids validate implementation. The universal guards
and paths are established by the exact reductions and shifted-cone certificates.

Controls retain low diagonal k=t=0,1 versus high k=t>=2; the different t=4
index sets with equal counts; t=0's missing index and t=1's real LAST x with
the same Parikh offset as the false RUN target. They reject corrupt identities,
bad inputs, disjoint legal pairs, wrong interior image targets, changed/truncated
paths, false unequal-type zero terminals, duplicate/incomplete indexed stars and
unsupported companion complete-star requests.

No full local suite, fresh hosted acceptance, Lean pass, complete companion
stars, all-t all-child productivity, closed carrier, universal BH/#139 or PSC
conclusion is claimed. Keep this increment stacked on #376 and integrate after
required exact-head gates in dependency order. Preserve 124 governed claims,
34 named Lean proofs and 325 source openings. Independent human review remains
pending validation debt.
