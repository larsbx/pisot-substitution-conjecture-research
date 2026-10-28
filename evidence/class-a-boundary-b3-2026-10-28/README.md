# B3 complete stars and two-edge typed exit — 2026-10-28

Scope: B3=(y,x,0,-1,0) and its actual reversal throughout the inherited
minus class-A boundary cone k,t>=0. Complete stars have 2n+2 occurrences
per orientation at t=0 and 2n+3 otherwise, with 20 labels in their chamber-wide
outgoing union. B3(0,n+2)->H1(1,2)->C gives a uniform two-edge typed exit.
The same first edge escapes S41 because H1 is absent from that candidate.

S41 now has 22 registered nonterminal complete stars plus C and 18 unregistered
labels. Its separate registered-exit count is 21 including C; the T2 orientations
retain stars without registered exits. The older R3/D3 36-label image now has
18 registered stars and 16 registered exits. B3's 20-label image has ten of each.
Unregistered means no interface bound here, not mathematical unproductivity.
All-direct-child productivity remains unproved.

| Receipt | Outcome and exact scope |
| --- | --- |
| native.log | PASS: locked Mojo 1.1.0.dev2026090805, 56 members / 112 source cells / 33,096 literal pairs / 2,448 accepted / 224 selected path edges; all 20 labels attained and final contract receipt reached |
| driver.log | PASS: exact Q[t,k] incidence/field identities, actual indexed ancestry/exit/endpoints, inherited certificates and complete 41-row registry |
| python-scoped.log | PASS: eight focused B3 and predecessor R3/D3 tests, including complete literal-star replay, endpoint types, all-row native/source inventory comparison and negative controls |
| probe.json | Independent literal-word/integer-polynomial/Fraction replay: 117 members / 234 source cells / 122,616 pairs / 6,760 accepted / 468 selected path edges; every actual reversed edge and all 20 labels checked |
| reconciliation.json | All 41 before/after star and exit rows, extracted from the independent probe and compared individually with native driver output |
| tla.log | PASS: all 18 expected existing model outcomes, including the intended nonproductive countermodel; no new B3 TLA theorem claimed |
| lean-attempt.log | FAIL before compilation: local launcher reports `failed to locate application`; exit 1, no proof pass credited |
| provenance.log | PASS: full `bash tools/verify_all.sh provenance`, including vendoring, generated ledgers/catalogue/proof bank, manuscript/Markdown integrity, hit-witness evidence and governance |
| dependencies.json | #375 exact-head snapshot at 5143d72e: listed hosted workflows queued, not accepted; inherited predecessors remain governed by their unchanged receipts |

The native replay used the existing pinned environment at
/workspace/scratch/c319bc870de5/psc/kernel/pixi.toml with `--locked`, explicitly
compiling this worktree's absolute driver/test paths and including
/workspace/scratch/4a7239947ba8/psc/kernel with `-I`. Its manifest and lock
were compared byte-for-byte with this worktree. Exact invocation:

```sh
/root/.pixi/bin/pixi run --locked \
  --manifest-path /workspace/scratch/c319bc870de5/psc/kernel/pixi.toml \
  mojo run -I /workspace/scratch/4a7239947ba8/psc/kernel \
  /workspace/scratch/4a7239947ba8/psc/kernel/tests/test_class_a_boundary_b3_children.mojo
```

Substitute the corresponding absolute driver path for the driver replay.
Portable fresh-environment replay is given in the derivation. TLA was run with
TLA_TOOLS=/tmp/psc-tla2tools.jar; Lean with /root/.elan/bin on PATH. The oracle's
512-refinement sign budget refuses on exhaustion. No floating approximation
enters a decision. Finite replays validate the implementation; the universal
nine-kind argument is in docs/class-a-boundary-b3-carrier-2026-10-28.md.

Negative controls preserve actual LAST edges when a proposed RUN index reaches
the endpoint. At t=0 the clipped RR upper pair (N,A+1) is y/x, not disjoint
and not P1. At t=0/1 the proposed LR boundary ordinals are actual LAST x.
Wrong interior targets, broken paths, false unequal-type zero terminals,
corrupt field identities, malformed stars and invalid inputs are refused.

No full local native/Python-suite pass, fresh hosted pass, Lean proof pass,
all-child productivity, closed carrier, universal BH/#139 or PSC claim is made.
Keep this increment stacked on #375 and integrate only after required exact-head
gates in dependency order. Preserve 124 governed claims, 34 named Lean proofs
and 325 source openings. Independent human review remains pending validation debt.
