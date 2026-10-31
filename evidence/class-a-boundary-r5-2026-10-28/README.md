# R5 complete oriented stars — 2026-10-28

Scope: R5=(x,y,1,-1,-1) and its actual reversal for every minus class-A
k,t>=0. The complete nine-kind table has exactly 2n+2 indexed strict children
per orientation at t=0, otherwise 2n+3. The chamber-wide image has eighteen
labels, all attained. The previously certified selected source exit remains
three edges via R(B2h). This packet adds no new selected exits.

Six image labels have existing complete stars and exits in the P/H3 packets:
B2, B2h and K with actual reversals. Those proofs are reused and their paths
replayed. Twelve image labels still lack registered exits; every-direct-child
productivity remains unproved. S41 now has thirty nonterminal complete stars
plus C, ten star gaps and ten exit gaps. Y4's eighteen-label image has sixteen
complete stars and eighteen exits; only D5 and reversal lack star interfaces.
The old R3/D3 image retains twenty-two stars and exits among thirty-six labels.
R5->R(B2h) escapes S41; K->L escapes R5's image. No closure or global BH/PSC.

| Receipt | Outcome and scope |
| --- | --- |
| native.log | PASS, locked Mojo 1.1.0.dev2026090805: 56 members / 112 oriented source cells / 33,096 literal pairs / 2,448 accepted occurrences / 336 selected R5 path edges / 678 reused K/B2/B2h exit edges. All eighteen labels attained; actual reversal of every accepted edge checked; final contract reached. |
| driver.log | PASS, exact source field/incidence identities, complete symbolic prefix updates, uniform RR/RL, FF face and RF shifted attainment cones, Y4 ancestry and all 59 source/image registry rows. |
| probe.json | Independent literal-word/integer-polynomial/Fraction replay: 117 members / 234 source cells / 122,616 pairs / 6,760 accepted / 702 selected R5 path edges / 1,410 reused exit edges. All image labels have exact witnesses and reversed edges. |
| reconciliation.json | All 41 S41 rows and 18 R5-image rows with separate before/after complete-star and current uniform-exit interfaces. Independent comparison with the native driver passes. |
| python-scoped.log | PASS, 34 focused R5/Y4/R4/B4/B3/R3 tests, including independent exhaustive-pair comparison, endpoint/prefix controls, typed paths and all-row registry refusal controls. |
| tla.log | PASS, all 18 expected existing TLA outcomes, including the intended nonproductive countermodel. No new R5 TLA theorem. |
| lean-attempt.log | FAIL before compilation, exit 1: local launcher reports `failed to locate application`. No Lean pass. |
| provenance.log | PASS, complete `bash tools/verify_all.sh provenance`: vendoring, generated proof bank/ledgers/catalogue, source integrity, archived hit-witness evidence and governance. |
| dependencies.json | Parent #379 at 7eb395cce20973c2c36bef09c97b3d6ae8e57067. Observed hosted workflows remain queued, not passed. |

Reproduce native receipts from the root with:

```sh
/root/.pixi/bin/pixi run --locked --manifest-path kernel/pixi.toml \
  mojo run -I kernel kernel/tests/test_class_a_boundary_r5_children.mojo
/root/.pixi/bin/pixi run --locked --manifest-path kernel/pixi.toml \
  mojo run -I kernel kernel/class_a_boundary_r5_children.mojo
```

This replay uses the restored repository checkout at
/workspace/scratch/c319bc870de5/psc and a fresh locked environment there.
The old scratch worktree's unavailable git worktree metadata was not used.
No source change or unpinned environment is substituted. Portable equivalents
from kernel/ start with `pixi run --locked mojo run -I .`.

Independent replay and inventory reconciliation:

```sh
python -m pytest -q tests/test_class_a_boundary_r5_children.py \
  tests/test_class_a_boundary_y4_children.py tests/test_class_a_boundary_r4_children.py \
  tests/test_class_a_boundary_b4_children.py tests/test_class_a_boundary_b3_children.py \
  tests/test_class_a_boundary_r3_children.py
python oracles/python/class_a_boundary_r5_children.py > /tmp/r5-probe.json
cmp /tmp/r5-probe.json evidence/class-a-boundary-r5-2026-10-28/probe.json
python -c "import runpy,pathlib; o=runpy.run_path('oracles/python/class_a_boundary_r5_children.py'); o['verify_native_registry'](pathlib.Path('evidence/class-a-boundary-r5-2026-10-28/driver.log').read_text())"
sha256sum -c evidence/class-a-boundary-r5-2026-10-28/source-sha256.txt
sha256sum -c evidence/class-a-boundary-r5-2026-10-28/SHA256SUMS
```

Native k=0..7,t=0..6; independent k=0..12,t=0..8. No floating decision.
The independent sign budget is 512 exact refinements and refuses on exhaustion;
canonical index arithmetic refuses overflow. Universal classification rests on
the complete integer guard reductions and symbolic parameter cones in
`docs/class-a-boundary-r5-carrier-2026-10-28.md`, not finite-grid extrapolation.
The stop/go reuses prior primary-source review and records no fresh reading.
TLA used TLA_TOOLS=/tmp/psc-tla2tools.jar; Lean put /root/.elan/bin on PATH.

Controls preserve t=1's actual strict FIRST/FIRST edge at nominal RF(t-1,0),
t=0's clipped indices, and the actual R5/D3 prefix distinction. They refuse
invalid chamber/orientation/indices and machine overflow, corrupt field identity,
disjoint literal pairs, wrong strict in-image targets of identical types,
incomplete/duplicate stars, altered/truncated paths, false unequal-type zero
terminals and missing/duplicate/corrupt inventory rows. B2's n=3 LAST-c control
is inherited and its longer true exit is replayed.

No full local suite, fresh hosted acceptance, Lean pass, new companion theorem,
every-child productivity, closed carrier, all-edge descent, plus/non-unit
internal-space transfer, universal BH/#139 or PSC claim. Preserve 124 governed
claims, 34 named Lean proofs, 325 source openings and pending independent review.
Integrate in dependency order only after required exact-head gates.
