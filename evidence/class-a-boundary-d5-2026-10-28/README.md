# D5 complete stars and every-first-choice typed completions — 2026-10-28

Based on reconciled #380 at 4711576a09da2df29a5fbe26942b891a1db50395.
D5=(x,c,1,-1,0) and actual reversal have n+3 indexed strict children each:
two RF noncoincident children, n direct y/y coincidences and one actual x/x
coincidence. The chamber image has six labels. Every indexed first choice
has a selected typed completion to conventional C in at most seven edges,
attained through D6; every child tail is at most six. The original one-edge
D5 exit is preserved. The x/x terminal is retained before its actual
RR(1,1) normalization to C; no new full star is asserted for that terminal.

New companions D6/D7/C6 have uniform selected exit lengths 6/2/1 but no
complete-star registration. All eighteen labels of Y4's image now have
registered complete nonterminal stars and exits. Composed unchanged R5/B5
registries give S41 31 star/terminal interfaces and 33 exits; S43 adds
D5/reversal for 33 star/terminal interfaces and 35 exits. Both have ten
star gaps and eight exit gaps. R5's image has 8/18 stars/exits; B5's image
has 20/24 stars and 22 uniform exits. No uniform E7 exit is imported from
B5's finite n=4 tails. D5->D6 escapes S43; D6->T1 escapes the new image.
No forward closure or global BH/PSC promotion.

| Receipt | Outcome and exact scope |
| --- | --- |
| native.log | PASS, locked Mojo 1.1.0.dev2026090805: 56 members / 112 complete-star source cells / 504 selected-path source cells / 36,008 literal pairs / 1,400 strict occurrences / 1,176 selected source-path edges / 2,408 all-child walk edges. All six labels attained and every reversed accepted edge and produced walk verified; final contract reached; max walk seven. |
| driver.log | PASS, exact field/incidence identities for nine source orientations, all nine D5 prefix kinds, uniform typed ancestry/first transitions, X0 normalization and all 150 registry rows across six scopes. |
| probe.json | Independent literal-word/integer-polynomial/Fraction replay: 117 members / 234 star cells / 1,053 selected-path cells / 130,572 pairs / 3,744 accepted / 2,457 selected source-path edges / 5,850 all-child walk edges; all witnesses, reversals and produced walks checked. |
| reconciliation.json | Full S41, S43 and D5/Y4/R5/B5 image inventories, independently compared with all 150 native rows; terminal flag distinguishes C/X0 from complete nonterminal stars. |
| python-scoped.log | PASS, 48 D5/R5/B5/Y4/R4/B4/B3/R3 tests: all-pair geometry, exact touching, typed terminals, selected companions, every first choice, historical-scope preservation and registry corruption refusal. |
| tla.log | PASS, all eighteen expected existing TLA outcomes; no new D5 TLA theorem. |
| lean-attempt.log | FAIL before compilation, exit 1: local launcher reports `failed to locate application`. No Lean pass. |
| provenance.log | PASS, full provenance verification including vendoring, generated proof bank and ledgers, source integrity, hit-witness receipts and governance. |
| dependencies.json | Exact #380 snapshot and its workflow runs; queued/cancelled is not hosted acceptance. |

Native grids k=0..7,t=0..6; independent grids k=0..12,t=0..8. There are
1,400 and 3,744 complete first-choice walks respectively; walk-edge totals
are 2,408 and 5,850. The universal nine-kind guard proof and uniform symbolic
parameter-cone transitions are separate from these finite validation grids.
The exact sign budget refuses after 512 refinements; machine arithmetic refuses
overflow. No floating tolerance supplies an intersection or a coincidence.

Reproduce from repository root:

```sh
/root/.pixi/bin/pixi run --locked --manifest-path kernel/pixi.toml mojo run -I kernel kernel/tests/test_class_a_boundary_d5_children.mojo
/root/.pixi/bin/pixi run --locked --manifest-path kernel/pixi.toml mojo run -I kernel kernel/class_a_boundary_d5_children.mojo
python -m pytest -o addopts='' -q tests/test_class_a_boundary_d5_children.py tests/test_class_a_boundary_r5_children.py tests/test_class_a_boundary_b5_children.py tests/test_class_a_boundary_y4_children.py tests/test_class_a_boundary_r4_children.py tests/test_class_a_boundary_b4_children.py tests/test_class_a_boundary_b3_children.py tests/test_class_a_boundary_r3_children.py
python oracles/python/class_a_boundary_d5_children.py > /tmp/d5-probe.json
cmp /tmp/d5-probe.json evidence/class-a-boundary-d5-2026-10-28/probe.json
python -c "import runpy,pathlib; o=runpy.run_path('oracles/python/class_a_boundary_d5_children.py'); o['verify_native_registry'](pathlib.Path('evidence/class-a-boundary-d5-2026-10-28/driver.log').read_text())"
sha256sum -c evidence/class-a-boundary-d5-2026-10-28/source-sha256.txt
sha256sum -c evidence/class-a-boundary-d5-2026-10-28/SHA256SUMS
```

Canonical replay used /workspace/scratch/c319bc870de5/psc with its locked
Pixi environment. TLA used TLA_TOOLS=/tmp/psc-tla2tools.jar; Lean put
/root/.elan/bin on PATH. Source digests include both R5/B5 dependencies;
all historical sources, derivations and evidence packets remain unchanged.

Negative controls reject five exact boundary-touching families, wrong strict
in-image same-type targets, false LAST/LAST terminal types, unequal-type zero,
corrupt field identity, unsupported companion stars, invalid/overflow indices,
malformed stars/walks and missing/duplicate/corrupt registry rows. Exact word
prefixes and all Parikh coordinates are checked at every produced step.

No full local suite, hosted acceptance, Lean pass, new companion complete stars,
closed carrier, all-edge descent, all-source strict-zipper, plus/non-unit
realization, universal BH/#139 or PSC conclusion. Preserve 124 governed claims,
34 named Lean proofs and 325 source openings. Pending independent human review
is validation debt; required exact-head gates and dependency order remain.
