# R3/D3 complete stars and source reconciliation — 2026-10-28

Scope: four oriented R3=(x,y,1,-1,0), D3=(x,c,1,-1,-1) stars throughout
the inherited minus class-A boundary cone k,t>=0. R3 has 2n+3 occurrences
per orientation; D3 has 2n+4 at t=0 and 2n+5 otherwise. Their chamber-wide
outgoing union has 36 labels. R3 has a two-edge typed exit; D3 has a selected
exit of six edges at k=0 and four at k>=1, reusing the established P0 suffix.
Every direct child's productivity is not established.

The 39-label candidate initially has 16 registered nonterminal complete stars
and C, with 22 unregistered labels. R3's two orientations reduce that gap to
20. Adding D3 and its reversal yields 41 labels with 20 registered nonterminal
stars, C and 20 unregistered labels. R3->D3 escapes the 39-label set, and
D3->P0 escapes the 41-label set. Registry membership does not prove coverage
of all relevant overlaps or applicability/impossibility of unregistered methods.

| Receipt | Outcome and exact scope |
| --- | --- |
| native.log | PASS: locked Mojo 1.1.0.dev2026090805, 56 members / 224 oriented source cells / 69,104 pairs / 5,136 accepted / 700 selected path edges; all 36 targets attained, every literal pair checked, complete contract receipt reached |
| driver.log | PASS: symbolic Q[t,k] transport/field identities, shifted actual-index cones, source ancestry, selected first edges and inherited suffix certificates; 39 complete native registry rows |
| python-scoped.log | PASS: four focused tests including all-row native/oracle inventory comparison and negative controls |
| probe.json | Independent literal-word/integer-polynomial/Fraction replay: 117 members / 468 source cells / 253,188 pairs / 14,014 accepted / 1,440 selected path edges; every actual reversed edge and all 36 labels checked |
| reconciliation.json | Complete 39-row before/after source and exit registry, extracted from the independent probe; every row cross-checked against the canonical driver |
| tla.log | PASS: all 18 expected existing model outcomes, including the intended nonproductive countermodel; no new R3/D3 TLA theorem claimed |
| lean-attempt.log | FAIL before compilation: local launcher reports `failed to locate application`; exit 1, no proof pass credited |
| provenance.log | PASS: full `bash tools/verify_all.sh provenance`, including vendoring, ledgers/catalogue/proof bank, manuscript/Markdown integrity, hit-witness evidence and governance |
| dependencies.json | Exact-head #372/#373 check snapshot; incomplete hosted gates remain blockers to dependent integration, not blockers to scoped proof development |

The native replay reused the existing pinned environment at
/workspace/scratch/c319bc870de5/psc/kernel/pixi.toml with `--locked`, while
explicitly compiling `/workspace/scratch/dcf9c4be57c4/r3/kernel` via `-I`
and absolute driver/test paths. Its manifest and lock are byte-identical to
the current worktree. Portable replay commands are in the derivation.
No floating-point arithmetic enters any decision. Python's independent sign
budget is 512 refinements; exhaustion refuses instead of guessing.

The earlier Q3 continuation's broad local Python log contains only partial
progress, with no completion summary; its old process handle is unavailable.
No full-suite pass or completion is inferred. This packet's fresh scoped
receipts are separate. No full local native or Python suite pass is claimed.
Fresh exact-head hosted native, Python, Lean, TLA, provenance and evidence-policy
checks remain required, and integration must follow #372 then #373 then this
increment. Preserve both predecessor evidence packets unchanged.

No Lean/TLA source or governed status changed. Inventory remains 124 governed
claims, 34 named Lean proofs, 325 source openings. Independent human review
pending; no BH/#139, A1-prime, G1 or PSC promotion.

From repository root:

```sh
python -m pytest -q tests/test_class_a_boundary_r3_children.py
python oracles/python/class_a_boundary_r3_children.py > /tmp/r3.json
cmp /tmp/r3.json evidence/class-a-boundary-r3-2026-10-28/probe.json
sha256sum -c evidence/class-a-boundary-r3-2026-10-28/source-sha256.txt
sha256sum -c evidence/class-a-boundary-r3-2026-10-28/SHA256SUMS
```
