# Class-A zero-defect escape: exact-source evidence

Date: 2026-11-14. Development base:
`c9358c2d46d7b306853609e2c5a090328aff92c3`. The publication is rebased
onto `a19670c521927a8f6ac7e08f26cd3d563eafdce3`, retaining #575's
roadmap and ledger entry. That base advance changes documentation only;
the mathematical runtime/formal dependencies used by the receipts are unchanged.

The result is a **parameter-uniform local occurrence theorem**: every strict
minus-Class-A overlap with `p=delta(a,b)` and `p+q+r=0` admits an actual
ordered-occurrence path to full integral offset zero in at most ten steps.
The [written proof](../../docs/class-a-zero-defect-escape-2026-11-14.md)
gives the complete endpoint classification, all thirteen endpoint paths,
parameter guards, strict geometry, original multilevel prefix addresses,
and the remaining source-entry obligation. The
[stop/go note](../../docs/bh-class-a-entry-stop-go-2026-11-14.md) precedes
the new theorem-facing experiments.

## Verification layers

| Layer | Observed local result | Scope |
| --- | --- | --- |
| Canonical native path table | 14 members, 176 endpoint paths, 904 overrun/reversal paths, 4,145 checked edges, maximum selected length 10 | Every edge retains its actual original ordinals, types and three Parikh coordinates; exact Perron geometry also checked |
| Full native/oracle differential | 1,332 complete path records, 4,145 edges | Exact expected source set, no duplicate/missing records, every original ordinal and intermediate full offset compared |
| Independent entire strict-slice replay | 3,970 sources, 6,512 edges at 14 named parameters | Complete strict affine slice at those parameters; finite regression, not parameter extrapolation |
| Universal symbolic certificate | 199 endpoint/chamber paths; 398 directed paths with genuine reversals; 1,096 edges | All 16 ordinary parameter chambers and 7 strict fifth-endpoint chambers; coefficientwise integer ordinal inequalities and full zero endpoints |
| Source reduction | Nine oriented symbolic LAST/FIRST identities | All full affine source coordinates retained |
| Rank-negative control | 106 literal pairs, 2 first-level and 13 second-level occurrences | At `k=t=0`, no old-target entry by depth 2; first entry at 3 and integral zero at 4 |
| Python tests | 23 passed | New theorem/refusal regressions plus the existing one-step predecessor oracle |
| Scoped Lean development compile and audit | 71 owned declarations, 53 theorem declarations; 5 exact endpoint types, 15 rejection controls | Four-step overrun family and two-step RUN slice; full thirteen-case theorem is not a Lean endpoint |
| Governance and inventory | Full governance audit, generated proof-bank check, vendored pins pass | 126 governed claims unchanged; no BH/A1′/C4/PSC promotion |

The full local theorem rests on the written parameter partition and symbolic
address/guard identities. Finite native and Python replays test the executable
implementation and its boundaries. Machine integers are checked: oversized
parameters or offsets refuse rather than returning a wrapped path. The
mathematical statement itself is over arbitrary integers.

The path with the maximum selected length is an upper-bound witness. No
optimal shortest-path claim is made. Integral offset zero permits different
terminal tile letters; this is not automatically typed coincidence.

## Lean acceptance boundary

`lean-development-pass.log` and `lean-audit-pass.log` are successful **local
development** receipts. The pinned Lean 4.34.0-rc2 compiler compiled the new
module using a read-only overlay of 14 transitive repository modules whose
source bytes matched the development base. The audit independently spells
out the literal words, packet sign, prefix ordinals and exact theorem types;
it scans all owned declarations and admits only `propext`, `Classical.choice`
and `Quot.sound`. Missing declarations, wrong types and an extra premise
are rejected for each of the five endpoints.

These local receipts do not stand in for a fresh source build. The dedicated
workflow runs `tools/check_class_a_zero_defect.sh`, copying project sources
into a new workspace, checking freshly obtained pinned dependency sources,
disabling caller Lake caches/configuration, and using only the fixed upstream
Mathlib artifact cache. The whole-library workflow separately rebuilds and
audits the full root import. **Exact-head hosted results are pending at this
evidence snapshot** and must be read from the PR's actual revision.

The failed development elaborations and the initial namespace-overlay audit
refusal are retained as `lean-development-initial-failure.log.gz`,
`lean-development-ordinal-failure.log.gz` and `lean-audit-initial-refusal.log.gz`.
They are historical development failures, not passing receipts for earlier
source. The later successful source and logs are distinct records.

## Replay

```bash
python -m pip install pytest==8.4.2 sympy==1.14.0
python -m pytest -o addopts='' -q tests/test_class_a_zero_defect_escape.py tests/test_class_a_zero_return_oracle.py
python oracles/python/class_a_zero_defect_symbolic.py
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_entry_defect.mojo
pixi run --locked mojo run -I . tests/test_class_a_zero_defect_escape.mojo --emit > /tmp/class-a-zero-defect-native.log
cd ..
python oracles/python/class_a_zero_defect_escape.py --native-log /tmp/class-a-zero-defect-native.log
./tools/check_class_a_zero_defect.sh
./tools/check_lean.sh
```

The local native runtime was Mojo `1.1.0.dev2026090805 (34562fa1)`, matching
the existing lock. A nonfatal Crashpad initialization warning is retained
in raw logs; the recorded successful commands exit zero. `local-checks.json`
records the exact local command vectors, working directories and exit codes.

`source-inputs.sha256` binds repository source/configuration inputs, including
transitive local native/formal dependencies and the generated proof bank.
`SHA256SUMS` binds the raw receipts. Verify from the repository root with:

```bash
sha256sum -c evidence/class-a-zero-defect-2026-11-14/source-inputs.sha256
sha256sum -c evidence/class-a-zero-defect-2026-11-14/SHA256SUMS
```

## Negative controls and nonclaims

The original two-defect rank proposal fails at an actual recurrent,
seed-reachable overlap whose two defects vanish but whose legal gap misses
the one-step target. Its source, cycle and productive exit remain explicit.
The new theorem supplies that rank's zero-defect base case; it does not prove
a selected decrease from arbitrary nonzero-defect cyclic descendants.

Additional controls reject the two non-strict fifth-endpoint walls, a false
slice premise, a nonexistent ordinal, a changed integral target, a wrong
symbolic ordinal, negative parameters, arithmetic overflow, a truncated native
log retaining all fourteen members, and duplicate native source records.

No finite graph census is used to establish the universal source-entry
quantifier. The result does not close #452 or BH #139. Residual A1′,
the nonunit realization dictionary, the alternative C4 route and the
all-alphabet extension remain separate obligations. The contribution is
independent of the open #574 bridge and the family PR stack.
