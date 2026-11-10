# PR #500: integration with main and exact-revision acceptance

## Assumptions and hypotheses

Integrate verification head `654c24561dae1172acc973c43f3db67322a17fb8`
with main `ba09fdbd770248905a297303b8de45b3d7c5018d` (merged #499).
This integrates existing results; it introduces no new mathematical claim.
Main's finite standing-corpus C4 result and conditional C4 dependency on
`UniversalAlignedCoincidence` (#138) keep their mainline scopes. Neither is
supplied by Lean packet acceptance.

## Derivation / reduction

The actual three-way merge has exactly three conflicts:

| File | Resolution |
| --- | --- |
| `docs/side-notes-ledger.md` | Retain both appended histories, including main's C4/cut-attractor/H1 developments and all five Lean implementation entries. Append this integration entry. |
| `proof/proof-bank.json` | Regenerate with `python3 tools/make_proof_bank.py` from the merged record table, policy, source statements, proof-bank TOML and Lean modules. |
| `docs/proof-bank.md` | Regenerate with the same command; never select one stale inventory. |

The resulting inventory has 126 claims, 106 named Lean proofs and 375 source
openings. Main-only changed files, except these reconciled inventories, were
compared byte-for-byte to main. Every PR-only implementation file, apart from
the workflow change below and this documentation update, remains byte-for-byte
identical to `654c2456`. In particular the exporter, complete occurrence rows,
packet checker, independent expected-type binding, oracle, axiom auditors,
negative fixture, subprocess timeouts and incomplete-replay refusal are intact.

The packet workflow now also triggers on the entire Lean project and governed
inventory inputs (`proof-bank.toml/json`, the record generator, claim policy and
governance sources). This makes mainline inventory integration trigger the full
packet gate. Its existing exact-head checkout and 240-minute job budget remain;
an uploaded revision file additionally identifies the checkout on failed runs.
The dedicated branch push trigger and manual dispatch remain available.

## Evidence and replay

The prompt's pending observation is superseded for the **old exact head only**:
[run 42109144786](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42109144786)
succeeded at `654c24561dae1172acc973c43f3db67322a17fb8`. Its full artifact
[13457433206](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42109144786/artifacts/13457433206)
contains all generated Lean sources, compiled modules, independent importer
sources, complete audit/packet logs, class and oracle receipts, and the real
wrong-proof-type negative-control receipt. Artifact ZIP SHA-256:
`1a28b804be6cd045ed5daf5926eaf6608944d336fac3dfe3c1a40110f12097e2`.

This session downloaded and verified that ZIP digest, checked every one of the
18 source and log hashes against the complete receipt, checked each independent
importer against `audit_source(index)`, reparsed every generated axiom/completion
record, reconstructed the complete emitted packet from those logs, and checked
that its bytes and digest equal the artifact packet. All compiler/exporter/audit
stderr files were empty. The complete stored oracle receipt equals the committed
class receipt. The independent Python oracle was also rerun against the complete
19,466,338-byte packet using the integrated source checkout: exact receipt equality.
This is an independent runtime replay of data binding, not a new Lean kernel run.

The hosted generic audit reached 531 declarations, 275 theorem declarations and
all 106 named proofs; only `propext`, `Classical.choice`, `Quot.sound` were allowed.
Every generated source audited 2,564 declarations / 1,539 theorem declarations.
The class receipt covers **18 sources / 285,786 states / 1,409,729 occurrence
edges**, with `geometry_formalized: false`.

| Period-three source | States | Occurrence edges | Old-head kernel/type/axiom/parity acceptance |
| --- | ---: | ---: | --- |
| 12 | 15,891 | 78,288 | Passed |
| 13 | 15,881 | 78,299 | Passed |
| 15 | 15,895 | 78,326 | Passed |
| 16 | 15,872 | 78,334 | Passed |

Small complete receipts and the full generic audit are retained under
`evidence/c4-overlap-lean-integration-2026-11-06/`; full source/audit/packet payloads
remain in the linked hosted artifact (30-day retention). The older pilot notes
are historical and must not be read as this all-18 result.

Reproduce on a host with the pinned package sources available, starting from
one clean exact revision and a nonexistent output directory:

```sh
./tools/setup_lean.sh
export PATH="$HOME/.elan/bin:$PATH"
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_overlap_lean_export.mojo)
(cd kernel && pixi run --locked mojo build -I . c4_overlap_lean_export.mojo -o /tmp/c4-overlap-lean-export)
./tools/check_lean.sh --overlap-packets /tmp/c4-overlap-lean-export /tmp/c4-overlap-lean-packets
```

The integrated revision requires its **own** successful exact-head hosted gate.
The old receipt is not relabelled as acceptance of the integration. Other
workflows at the old head included failures; the packet success is focused
acceptance, not an assertion that every repository check passed.

## Negative controls

All existing controls remain: malformed layout/targets/payloads/weights/source
IDs, missing rows and repeated-occurrence counting; wrong theorem types with
plausible names and standard axioms; unexpected/admitted/native-reduction axiom
records; duplicate/stale/missing completion records. Subprocess failures and
resource timeouts still prevent a class receipt; no skipped source is accepted.
The retained real Lean control compiles the fixture but refuses its `True`
proofs at the independent expected-type check.

## Non-claims / remaining gaps

No PSC promotion, no change to main's governed statuses, and no PR merge.
The geometric cover recurrence, M-adic Haar measure/index-two scaling,
correctness of graph-state/geometric-overlap correspondence and pruning,
actual compact-prefix contraction, and strict-cut counting remain explicit
geometric/refinement hypotheses. Conditional deductions do not discharge them.

Local full native/Lean replay was unavailable: Pixi v0.81.0 failed after three
retries fetching locked conda-forge package
`python-dotenv-1.2.3-pyhcf101f3_0.conda` through the network proxy (`tunnel error:
unsuccessful`). No substitute native exporter or unlocked environment is credited.
The official Lean executable also needs this host's already archived numeric-PID
`readlink` adapter to find itself; the adapter successfully restores its version
probe and is an additional runtime trust input, not a change to proof code.
Normal hosted CI uses neither adaptation nor a package substitution.
