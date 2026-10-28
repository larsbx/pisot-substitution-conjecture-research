# Q3 verification packet — 2026-10-28

Scope: Q3=(x,y,1,-1,1) and actual reversal in the full minus class-A boundary
chamber k,t>=0. Complete nine-kind proof gives one X child per orientation;
every direct Q3 child has a selected four-edge typed-coincidence tail. Q3's
selected exit has five edges. A genuine Q3/X two-cycle remains. Universal
inequalities are in docs/class-a-boundary-q3-carrier-2026-10-28.md; finite
replay numbers validate implementations, not the infinite quantifier alone.

| Receipt | Result and exact scope |
| --- | --- |
| native.log | PASS: locked Mojo 1.1.0.dev2026090805; 56 members / 112 oriented sources / 33,096 pairs / 112 accepted; 560 selected path edges / 224 cycle-edge replays; full contract receipt reached |
| driver.log | PASS: symbolic Q[t,k] transport, inherited field/length bounds, cone lower-margin checks, actual ancestry, selected exit and real return; no global BH |
| python-scoped.log | PASS: all three Q3 regression tests, including negative controls |
| probe.json | Independent literal-word/integer-polynomial/Fraction oracle: 117 members / 234 sources / 122,616 pairs / 234 accepted; 1,170 selected path edges / 468 cycle-edge replays; both target labels attained; every actual direct child tail checked |
| tla.log | PASS: all 18 expected outcomes, including the intended nonproductive countermodel; no new Q3 TLA theorem is claimed |
| lean-attempt.log | FAIL before compilation: local launcher reports `failed to locate application`; exit 1, no Lean proof pass credited |
| provenance.log | PASS: full `bash tools/verify_all.sh provenance`, including vendoring, generated ledgers/catalogue/proof bank, manuscript and Markdown integrity, hit witnesses and governance |
| dependencies.json | Exact-head predecessor checks and integration snapshot; #365 passed all 68 recorded checks then merged at 148e5b35730ffa979b7f017bfa09f5882b5b1b5b; #372 retargeted to main with unchanged 8e97ad5035072951259b0301e7387f8baf25d148 head and evidence, still open with incomplete hosted gates |

Native replay used the existing installed environment at
/workspace/scratch/c319bc870de5/psc/kernel/pixi.toml with `--locked`,
explicitly passing `-I /workspace/scratch/dcf9c4be57c4/q3/kernel` and the
absolute new worktree driver/test path. Both manifest and lock are byte-identical
to this worktree's recorded source hashes. This reuses the pinned toolchain,
while compiling this packet's source. The portable commands are in the derivation.
The initial Python environment lacked pytest; pytest and the repository-pinned
pypdf==6.19.0 were installed before the recorded successful runs.

The complete local Python suite was also started; its outcome is recorded
separately if completed. It earns no pass while in progress. The complete local
native suite is not claimed. Fresh exact-head hosted native, Python, Lean,
TLA, provenance and evidence-policy gates remain required before integration.
Independent human review pending; unchanged inventory: 124 governed claims,
34 named Lean proofs, 325 source openings. No status or formal source promotion.

Checksums below are replayed from repository root:

```sh
sha256sum -c evidence/class-a-boundary-q3-2026-10-28/source-sha256.txt
sha256sum -c evidence/class-a-boundary-q3-2026-10-28/SHA256SUMS
python oracles/python/class_a_boundary_q3_children.py > /tmp/q3.json
cmp /tmp/q3.json evidence/class-a-boundary-q3-2026-10-28/probe.json
python -m pytest -q tests/test_class_a_boundary_q3_children.py
```
